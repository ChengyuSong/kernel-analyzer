//===- Watchdog.h - the cell solver's timer progress line -------*- C++ -*-===//
//
// A thread that prints, every interval, the solver's current phase, how long
// it has been in it, the pops so far and the process's RSS, whatever the
// solver is doing (Fable 2026-10-17: a stall is always attributable, a
// timeout or an OOM labeled from the log alone). The thread reads atomics
// only, never a solver or LLVM structure; each tick is one preformatted line
// written in one write(2) call (KA_LOG composes its lines the same way, so a
// tick lands between lines); RSS comes from /proc/self/statm. It starts with
// the solver and is stopped and joined before the solver's summary prints
// (and by its destructor on any other way out).
//
// Long pops (LP, Fable 2026-10-25, --cfl-cell-long-pop): the solver stores
// the pop's sequence number, node, delta size and successor count on every
// pop, and names the operation it is in (a sub-phase: refold drain, fact
// merge, copy region, field steps, propagation by edge kind, ...) with its
// subject, plus a progress counter (units: facts offered, steps replayed,
// members moved). When one pop runs past the threshold the thread prints a
// line each interval naming them; when that pop ends it leaves the sampled
// sub-phase times for the solver thread, which prints the closing line
// (node and object descriptions are solver data, read there only).
//
//===----------------------------------------------------------------------===//

#ifndef KA_WATCHDOG_H
#define KA_WATCHDOG_H

#include <atomic>
#include <chrono>
#include <condition_variable>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <fcntl.h>
#include <mutex>
#include <string>
#include <thread>
#include <unistd.h>

class SolverWatchdog {
public:
  // Phase names are string literals (static storage): the thread reads the
  // pointer only. A phase change ends the current pop's watch (the phases
  // name what runs between pops); the next pop re-arms it.
  void phase(const char *P) {
    Phase.store(P, std::memory_order_relaxed);
    PhaseSince.store(nowNs(), std::memory_order_relaxed);
    Armed.store(false, std::memory_order_relaxed);
  }
  void pops(uint64_t N) { Pops.store(N, std::memory_order_relaxed); }
  // Every pop: its number (the pops so far), node, delta and successors.
  void pop(uint64_t Seq, uint32_t Node, uint32_t Delta, uint32_t Succ) {
    Pops.store(Seq, std::memory_order_relaxed);
    PopNode.store(Node, std::memory_order_relaxed);
    PopDelta.store(Delta, std::memory_order_relaxed);
    PopSucc.store(Succ, std::memory_order_relaxed);
    Sub.store(nullptr, std::memory_order_relaxed);
    SubObj.store(UINT32_MAX, std::memory_order_relaxed);
    SubNode.store(UINT32_MAX, std::memory_order_relaxed);
    Armed.store(true, std::memory_order_relaxed);
  }
  // The operation under way and what it works on (set once at its entry).
  const char *sub(const char *S) { return Sub.exchange(S, std::memory_order_relaxed); }
  void unsub(const char *Prev) { Sub.store(Prev, std::memory_order_relaxed); }
  void subject(uint32_t Obj, uint32_t Node, uint64_t Size) {
    SubObj.store(Obj, std::memory_order_relaxed);
    SubNode.store(Node, std::memory_order_relaxed);
    SubSize.store(Size, std::memory_order_relaxed);
  }
  // Progress: a local count, published every 4096 units.
  void unit() {
    if ((++LocalUnits & 0xfff) == 0) Units.store(LocalUnits, std::memory_order_relaxed);
  }
  // The heaviest objects' holder counts at the last mass report.
  static constexpr int NHeavy = 12;
  void heavy(int I, uint32_t Obj, uint64_t Holders) {
    if (I < 0 || I >= NHeavy) return;
    HeavyObj[I].store(Obj, std::memory_order_relaxed);
    HeavyHolders[I].store(Holders, std::memory_order_relaxed);
  }
  // A long pop ended: the solver thread takes what the watch recorded, once.
  struct Ended {
    uint64_t Seq = 0;
    uint32_t Node = UINT32_MAX, Obj = UINT32_MAX;
    double Secs = 0, Rss0 = 0, Rss1 = 0;
    std::string Subs;
  };
  bool longPopEnded() const { return LongEnded.load(std::memory_order_relaxed); }
  Ended takeLongPop() {
    std::lock_guard<std::mutex> G(M);
    LongEnded.store(false, std::memory_order_relaxed);
    return std::move(Last);
  }

  void start(int Iteration, unsigned IntervalSecs, unsigned LongPopSecs = 0) {
    if (T.joinable() || !IntervalSecs) return;
    Iter = Iteration;
    Interval = IntervalSecs;
    LongPop = LongPopSecs;
    Start = nowNs();
    Stop = false;
    T = std::thread([this] { run(); });
  }
  void stop() {
    if (!T.joinable()) return;
    {
      std::lock_guard<std::mutex> G(M);
      Stop = true;
    }
    CV.notify_all();
    T.join();
    // A long pop the last tick saw under way: ended by the stop (the thread
    // is joined; the solver takes it after).
    if (InLong) endLong(nowNs(), rssGB());
  }
  ~SolverWatchdog() { stop(); }

  // Names the operation for its scope and restores the enclosing one.
  class Scope {
  public:
    Scope(SolverWatchdog &W, const char *S) : W(W), Prev(W.sub(S)) {}
    ~Scope() { W.unsub(Prev); }

  private:
    SolverWatchdog &W;
    const char *Prev;
  };

private:
  static int64_t nowNs() {
    return std::chrono::duration_cast<std::chrono::nanoseconds>(
               std::chrono::steady_clock::now().time_since_epoch())
        .count();
  }
  static double rssGB() {
    char buf[128];
    const int fd = ::open("/proc/self/statm", O_RDONLY);
    if (fd < 0) return -1;
    const ssize_t n = ::read(fd, buf, sizeof(buf) - 1);
    ::close(fd);
    if (n <= 0) return -1;
    buf[n] = 0;
    unsigned long long size = 0, rss = 0;
    if (std::sscanf(buf, "%llu %llu", &size, &rss) != 2) return -1;
    return (double)rss * (double)::sysconf(_SC_PAGESIZE) / (1024.0 * 1024 * 1024);
  }
  static void emit(const char *line, int n, size_t cap) {
    if (n <= 0) return;
    const ssize_t w = ::write(STDERR_FILENO, line, (size_t)n < cap ? (size_t)n : cap - 1);
    (void)w;
  }
  // The long pop ended: what the watch recorded, for the solver thread.
  void endLong(int64_t now, double rss) {
    std::string subs;
    for (int i = 0; i < NSubs && SubName[i]; i++) {
      char b[96];
      std::snprintf(b, sizeof(b), "%s%s: %.0f s", subs.empty() ? "" : ", ", SubName[i], SubSecs[i]);
      subs += b;
    }
    Last.Seq = WatchSeq;
    Last.Node = LongNode;
    Last.Obj = LongObj;
    Last.Secs = (now - WatchSince) / 1e9;
    Last.Rss0 = LongRss0;
    Last.Rss1 = rss;
    Last.Subs = subs.empty() ? "none sampled" : subs;
    LongEnded.store(true, std::memory_order_relaxed);
    InLong = false;
  }
  // One tick of the long-pop watch (the thread holds M).
  void watchPop(int64_t now, double rss) {
    const uint64_t units = Units.load(std::memory_order_relaxed);
    const uint64_t dUnits = units - PrevUnits;
    const double dRss = rss - PrevRss;
    PrevUnits = units;
    PrevRss = rss;
    const uint64_t seq = Pops.load(std::memory_order_relaxed);
    const bool armed = Armed.load(std::memory_order_relaxed);
    if (seq != WatchSeq || !armed) {
      if (InLong) endLong(now, rss); // the next pop, or a phase
      WatchSeq = seq;
      WatchSince = now;
      WatchRss = rss;
      return;
    }
    const double secs = (now - WatchSince) / 1e9;
    if (secs < LongPop) return;
    const char *sub = Sub.load(std::memory_order_relaxed);
    if (!sub) sub = "pop body";
    if (!InLong) {
      InLong = true;
      LongNode = PopNode.load(std::memory_order_relaxed);
      LongRss0 = WatchRss;
      for (int i = 0; i < NSubs; i++) SubName[i] = nullptr, SubSecs[i] = 0;
    }
    // Sampled: the interval goes to the sub-phase seen at its end.
    for (int i = 0; i < NSubs; i++)
      if (!SubName[i] || SubName[i] == sub) {
        SubName[i] = sub;
        SubSecs[i] += Interval;
        break;
      }
    const uint32_t obj = SubObj.load(std::memory_order_relaxed);
    LongObj = obj;
    char subj[160];
    if (obj != UINT32_MAX) {
      uint64_t h = UINT64_MAX;
      for (int i = 0; i < NHeavy; i++)
        if (HeavyObj[i].load(std::memory_order_relaxed) == obj) h = HeavyHolders[i].load(std::memory_order_relaxed);
      char hs[64] = "";
      if (h != UINT64_MAX) std::snprintf(hs, sizeof(hs), ", %llu holder nodes at the last mass report", (unsigned long long)h);
      std::snprintf(subj, sizeof(subj), "obj #%u (size %llu%s)", obj,
                    (unsigned long long)SubSize.load(std::memory_order_relaxed), hs);
    } else {
      const uint32_t sn = SubNode.load(std::memory_order_relaxed);
      if (sn != UINT32_MAX)
        std::snprintf(subj, sizeof(subj), "node %u (size %llu)", sn, (unsigned long long)SubSize.load(std::memory_order_relaxed));
      else
        std::snprintf(subj, sizeof(subj), "none");
    }
    char line[512];
    const int n = std::snprintf(
        line, sizeof(line),
        "CallGraph: Cells: long pop (iteration %d) for at least %.0f s: pop #%llu node %u (class n/a, delta %u facts, "
        "succ %u), in %s [subject: %s], units %llu (+%llu in the last interval), RSS %.2f GB (%+.2f)\n",
        Iter, secs, (unsigned long long)seq, LongNode, PopDelta.load(std::memory_order_relaxed),
        PopSucc.load(std::memory_order_relaxed), sub, subj, (unsigned long long)units,
        (unsigned long long)dUnits, rss, dRss);
    emit(line, n, sizeof(line));
  }
  void run() {
    std::unique_lock<std::mutex> L(M);
    while (!CV.wait_for(L, std::chrono::seconds(Interval), [this] { return Stop; })) {
      const int64_t now = nowNs();
      const double rss = rssGB();
      char line[256];
      const int n = std::snprintf(line, sizeof(line),
                                  "CallGraph: Cells: watchdog (iteration %d) at %.0f s: phase %s for %.0f s, %llu pops, "
                                  "RSS %.2f GB\n",
                                  Iter, (now - Start) / 1e9, Phase.load(std::memory_order_relaxed),
                                  (now - PhaseSince.load(std::memory_order_relaxed)) / 1e9,
                                  (unsigned long long)Pops.load(std::memory_order_relaxed), rss);
      emit(line, n, sizeof(line));
      if (LongPop) watchPop(now, rss);
    }
  }

  std::atomic<const char *> Phase{"start"};
  std::atomic<int64_t> PhaseSince{nowNs()};
  std::atomic<uint64_t> Pops{0};
  // Long pops: written by the solver thread.
  std::atomic<bool> Armed{false};
  std::atomic<uint32_t> PopNode{UINT32_MAX}, PopDelta{0}, PopSucc{0};
  std::atomic<const char *> Sub{nullptr};
  std::atomic<uint32_t> SubObj{UINT32_MAX}, SubNode{UINT32_MAX};
  std::atomic<uint64_t> SubSize{0}, Units{0};
  uint64_t LocalUnits = 0; // solver thread only
  std::atomic<uint32_t> HeavyObj[NHeavy] = {};
  std::atomic<uint64_t> HeavyHolders[NHeavy] = {};
  std::atomic<bool> LongEnded{false};
  // Long pops: the thread's own state (under M).
  static constexpr int NSubs = 16;
  uint64_t WatchSeq = 0, PrevUnits = 0;
  int64_t WatchSince = 0;
  double WatchRss = 0, LongRss0 = 0, PrevRss = 0;
  bool InLong = false;
  uint32_t LongNode = UINT32_MAX, LongObj = UINT32_MAX;
  const char *SubName[NSubs] = {};
  double SubSecs[NSubs] = {};
  Ended Last;
  int Iter = 0;
  unsigned Interval = 60, LongPop = 0;
  int64_t Start = 0;
  bool Stop = false;
  std::mutex M;
  std::condition_variable CV;
  std::thread T;
};

#endif
