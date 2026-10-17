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
//===----------------------------------------------------------------------===//

#ifndef KA_WATCHDOG_H
#define KA_WATCHDOG_H

#include <atomic>
#include <chrono>
#include <condition_variable>
#include <cstdint>
#include <cstdio>
#include <fcntl.h>
#include <mutex>
#include <thread>
#include <unistd.h>

class SolverWatchdog {
public:
  // Phase names are string literals (static storage): the thread reads the
  // pointer only.
  void phase(const char *P) {
    Phase.store(P, std::memory_order_relaxed);
    PhaseSince.store(nowNs(), std::memory_order_relaxed);
  }
  void pops(uint64_t N) { Pops.store(N, std::memory_order_relaxed); }

  void start(int Iteration, unsigned IntervalSecs) {
    if (T.joinable() || !IntervalSecs) return;
    Iter = Iteration;
    Interval = IntervalSecs;
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
  }
  ~SolverWatchdog() { stop(); }

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
  void run() {
    std::unique_lock<std::mutex> L(M);
    while (!CV.wait_for(L, std::chrono::seconds(Interval), [this] { return Stop; })) {
      const int64_t now = nowNs();
      char line[256];
      const int n = std::snprintf(line, sizeof(line),
                                  "CallGraph: Cells: watchdog (iteration %d) at %.0f s: phase %s for %.0f s, %llu pops, "
                                  "RSS %.2f GB\n",
                                  Iter, (now - Start) / 1e9, Phase.load(std::memory_order_relaxed),
                                  (now - PhaseSince.load(std::memory_order_relaxed)) / 1e9,
                                  (unsigned long long)Pops.load(std::memory_order_relaxed), rssGB());
      if (n > 0) {
        const ssize_t w = ::write(STDERR_FILENO, line, (size_t)n < sizeof(line) ? (size_t)n : sizeof(line) - 1);
        (void)w;
      }
    }
  }

  std::atomic<const char *> Phase{"start"};
  std::atomic<int64_t> PhaseSince{nowNs()};
  std::atomic<uint64_t> Pops{0};
  int Iter = 0;
  unsigned Interval = 60;
  int64_t Start = 0;
  bool Stop = false;
  std::mutex M;
  std::condition_variable CV;
  std::thread T;
};

#endif
