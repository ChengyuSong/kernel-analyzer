# Eval environment — source'd by every eval script. Override any of
# these by exporting before invocation, e.g.:
#   KA_WORK=/scratch/ka-eval KA_JOBS=64 eval/run-all.sh

# Where corpora are fetched/built and results land (needs ~15 GB).
export KA_WORK="${KA_WORK:-$HOME/ka-eval}"
export KA_RESULTS="${KA_RESULTS:-$KA_WORK/results}"

# Repo root = parent of this script's directory (scripts live in-repo).
export KA_REPO="${KA_REPO:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
export KA_BIN="${KA_BIN:-$KA_REPO/release/lib/KAMain}"

# Toolchain. LLVM >= 18 with lld and llvm-ar. On systems with
# unsuffixed binaries set KA_LLVM_SUFFIX= (empty).
export KA_LLVM_SUFFIX="${KA_LLVM_SUFFIX:--18}"
export KA_CC="${KA_CC:-clang$KA_LLVM_SUFFIX}"
export KA_LLVM_BUILD="${KA_LLVM_BUILD:-/usr/lib/llvm${KA_LLVM_SUFFIX/-//}}"
export KA_AR="llvm-ar$KA_LLVM_SUFFIX"
export KA_RANLIB="llvm-ranlib$KA_LLVM_SUFFIX"
export KA_NM="llvm-nm$KA_LLVM_SUFFIX"
export KA_LLD="lld$KA_LLVM_SUFFIX"

export KA_JOBS="${KA_JOBS:-$(nproc)}"

# Fair-comparison thread policy. KA_THREADS bounds worker/OpenMP
# threads for every tool we run (ours and baselines: GraCFL uses
# OpenMP/TBB and grabs ALL cores by default — always set this for
# any timed comparison row). KA_CPUSET pins the run to specific
# CPUs (taskset -c list, e.g. "0-7"); with disjoint cpusets and
# enough RAM, untimed arms can run in parallel.
export KA_THREADS="${KA_THREADS:-}"
export KA_CPUSET="${KA_CPUSET:-}"

# Spill root for fs-mode (batched) runs ONLY; FI runs never spill.
# Rules (stale-spill incident, 2026-08): every run gets a FRESH
# subdirectory under this root (scripts mkdir -p a per-arm dir and
# refuse to reuse a nonempty one); must be real disk, NOT tmpfs
# (/tmp is tmpfs on our machines; spill ~ total fact mass); cleaned
# on success. Empty default = recompute mode (no spill).
export KA_SPILL_ROOT="${KA_SPILL_ROOT:-}"

# Corpus versions (pinned; bump deliberately and re-pin answer hashes).
export HTTPD_VER="${HTTPD_VER:-2.4.68}"
export APR_VER="${APR_VER:-1.7.6}"
export APRUTIL_VER="${APRUTIL_VER:-1.6.4}"
export PG_VER="${PG_VER:-18.4}"

# Run controls.
#   KA_MEM_LIMIT_GB: 0 = analyzer default (80% of RAM watchdog).
#     On big machines raise it for the saturation runs — whether
#     saturation COMPLETES given enough memory is itself a data point.
#   KA_SAT_TIMEOUT: wall-clock cap per saturation run (seconds).
export KA_MEM_LIMIT_GB="${KA_MEM_LIMIT_GB:-0}"
export KA_SAT_TIMEOUT="${KA_SAT_TIMEOUT:-14400}"
export KA_FT_TIMEOUT="${KA_FT_TIMEOUT:-14400}"
# Extra flags appended to every flows-to run (e.g. --func-summaries=...).
export KA_EXTRA_FLAGS="${KA_EXTRA_FLAGS:-}"
# Field-sensitive mode (KA_MODES+=" ftfs"): canonical fs config as of
# 2026-08-17 — P=41 residues + presolve-once (byte-identical to the
# eager pin at P=41; the pre-solve re-run it skips was 56% of fs41
# wall). For kernel-scale corpora add the batch/bidi tier via
# KA_EXTRA_FLAGS: --cfl-bidi-prune --cfl-batch-roots=4000
# --cfl-batch-workers=<cores/4> --cfl-batch-spill=<big-disk-dir>
# (spill dir NOT tmpfs; bidi answers are strictly tighter under fs —
# flag-match pins).
export KA_FS_FLAGS="${KA_FS_FLAGS:---cfl-field-buckets=41 --cfl-presolve-once}"
# Optional: analyze a pre-existing bitcode list too (e.g. a kernel):
#   KA_USER_BCLIST=/path/bclist KA_USER_NAME=linux-6.8
export KA_USER_BCLIST="${KA_USER_BCLIST:-}"
export KA_USER_NAME="${KA_USER_NAME:-user-corpus}"

export MALLOC_ARENA_MAX=2
export LC_ALL=C

# KA_MEM_LIMIT_MODE: empty = analyzer default (RLIMIT_AS); "rss" for
# RSS-watchdog mode (big-machine kernel runs used rss).
export KA_MEM_LIMIT_MODE="${KA_MEM_LIMIT_MODE:-}"
# KA_MODES: which of ft/sat 30-run.sh executes per corpus. A/B config
# runs (e.g. kernel FI vs selective-fs) want "ft" for the second
# invocation so the saturation bar isn't paid twice.
export KA_MODES="${KA_MODES:-ft sat}"

ka_memflag() {
  if [ "$KA_MEM_LIMIT_GB" != "0" ]; then echo "--mem-limit=$KA_MEM_LIMIT_GB"; fi
  if [ -n "$KA_MEM_LIMIT_MODE" ]; then echo "--mem-limit-mode=$KA_MEM_LIMIT_MODE"; fi
}

ka_require() {
  for t in "$@"; do
    command -v "$t" >/dev/null || { echo "MISSING TOOL: $t" >&2; exit 1; }
  done
}
