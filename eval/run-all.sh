#!/bin/bash
# End-to-end eval on a fresh machine:
#   git clone <repo> && cd <repo> && eval/run-all.sh
# Configuration via env — see eval/env.sh (KA_WORK, KA_JOBS,
# KA_LLVM_SUFFIX, KA_MEM_LIMIT_GB, KA_SAT_TIMEOUT, KA_USER_BCLIST...).
set -euo pipefail
d="$(dirname "$0")"
bash "$d/00-build-kanalyzer.sh"
bash "$d/10-fetch-corpora.sh"
bash "$d/20-build-corpora.sh"
bash "$d/30-run.sh" "$@"
if [ "${KA_ABLATE:-0}" = 1 ]; then bash "$d/35-ablate.sh" "$@"; fi
bash "$d/40-extract.sh"
