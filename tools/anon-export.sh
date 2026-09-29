#!/bin/bash
# Build the anonymized replication package for double-blind review.
#
# Copies ONLY the files the paper's results depend on (explicit list
# below; no git history, no internal notes), replaces identifying terms,
# writes a fresh README, then refuses to finish if any identifying term
# survives in any file (text or binary). This script itself is NOT part
# of the package: it names the terms it removes.
#
# Not included: the kernel fuzzing ground truth (third-party data, not
# ours to redistribute); the package ships the matcher, and eval/60 runs
# without it when KA_GT is unset.
#
# usage: tools/anon-export.sh OUTDIR     -> OUTDIR/ + OUTDIR.tar.gz
set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT="${1:?usage: tools/anon-export.sh OUTDIR}"
[[ -e "$OUT" ]] && { echo "!! $OUT exists; remove it first" >&2; exit 1; }
mkdir -p "$(dirname "$OUT")"; OUT="$(cd "$(dirname "$OUT")" && pwd)/$(basename "$OUT")"

# ---- what the results depend on -------------------------------------------
TRACKED=(
  LICENSE Makefile Makefile.inc func_summaries.txt
  src proof docker
  eval/00-build-kanalyzer.sh eval/10-fetch-corpora.sh eval/20-build-corpora.sh
  eval/59-kernel-corpus.sh eval/60-kernel-fse.sh eval/61-kernel-fs-endpoints.sh
  eval/62-sok-arm.sh eval/63-gracfl-graspan.sh eval/64-usermode-fse.sh
  eval/65-sok-compare.sh eval/66-sok-baselines.sh eval/67-dataflow-baselines.sh
  eval/68-sok-httpd-apr.sh eval/69-sok-bigbox.sh
  eval/env.sh eval/lib-fetch.sh eval/sok-downgrade.sh
  eval/kernel-toolchain.Dockerfile eval/sok-toolchain.Dockerfile
  eval/sok-baselines.Dockerfile eval/svf-baseline.Dockerfile eval/svf-baseline
  eval/lotus-baseline.Dockerfile eval/lotus-baseline eval/gracfl
  tools/gt-match.py tools/sok-persite.py tools/sok-report.py
  tools/derive-libc-summaries.sh
  test/cfl-smoke.sh
)
# untracked inputs the package needs ("repo path:package path")
DATA=(
  "test/libpng/libpng_read_fuzzer.0.0.preopt.bc:test/libpng/libpng_read_fuzzer.0.0.preopt.bc"
)

# ---- identifying terms: replacements, then a hard check -------------------
SED=(
  -e 's/Chengyu Song/Anonymous Author/g'
  -e 's/ChengyuSong/anonymous/g'
  -e 's/csong@cs\.ucr\.edu/anonymous@example.org/g'
  -e 's/csong84@gatech\.edu/anonymous@example.org/g'
  -e 's/chengyu\.song@gmail\.com/anonymous@example.org/g'
  -e 's#/home/csong#/home/user#g'
  -e 's#/data/csong#/data#g'
)
# text: case-insensitive; binaries: exact identity strings only (random
# bytes in bitcode can spell short words like "ucR")
LEAK_TEXT='chengyu|csong|ucr\.edu|gatech|haochen|zeng10|claude-1000|\bUCR\b|riverside'
LEAK_BIN='Chengyu|chengyu|csong|ucr\.edu|gatech|Haochen|zeng10|claude-1000'

cd "$REPO"
for p in "${TRACKED[@]}"; do
  [[ -n "$(git ls-files -- "$p")" ]] || { echo "!! nothing tracked at $p" >&2; exit 1; }
done
git ls-files -z -- "${TRACKED[@]}" | while IFS= read -r -d '' f; do
  mkdir -p "$OUT/$(dirname "$f")"; cp -p "$f" "$OUT/$f"
done
for m in "${DATA[@]}"; do
  src=${m%%:*}; dst=${m#*:}
  [[ -f "$src" ]] || { echo "!! missing input $src" >&2; exit 1; }
  mkdir -p "$OUT/$(dirname "$dst")"; cp -p "$src" "$OUT/$dst"
done

# scrub text files (binaries are only checked, never edited)
while IFS= read -r -d '' f; do
  if grep -Iq . "$f"; then sed -i "${SED[@]}" "$f"; fi
done < <(find "$OUT" -type f -print0)

cat > "$OUT/README.md" <<'EOF'
# Replication package (anonymized for review)

A whole-program flows-to analysis for indirect-call resolution over
LLVM IR, its Lean model, and the scripts that reproduce the paper's
numbers. Everything external is fetched from pinned sources and
verified (git commits by SHA, files by sha256): the Linux 5.18 source
(kernel.org), the SoK-MLTA dataset and scripts, SVF, Lotus, GraCFL and
the Graspan graphs, and the APR libraries. Nothing is prebuilt.

## Layout
- `src/` the analysis (C++17, LLVM 18); `src/gracfl/` bundled CFL engine
- `func_summaries.txt` library transfer summaries
- `proof/lean/` Lean model and proofs (`lake build`); `GAPS.md` lists
  the open obligations
- `eval/` experiment scripts, numbered by stage; each documents its
  inputs, outputs and environment variables in its header
- `tools/` scoring (`sok-persite.py`, `sok-report.py`) and the kernel
  ground-truth matcher (`gt-match.py`)
- `test/cfl-smoke.sh` smoke test

## Build
    make BUILD_DIR=release LLVM_BUILD=/usr/lib/llvm-18
    test/cfl-smoke.sh            # expect four PASS lines

## Reproduce
Kernel (Linux 5.18, x86-64 defconfig + Clang ThinLTO):

    eval/59-kernel-corpus.sh           # kernel.org source -> bitcode corpus
    KA_KERNEL_BCLIST=$KA_WORK/linux-5.18.bclist eval/60-kernel-fse.sh
    KA_KERNEL_BCLIST=$KA_WORK/linux-5.18.bclist eval/61-kernel-fs-endpoints.sh

The kernel recall numbers use fuzzing call traces from a third party,
which we cannot redistribute. `eval/60-kernel-fse.sh` runs without
them; with a trace file in the same format, set `KA_GT=<file>`.

User-space programs (httpd, PostgreSQL):

    eval/10-fetch-corpora.sh && eval/20-build-corpora.sh && eval/64-usermode-fse.sh

SoK-MLTA comparison with all baselines (needs docker):

    export KA_BIGBOX_WORK=/big/disk/sok
    eval/69-sok-bigbox.sh setup        # dataset, SoK scripts, SVF, Lotus, APR
    eval/69-sok-bigbox.sh all          # -> $KA_BIGBOX_WORK/report.md

CFL engines on the Graspan graphs:

    eval/63-gracfl-graspan.sh

`eval/env.sh` holds the shared defaults (`KA_WORK` and toolchain).
EOF

# hard check: no identifying term anywhere, text or binary
leaks=$( { grep -rIilE "$LEAK_TEXT" "$OUT"
          find "$OUT" -type f ! -exec grep -Iq . {} \; -print0 \
            | xargs -0 -r grep -laE "$LEAK_BIN"
          find "$OUT" -name '*groundtruth*.json'; } | sort -u || true)
if [[ -n "$leaks" ]]; then
  echo "!! identifying terms or third-party data remain in:" >&2; echo "$leaks" >&2
  grep -rnIioE "$LEAK_TEXT" "$OUT" | head -20 >&2
  exit 1
fi
tar -C "$(dirname "$OUT")" -czf "$OUT.tar.gz" "$(basename "$OUT")"
echo "== package: $OUT ($(du -sh "$OUT" | cut -f1)), $OUT.tar.gz, $(find "$OUT" -type f | wc -l) files; leak check clean"
