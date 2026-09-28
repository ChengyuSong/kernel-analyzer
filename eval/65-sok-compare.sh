#!/bin/bash
# SoK-MLTA (WOOT'26) comparison stage. eval/62-sok-arm.sh produces
# our per-program parsed_log JSON; this script (1) merges + rekeys
# it into the layout their harness expects, and (2) runs THEIR
# scripts/compare_approaches.py — their formulas, their ground
# truth — inside a network-less Docker sandbox, against their
# pre-computed baseline results (O0: LLVM-CFI + KallGraph; O3:
# LLVM-CFI + HPCFI).
#
# SANDBOX (user directive): third-party code runs in a container —
# --network none, non-root (-u uid:gid), read-only mounts for their
# repo and dataset; only the results dir is writable. Building the
# sok-compare image is the single step that needs the network.
#
# KEY ALIGNMENT: our --cfl-dump-icalls-json keys are
# "<path-as-compiled>:line" (e.g. "./coff-i386.c:164"); their
# pre-computed logs use whatever the tool's build emitted — the
# style VARIES per program ("nm.c:1294", "./print-lmp.c:481",
# "src/flv.c:489") and their intersection tables match keys
# EXACTLY. We therefore align each of our keys onto LLVM-CFI's
# exact string when the two agree up to a path boundary
# (suffix-of-suffix), keep the original otherwise, and UNION
# duplicate keys (sound: over-approximate per callsite, never
# dropping targets).
#
# Inputs:
#   KA_SOK_OUT   eval/62's output root (default $KA_RESULTS/sok);
#                dataset dir tags must contain O0/O3 (they do, from
#                their Drive layout).
#   KA_SOK_ROOT  their artifact root containing pre-computed/ and
#                fuzz_groundtruth/ (the Drive download).
#   KA_SOK_REPO  their code checkout (github SoK-MLTA).
# Output:
#   $KA_RESULTS/sok-merged/{O0,O3}/: ORCFL-{full,base}/parsed_log/,
#   their comparison_*.csv tables, common/ intermediates.
#
# SAME-MACHINE NOTE: this consumes their PRE-COMPUTED baseline
# parsed_log (recall/AICT are answer-set properties — machine-
# independent). Timing rows against MLTA/DeepType/TFA require
# building their tools from source (their patches/) and running
# run_experiment.py here — a separate, heavier step, not this
# script.

set -eu
source "$(dirname "${BASH_SOURCE[0]}")/env.sh"
ka_require docker python3

: "${KA_SOK_ROOT:?set KA_SOK_ROOT to the SoK artifact root (pre-computed/ + fuzz_groundtruth/)}"
: "${KA_SOK_REPO:?set KA_SOK_REPO to their code checkout}"
SOK_OUT="${KA_SOK_OUT:-$KA_RESULTS/sok}"
MERGED="${KA_SOK_MERGED:-$KA_RESULTS/sok-merged}"
IMG="${KA_SOK_IMAGE:-sok-compare}"

for d in "$KA_SOK_ROOT/pre-computed" "$KA_SOK_ROOT/fuzz_groundtruth" \
         "$KA_SOK_REPO/scripts/compare_approaches.py"; do
  [[ -e "$d" ]] || { echo "!! missing: $d" >&2; exit 1; }
done

# 1. Merge + rekey our parsed_log into ORCFL-{full,base} per opt
# level. Program names are canonicalized against the baseline + GT
# name universe: their ossfuzz programs are keyed
# "<project>__<prog>" (httpd__httpd, libjpeg-turbo__cjpeg-static)
# while eval/62 names by .bc basename — a unique "*__<prog>" suffix
# match adopts their name; ambiguity aborts.
for opt in O0 O3; do
  for cfg in full base; do
    dst="$MERGED/$opt/ORCFL-$cfg/parsed_log"
    mkdir -p "$dst" "$MERGED/$opt/common"
    python3 - "$SOK_OUT/$cfg" "$opt" "$dst" \
        "$KA_SOK_ROOT/pre-computed/soundness/$opt" \
        "$KA_SOK_ROOT/fuzz_groundtruth" <<'EOF'
import json, sys
from pathlib import Path
src, opt, dst, pre, gt = (Path(sys.argv[1]), sys.argv[2],
                          Path(sys.argv[3]), Path(sys.argv[4]),
                          Path(sys.argv[5]))
canon = {p.stem for p in gt.glob('*.json')}
for d in pre.glob('*/parsed_log'):
    canon |= {p.stem for p in d.glob('*.json')}
def canonical(prog):
    if prog in canon:
        return prog
    m = [c for c in canon if c.endswith('__' + prog)]
    if len(m) > 1:
        sys.exit(f'!! ambiguous canonical name for {prog}: {m}')
    return m[0] if m else prog
merged = {}   # prog -> key -> set(targets)
n = 0
for j in sorted(src.glob(f'*{opt}*/parsed_log/*.json')):
    d = json.load(open(j)); n += 1
    prog = merged.setdefault(canonical(j.stem), {})
    for k, v in d.items():
        prog.setdefault(k, set()).update(v)
if n == 0:
    sys.exit(f'!! no parsed_log JSON under {src}/*{opt}*/ — run eval/62 first')
def boundary_suffix(a, b):   # a agrees with b up to a path boundary
    return a == b or a.endswith('/' + b) or b.endswith('/' + a)
for prog, keys in merged.items():
    cfi_file = pre / 'LLVM-CFI' / 'parsed_log' / f'{prog}.json'
    aligned = {}
    if cfi_file.exists():
        cfi_keys = list(json.load(open(cfi_file)))
        for k, v in keys.items():
            m = [c for c in cfi_keys if boundary_suffix(k, c)]
            # longest agreement wins (e.g. "a/x.c:5" over "x.c:5")
            kk = max(m, key=len) if m else k
            aligned.setdefault(kk, set()).update(v)
    else:
        aligned = keys
    out = {k: sorted(v) for k, v in sorted(aligned.items())}
    json.dump(out, open(dst / f'{prog}.json', 'w'), indent=1)
print(f'== ORCFL-{dst.parent.parent.name.split("-")[-1]}/{opt}: '
      f'{len(merged)} programs from {n} source files')
EOF
  done
done

# 1b. Locally-run baselines, if present: merge each approach's
# per-dataset parsed_log (ossfuzz + unifuzz share an opt level) into
# one dir per approach. eval/66 output (their harness) is already in
# their names and keys. eval/67 output (our per-site dumpers) uses
# eval/62's convention, so it gets the SAME canonical program names and
# the SAME key alignment onto LLVM-CFI's strings as the ORCFL rows.
BASE_APPROACHES=""
if [[ -d "$SOK_OUT/baselines" ]]; then
  BASE_APPROACHES=$(python3 - "$SOK_OUT/baselines" "$MERGED" \
      "$KA_SOK_ROOT/pre-computed/soundness" \
      "$KA_SOK_ROOT/fuzz_groundtruth" <<'EOF'
import json, sys
from pathlib import Path
src, merged = Path(sys.argv[1]), Path(sys.argv[2])
pre_root, gt = Path(sys.argv[3]), Path(sys.argv[4])
THEIRS = ('TFA', 'DeepType', 'MLTA', 'MLTA_Orig')           # eval/66
OURS = ('SVF-Andersen', 'SVF-VFS', 'AserPTA-CI', 'AserPTA-1CFA',
        'AserPTA-2CFA', 'DyckAA', 'SeaDsa', 'AserPTA-CI-shape',
        'DyckAA-shape', 'GPG-FSCS', 'GPG-FICS', 'GPG-FICI',
        'LotusAA', 'TPA-K0', 'TPA-K1', 'FSPTA', 'VFSPTA', 'VFPTA',
        'SparrowAA', 'BootstrapAA', 'DDA-Flow', 'AserPTA-Origin',
        'CHA', 'RTA', 'VTA', 'OTF')                           # eval/67
def boundary_suffix(a, b):   # a agrees with b up to a path boundary
    return a == b or a.endswith('/' + b) or b.endswith('/' + a)
seen = set()
for opt in ('O0', 'O3'):
    pre = pre_root / opt
    canon = {p.stem for p in gt.glob('*.json')}
    for d in pre.glob('*/parsed_log'):
        canon |= {p.stem for p in d.glob('*.json')}
    def canonical(prog):
        if prog in canon:
            return prog
        m = [c for c in canon if c.endswith('__' + prog)]
        if len(m) > 1:
            sys.exit(f'!! ambiguous canonical name for {prog}: {m}')
        return m[0] if m else prog
    per = {}   # approach -> prog -> key -> set(targets)
    for tagdir in src.glob(f'*_{opt}'):
        for adir in tagdir.iterdir():
            # only the approaches eval/66 and eval/67 actually RUN here —
            # their harness also copies the pre-computed results into
            # its output dir, and those must keep coming from /sok
            if adir.name not in THEIRS + OURS:
                continue
            plog = adir / 'parsed_log'
            if not plog.is_dir():
                continue
            for j in plog.glob('*.json'):
                d = json.load(open(j))
                name = canonical(j.stem) if adir.name in OURS else j.stem
                prog = per.setdefault(adir.name, {}).setdefault(name, {})
                for k, v in d.items():
                    prog.setdefault(k, set()).update(v)
    for appr, progs in per.items():
        dst = merged / opt / appr / 'parsed_log'
        dst.mkdir(parents=True, exist_ok=True)
        for prog, keys in progs.items():
            cfi_file = pre / 'LLVM-CFI' / 'parsed_log' / f'{prog}.json'
            if appr in OURS and cfi_file.exists():
                cfi_keys = list(json.load(open(cfi_file)))
                aligned = {}
                for k, v in keys.items():
                    m = [c for c in cfi_keys if boundary_suffix(k, c)]
                    kk = max(m, key=len) if m else k
                    aligned.setdefault(kk, set()).update(v)
                keys = aligned
            out = {k: sorted(v) for k, v in sorted(keys.items())}
            json.dump(out, open(dst / f'{prog}.json', 'w'), indent=1)
        seen.add(appr)
print(' '.join(sorted(seen)))
EOF
) || exit 1
  [[ -n "$BASE_APPROACHES" ]] \
    && echo "== local baselines merged: $BASE_APPROACHES"
fi

# 2. Sandbox image (the only networked step; skipped once built).
if ! docker image inspect "$IMG" >/dev/null 2>&1; then
  echo "== building $IMG image"
  docker build -t "$IMG" - <<'EOF'
FROM python:3.12-slim
RUN pip install --no-cache-dir pandas seaborn matplotlib brokenaxes
EOF
fi

# 3. Their compare config, container-side paths.
for opt in O0 O3; do
  if [[ "$opt" == O0 ]]; then
    bl='"LLVM-CFI": "/sok/pre-computed/soundness/O0/LLVM-CFI/parsed_log/",
    "KallGraph": "/sok/pre-computed/soundness/O0/KG/parsed_log/",'
  else
    bl='"LLVM-CFI": "/sok/pre-computed/soundness/O3/LLVM-CFI/parsed_log/",
    "HPCFI": "/sok/pre-computed/soundness/O3/HPCFI/parsed_log/",'
  fi
  for appr in $BASE_APPROACHES; do
    [[ -d "$MERGED/$opt/$appr/parsed_log" ]] || continue
    bl+="
    \"$appr\": \"/results/$opt/$appr/parsed_log/\","
  done
  cat > "$MERGED/cmp-$opt.json" <<EOF
{
  "COMMON_PATH": "/results/$opt/",
  "RESULT_DIRS": {
    $bl
    "ORCFL": "/results/$opt/ORCFL-full/parsed_log/",
    "ORCFL-base": "/results/$opt/ORCFL-base/parsed_log/"
  },
  "GEN_HYBRID_RESULTS": false,
  "ENABLE_FUZZING_RESULTS": true,
  "RESULT_DIR_FUZZ": "/sok/fuzz_groundtruth/"
}
EOF
done

# 4. Run their comparison in the sandbox.
for opt in O0 O3; do
  echo "== compare_approaches $opt"
  docker run --rm --network none -u "$(id -u):$(id -g)" \
    -v "$KA_SOK_REPO/scripts":/scripts:ro \
    -v "$KA_SOK_ROOT":/sok:ro \
    -v "$MERGED":/results \
    -w /scripts "$IMG" \
    python compare_approaches.py --json "/results/cmp-$opt.json" \
    2>&1 | tee "$MERGED/$opt/compare.log"
done

# 5. Pairwise tables (KA_SOK_PAIRWISE=1): their script keeps a program
# only if EVERY configured approach has it, so one baseline that times
# out or is killed on a program drops that program for all. Pairwise
# runs compare each local baseline with ORCFL (full, base) and
# LLVM-CFI over the sites those share, same script, same formulas.
if [[ "${KA_SOK_PAIRWISE:-0}" == 1 ]]; then
  for opt in O0 O3; do
    for appr in $BASE_APPROACHES; do
      [[ -d "$MERGED/$opt/$appr/parsed_log" ]] || continue
      pdir="$MERGED/$opt/pair-$appr"
      mkdir -p "$pdir/common"
      cat > "$MERGED/cmp-$opt-pair-$appr.json" <<EOF
{
  "COMMON_PATH": "/results/$opt/pair-$appr/",
  "RESULT_DIRS": {
    "LLVM-CFI": "/sok/pre-computed/soundness/$opt/LLVM-CFI/parsed_log/",
    "$appr": "/results/$opt/$appr/parsed_log/",
    "ORCFL": "/results/$opt/ORCFL-full/parsed_log/",
    "ORCFL-base": "/results/$opt/ORCFL-base/parsed_log/"
  },
  "GEN_HYBRID_RESULTS": false,
  "ENABLE_FUZZING_RESULTS": true,
  "RESULT_DIR_FUZZ": "/sok/fuzz_groundtruth/"
}
EOF
      echo "== compare_approaches $opt pairwise $appr"
      docker run --rm --network none -u "$(id -u):$(id -g)" \
        -v "$KA_SOK_REPO/scripts":/scripts:ro \
        -v "$KA_SOK_ROOT":/sok:ro \
        -v "$MERGED":/results \
        -w /scripts "$IMG" \
        python compare_approaches.py \
          --json "/results/cmp-$opt-pair-$appr.json" \
        > "$pdir/compare.log" 2>&1
    done
  done
  echo "== pairwise tables: $MERGED/{O0,O3}/pair-*/comparison_*.csv"
fi

echo "== done. Tables: $MERGED/{O0,O3}/comparison_*.csv"
