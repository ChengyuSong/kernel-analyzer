#!/bin/bash
# Compare two ICALL answer pins: A = baseline (e.g. kernel FI),
# B = variant (e.g. selective fs / all+ids). Produces the decision
# deliverables for "is field sensitivity worth it":
#   - pair deltas in BOTH directions (removed-by-B vs added-by-B —
#     for fs, added = sound recall via container_of composition);
#   - per-site fanout distribution for each side;
#   - where the removals concentrate: top sites by |delta| with
#     caller names, so channel overlap is visible at a glance.
# Accepts .gz pins transparently. LC_ALL=C is set in env.sh.
#
# REQUIREMENT: both pins must come from the SAME IR build (same
# bclist files). Dump lines embed SSA value numbers and metadata
# slot ids, which renumber across builds — pins from different
# builds share zero lines and the comparison is meaningless. The
# script aborts if the intersection is empty.
#
# Usage: 50-compare.sh <A.sort[.gz]> <B.sort[.gz]> [outdir]
set -euo pipefail
source "$(dirname "$0")/env.sh"
[ $# -ge 2 ] || { echo "usage: $0 <A.sort[.gz]> <B.sort[.gz]> [outdir]" >&2; exit 1; }
A=$1; B=$2; out=${3:-$KA_RESULTS/compare}
mkdir -p "$out"

cat_pin() { case $1 in *.gz) zcat "$1" ;; *) cat "$1" ;; esac; }

wa=$(mktemp); wb=$(mktemp); trap 'rm -f "$wa" "$wb"' EXIT
cat_pin "$A" > "$wa"; cat_pin "$B" > "$wb"

nA=$(wc -l < "$wa"); nB=$(wc -l < "$wb")
comm -23 "$wa" "$wb" > "$out/removed-by-B.txt"   # in A only
comm -13 "$wa" "$wb" > "$out/added-by-B.txt"     # in B only
nRem=$(wc -l < "$out/removed-by-B.txt")
nAdd=$(wc -l < "$out/added-by-B.txt")
nCommon=$((nA - nRem))
if [ "$nCommon" = 0 ] && [ "$nA" -gt 0 ] && [ "$nB" -gt 0 ]; then
  echo "ERROR: pins share ZERO pairs — they are from different IR builds" >&2
  echo "(SSA/metadata numbering differs across builds; re-run both configs" >&2
  echo "on the same bclist on the same machine)" >&2
  exit 1
fi

# Per-site fanout: site key = line minus the " -> callee" suffix.
site_counts() { sed 's/ -> [^ ]*$//' "$1" | sort | uniq -c | sort -rn; }
site_counts "$wa" > "$out/sites-A.txt"
site_counts "$wb" > "$out/sites-B.txt"

dist() { # dist <sites file> -> "sites avg p50 p90 max"
  awk '{print $1}' "$1" | sort -n | awk '
    {v[NR]=$1; s+=$1}
    END {if (NR==0) {print "0 0 0 0 0"; exit}
         printf "%d %.1f %d %d %d\n", NR, s/NR,
                v[int(NR*0.5)+ (NR%2==0?0:0)], v[int(NR*0.9)], v[NR]}'
}

# Top sites by |delta| (join the two per-site tables on the site key).
awk '{c=$1; $1=""; sub(/^ /,""); print c "\t" $0}' "$out/sites-A.txt" | sort -t$'\t' -k2 > "$out/.sa"
awk '{c=$1; $1=""; sub(/^ /,""); print c "\t" $0}' "$out/sites-B.txt" | sort -t$'\t' -k2 > "$out/.sb"
join -t$'\t' -a1 -a2 -1 2 -2 2 -o 0,1.1,2.1 -e 0 "$out/.sa" "$out/.sb" \
  | awk -F'\t' '{d=$3-$2; ad=(d<0?-d:d); print ad "\t" $2 "\t" $3 "\t" d "\t" $1}' \
  | sort -rn | awk 'NR<=40' \
  | awk -F'\t' 'BEGIN{printf "%-8s %-8s %-8s  %s\n","A","B","delta","site"}
                {printf "%-8s %-8s %-8s  %.130s\n",$2,$3,$4,$5}' > "$out/top-delta-sites.txt"
rm -f "$out/.sa" "$out/.sb"

read -r sA aA mA p9A xA < <(dist "$out/sites-A.txt")
read -r sB aB mB p9B xB < <(dist "$out/sites-B.txt")

{
  echo "A: $A ($nA pairs, $sA sites; fanout avg $aA / p50 $mA / p90 $p9A / max $xA)"
  echo "B: $B ($nB pairs, $sB sites; fanout avg $aB / p50 $mB / p90 $p9B / max $xB)"
  echo "common: $nCommon"
  echo "removed by B (in A only): $nRem"
  echo "added by B   (in B only): $nAdd"
  echo "net: $((nB - nA))"
  echo
  echo "Top sites by |delta| -> $out/top-delta-sites.txt"
  echo "Full diffs -> $out/removed-by-B.txt, $out/added-by-B.txt"
} | tee "$out/summary.txt"
echo; head -12 "$out/top-delta-sites.txt"
