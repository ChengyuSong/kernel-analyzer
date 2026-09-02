#!/usr/bin/env python3
"""GT recall matcher for the linux-5.18 ground-truth campaign.

Reproduces the classification used for the 2026-08-13 GT pin
(98.50% strict / ~99.38% adjusted recall): each dynamic icall record
is bucketed as matched / FN / off / siteless / target_absent /
caller_absent, where only records whose target+callers are visible
to the analyzed corpus can be FNs.

Inputs:
  --gt       linux-5.18-groundtruth.json (icall_records: "site;frames, tgt+off")
  --pairs    analyzer answer pairs, one "caller target" per line
             (ICALL ∪ REGCALL union convention:
              zstdcat run.log.zst | awk '/^ICALL |^REGCALL /{print $2, $NF}' | sort -u)
  --funcs    optional: defined-function name list for the corpus (one per
             line; e.g. llvm-nm --defined-only over the bclist). Without
             it, target-absence falls back to "target never appears in
             any answer" — conservative: absent-from-corpus targets may
             count as FNs, so recall is a LOWER bound.

Output: bucket counts, strict recall = matched/(matched+FN), and the
FN list (frames + target) to stdout/--fn-out for triage.
"""
import argparse, collections, json, re, sys

ap = argparse.ArgumentParser()
ap.add_argument("--gt", required=True)
ap.add_argument("--pairs", required=True)
ap.add_argument("--funcs")
ap.add_argument("--fn-out")
ap.add_argument("--aux", help="DCALL/SCTCALL lines from --cfl-dump-gt-aux: "
                "direct (devirtualized) and static_call-trampoline edges. "
                "Used ONLY in the match test (monotone: can convert FN -> "
                "matched, never the reverse), so FN lists stay comparable "
                "with pre-aux pins")
ap.add_argument("--icall-json", help="per-callsite answers keyed by debug "
                "file:line (--cfl-dump-icalls-json). Debug locations survive "
                "inlining, so this closes the inline-attribution FN class: "
                "a GT record matches when its site location's answer set "
                "contains the target, regardless of which caller the "
                "inliner gave the copy. Monotone, like --aux")
args = ap.parse_args()

ours_pairs = set()
with open(args.pairs) as f:
    for line in f:
        parts = line.split()
        if len(parts) == 2:
            ours_pairs.add((parts[0], parts[1]))
ours_callers = {c for c, _ in ours_pairs}
ours_targets_any = {t for _, t in ours_pairs}
aux_pairs = set()
if args.aux:
    with open(args.aux) as f:
        for line in f:
            parts = line.split()
            if len(parts) == 3 and parts[0] in ("DCALL", "SCTCALL"):
                aux_pairs.add((parts[1], parts[2]))
ours_funcs = set()
if args.funcs:
    with open(args.funcs) as f:
        ours_funcs = set(f.read().split())

def normtgt(n):
    # strip numeric clone suffixes ("foo.123" -> "foo")
    h, _, s = n.rpartition(".")
    return h if h and s.isdigit() else n

loc_answers = {}
if args.icall_json:
    jd = json.load(open(args.icall_json))
    for loc, tgts in jd.items():
        loc_answers.setdefault(loc.lstrip("./"), set()).update(
            normtgt(x) for x in tgts)

d = json.load(open(args.gt))
recs = set()
for r in d["icall_records"]:
    site, _, tgt = r.rpartition(", ")
    m = re.match(r"^(.*)\+(-?\d+)$", tgt)
    if not m:
        continue
    name, off = m.group(1), int(m.group(2))
    frames = tuple(fr.split(":")[0] for fr in site.split(";")) if site else ()
    locs = tuple(fr.split(":", 1)[1] for fr in site.split(";")
                 if ":" in fr) if site else ()
    recs.add((frames, locs, name, off))

b = collections.Counter()
fns = []
for frames, locs, tgt, off in sorted(recs):
    if off != 0:
        b["off"] += 1
        continue
    if not frames:
        b["siteless"] += 1
        continue
    if tgt not in ours_funcs and tgt not in ours_targets_any:
        b["target_absent"] += 1
        continue
    present = [f for f in frames if f in ours_callers]
    if not present:
        b["caller_absent"] += 1
        continue
    if any((f, tgt) in ours_pairs for f in present):
        b["matched"] += 1
    elif any((f, tgt) in aux_pairs for f in frames):
        b["matched-aux"] += 1  # devirtualized / SCT-trampoline coverage
    elif loc_answers and any(
            normtgt(tgt) in loc_answers.get(l.lstrip("./"), ())
            for l in locs):
        b["matched-loc"] += 1  # inline-attribution coverage (debug loc)
    else:
        b["FN"] += 1
        fns.append((frames, tgt))

print(dict(b))
tot = b["matched"] + b["matched-aux"] + b["matched-loc"] + b["FN"]
if tot:
    m = b["matched"] + b["matched-aux"] + b["matched-loc"]
    print(f"strict recall: {m}/{tot} = {100.0*m/tot:.2f}%")
if not args.funcs:
    print("(no --funcs: target_absent under-classified; recall is a lower bound)")
out = open(args.fn_out, "w") if args.fn_out else sys.stdout
for frames, tgt in fns:
    print(";".join(frames), tgt, file=out)
