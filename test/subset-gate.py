#!/usr/bin/env python3
"""Removal-only gate between two test/consumer-gate.sh output trees.

  test/subset-gate.py OFF ON [GTDIR]

Per run present in both trees: every (site, target) pair ON answers must
also be answered by OFF (a pair only ON has is a violation), and the
number of pairs ON removed. With GTDIR (the SoK fuzz_groundtruth/
directory), every removed pair is checked against the fuzz-observed
targets of its site: a removed observed pair is a recall loss. Sites
match when one key is a path suffix of the other ("nm.c:1294" vs
"/home/x/binutils/nm.c:1294"). Exit 1 on any violation or recall loss.
"""
import json
import os
import sys


def load(path):
    with open(path) as f:
        d = json.load(f)
    return {k: set(v) for k, v in d.items()}


def gt_for(run, gtdir):
    prog = run.rsplit("-", 1)[0]  # nm-new-O0 -> nm-new
    for name in (prog, prog + "-static"):
        for f in os.listdir(gtdir):
            stem = f[:-5]
            if stem == name or stem.endswith("__" + name):
                return load(os.path.join(gtdir, f))
    return None


def suffix_match(ours, theirs):
    return theirs == ours or theirs.endswith("/" + ours.lstrip("./"))


def main():
    off_root, on_root = sys.argv[1], sys.argv[2]
    gtdir = sys.argv[3] if len(sys.argv) > 3 else None
    bad = False
    for run in sorted(os.listdir(off_root)):
        fo = os.path.join(off_root, run, "icalls.json")
        fn = os.path.join(on_root, run, "icalls.json")
        if not (os.path.isfile(fo) and os.path.isfile(fn)):
            continue
        off, on = load(fo), load(fn)
        extra = [(s, t) for s, ts in on.items() for t in ts
                 if t not in off.get(s, ())]
        removed = [(s, t) for s, ts in off.items() for t in ts
                   if t not in on.get(s, ())]
        npairs = sum(len(v) for v in off.values())
        line = (f"{run}: {npairs} pairs, -{len(removed)} removed, "
                f"+{len(extra)} added")
        if extra:
            bad = True
            line += "  VIOLATION " + "; ".join(f"{s} {t}" for s, t in extra[:5])
        gt = gt_for(run, gtdir) if gtdir else None
        if gt is not None:
            lost = []
            for s, t in removed:
                for gs, gts in gt.items():
                    if t in gts and suffix_match(s, gs):
                        lost.append((s, t))
                        break
            line += f", GT-observed removed {len(lost)}"
            if lost:
                bad = True
                line += "  RECALL-LOSS " + "; ".join(
                    f"{s} {t}" for s, t in lost[:5])
        print(line)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
