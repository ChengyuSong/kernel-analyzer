#!/usr/bin/env python3
"""kdoc_invoke.py — tier-3 proposer input: corroborate INVOKE census
candidates against kerneldoc (task #28).

The kernel documents pair-correlated dispatch in stereotyped kerneldoc
idioms ("@dev_id: A cookie passed back to the handler function"), which
is the INVOKE relation in natural language. This tool takes census
candidates (InvokeCensus/ConfirmInvoke REVIEW lines), extracts each
function's kerneldoc from the kernel tree, matches the fn/data idioms
against the @param blocks, and emits proposal lines with the matched
doc sentence as provenance.

Docs describe INTENT: output feeds the proposer tier only. The body
confirmer / file review remain the soundness gate. The callee formal
index (fK) is not derivable from docs — proposals carry f? for review
against the callback typedef.

Usage:
  kdoc_invoke.py --kernel-tree ~/fast/linux/linux-6.8.2 \
                 --census-log km-census2.log \
                 [--summaries func_summaries.txt]   # skip adopted names
"""
import argparse
import os
import re
import subprocess
import sys
from collections import namedtuple

Cand = namedtuple("Cand", "name shape argf argd fk callsites constfn")

FN_PAT = re.compile(
    r"\b(callback|handler|function (to (be )?)?(call(ed)?|invoke[d]?|"
    r"execute[d]?|run)|called (when|for|on|from)|invoked|"
    r"thread function)\b", re.I)
DATA_PAT = re.compile(
    r"\b(cookie|passed( back)? (to|as|into)|argument (to|for|of)|"
    r"data (pointer )?(passed|given|provided|for)|context (pointer|data|for)|"
    r"private data|opaque (pointer|data|value)|user data|"
    r"as (the )?(first |second |sole |only )?(argument|parameter))\b", re.I)


def parse_census(path):
    cands = {}
    ln = re.compile(
        r"InvokeCensus: (DIRECT|FIELD|COSTORE|PASSTHRU) (\S+) fn=arg(\d+)"
        r" data=arg(\d+)(?: f(\d+))? callsites=(\d+) constFn=(\d+)")
    rv = re.compile(r"ConfirmInvoke: REVIEW (\S+) \((DIRECT|PASSTHRU), (\S+)\)")
    for line in open(path, errors="replace"):
        m = ln.search(line)
        if m:
            c = Cand(m.group(2), m.group(1), int(m.group(3)), int(m.group(4)),
                     int(m.group(5)) if m.group(5) else None,
                     int(m.group(6)), int(m.group(7)))
            # keep the highest-evidence entry per (name, argf, argd)
            key = (c.name, c.argf, c.argd)
            if key not in cands or cands[key].constfn < c.constfn:
                cands[key] = c
            continue
        m = rv.search(line)
        if m and not any(k[0] == m.group(1) for k in cands):
            cands[(m.group(1), -1, -1)] = Cand(
                m.group(1), "REVIEW-" + m.group(2), -1, -1, None, 0, 0)
    return list(cands.values())


def summarized_names(path):
    names = set()
    for line in open(path):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        names.add(line.split()[0].rstrip("*"))
    return names


def find_kdoc_blocks(tree, names):
    """One grep pass for ' * <name> - ' kerneldoc headers."""
    alt = "|".join(re.escape(n) for n in names)
    pat = r"^[[:space:]]*\*[[:space:]]*(" + alt + r")[[:space:]]+-[[:space:]]"
    try:
        out = subprocess.run(
            ["grep", "-rnE", "--include=*.c", "--include=*.h", pat, tree],
            capture_output=True, text=True, timeout=600).stdout
    except subprocess.TimeoutExpired:
        sys.exit("grep over kernel tree timed out")
    hits = {}  # name -> (file, line)
    hdr = re.compile(r"^(.*?):(\d+):\s*\*\s*(\w+)\s+-\s")
    for line in out.splitlines():
        m = hdr.match(line)
        if m and m.group(3) in names and m.group(3) not in hits:
            hits[m.group(3)] = (m.group(1), int(m.group(2)))
    return hits


def extract_params(path, lineno):
    """Walk the kerneldoc block; return ordered [(param, text)]."""
    lines = open(path, errors="replace").read().splitlines()
    i = lineno - 1
    # back up to /**
    start = i
    while start > 0 and "/**" not in lines[start]:
        start -= 1
    end = i
    while end < len(lines) and "*/" not in lines[end]:
        end += 1
    params, cur = [], None
    prm = re.compile(r"^\s*\*\s*@(\w+|\.\.\.):\s*(.*)")
    cont = re.compile(r"^\s*\*\s{2,}(\S.*)")
    for l in lines[start:end]:
        m = prm.match(l)
        if m:
            if m.group(1).lower() in ("return", "returns", "note", "context"):
                cur = None
                continue
            cur = [m.group(1), m.group(2)]
            params.append(cur)
            continue
        m = cont.match(l)
        if m and cur is not None:
            cur[1] += " " + m.group(1)
            continue
        cur = None
    return [(p, t.strip()) for p, t in params]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--kernel-tree", required=True)
    ap.add_argument("--census-log", required=True)
    ap.add_argument("--summaries", help="skip names already summarized")
    args = ap.parse_args()

    cands = parse_census(args.census_log)
    if args.summaries:
        done = summarized_names(args.summaries)
        cands = [c for c in cands if c.name not in done]
    if not cands:
        sys.exit("no candidates")
    names = {c.name for c in cands}
    blocks = find_kdoc_blocks(args.kernel_tree, names)

    n_agree = n_doconly = n_nodoc = n_mismatch = 0
    for c in sorted(cands, key=lambda c: -c.constfn):
        loc = blocks.get(c.name)
        print(f"\n{c.name}  census: {c.shape} fn=arg{c.argf} data=arg{c.argd}"
              f" callsites={c.callsites} constFn={c.constfn}")
        if not loc:
            n_nodoc += 1
            print("  doc: NONE (no kerneldoc block found)")
            continue
        params = extract_params(*loc)
        rel = os.path.relpath(loc[0], args.kernel_tree)
        fn_idx = [i for i, (p, t) in enumerate(params) if FN_PAT.search(t)]
        data_idx = [i for i, (p, t) in enumerate(params)
                    if DATA_PAT.search(t) and i not in fn_idx]
        for i in fn_idx + data_idx:
            p, t = params[i]
            kind = "fn " if i in fn_idx else "data"
            print(f"  doc[{rel}:{loc[1]}] {kind} @{p}(#{i}): {t[:110]}")
        if c.argf < 0:
            n_doconly += 1
            continue
        agree_f = c.argf in fn_idx
        agree_d = c.argd in data_idx
        if agree_f and agree_d:
            n_agree += 1
            fk = f"f{c.fk}" if c.fk is not None else "f?"
            note = "" if c.fk is not None else \
                "   # fK: review the callback typedef"
            print(f"  AGREE -> propose: {c.name} "
                  f"INVOKE(arg{c.argf}:{fk}<-arg{c.argd}){note}")
        elif fn_idx or data_idx:
            n_mismatch += 1
            print(f"  PARTIAL: doc fn={fn_idx} data={data_idx} vs census "
                  f"fn={c.argf} data={c.argd} — review")
        else:
            n_doconly += 1
            print("  doc found but no fn/data idiom matched")
    print(f"\n== {len(cands)} candidates: {n_agree} AGREE, "
          f"{n_mismatch} PARTIAL, {n_nodoc} no-doc, rest doc-neutral")


if __name__ == "__main__":
    main()
