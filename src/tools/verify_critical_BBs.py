#!/usr/bin/env python3
"""
 Reachability-based Call Graph Analysis

 Copyrigth (C) 2024 - 2025 Haochen Zeng

 For licensing details see LICENSE
"""

import os
import sys

# Path to your bid -> location mapping
mapping_file = 'bid_loc_mapping.txt'
bid_file = "critical_BBs.txt"

def get_bids():
    bids = []
    lines = []
    with open(bid_file) as fd:
        lines = fd.readlines()
    for l in lines:
        items = l.split(',')
        assert len(items) >= 2
        bids.append(int(items[0].strip()))
    return bids

def load_mappings(path):
    """Read mapping_file into a dict: bid → (filepath, line_no)."""
    m = {}
    with open(path, 'r') as f:
        for raw in f:
            line = raw.strip()
            if not line:
                continue
            # split only into 4 parts so the filepath:linenumber stays together
            bid, _, _, loc = line.split(',', 3)
            if ':' not in loc:
                continue
            file_path, lineno = loc.rsplit(':', 1)
            try:
                lineno = int(lineno)
            except ValueError:
                continue
            m[int(bid)] = (file_path, lineno)
    return m

def show_context(file_path, line_no):
    """Print the line_no ± ctx lines from file_path."""
    if not os.path.exists(file_path):
        print(f"[ERROR] File not found: {file_path}", file=sys.stderr)
        return
    with open(file_path, 'r') as f:
        lines = f.readlines()
    # zero-based indices
    idx = line_no - 1
    start = max(0, idx - 2)
    end = min(len(lines), idx + 10 + 1)

    print(f"\n--- BID context: {os.path.basename(file_path)}:{line_no} ---")
    print("```")
    for i in range(start, end):
        prefix = "=> " if i == idx else "   "
        # Pad line numbers for readability
        print(f"{prefix}{i+1:4d}: {lines[i].rstrip()}")
    print("```")

def main():
    # load all mappings at once
    mappings = load_mappings(mapping_file)
    critical_bids = get_bids()
    for bid in critical_bids:
        if bid not in mappings:
            print(f"[WARN] No mapping found for bid {bid}", file=sys.stderr)
            continue
        filepath, lineno = mappings[bid]
        show_context(filepath, lineno)

if __name__ == '__main__':
    main()
