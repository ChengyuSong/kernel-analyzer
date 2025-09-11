#!/usr/bin/env python3
"""
 Reachability-based Call Graph Analysis

 Copyrigth (C) 2024 - 2025 Haochen Zeng

 For licensing details see LICENSE
"""

import os
import sys

def get_bids():
    bids = []
    with open(bid_file, 'r') as fd:
        for raw in fd:
            line = raw.strip()
            if not line or line.startswith('#'):
                continue
            first_field = line.split(',', 1)[0].strip()
            try:
                bids.append(int(first_field))
            except ValueError:
                print(f"[WARN] Skip invalid bid line: {line}", file=sys.stderr)
    return bids

def load_mappings(path):
    """Read mapping_file into a dict: bid → (filepath, line_no)."""
    mappings = {}
    with open(path, 'r') as f:
        for raw in f:
            line = raw.strip()
            if not line or line.startswith('#'):
                continue
            parts = line.split(',')
            if len(parts) < 2:
                continue
            bid_str = parts[0].strip()
            loc = parts[-1].strip()
            if ':' not in loc:
                continue
            file_path, lineno_str = loc.rsplit(':', 1)
            try:
                bid = int(bid_str)
                lineno = int(lineno_str)
            except ValueError:
                continue
            mappings[bid] = (file_path, lineno)
    return mappings

def show_context(file_path, line_no, bid):
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

    print(f"\n--- BID({bid}) context: {os.path.basename(file_path)}:{line_no}---")
    print("```")
    for i in range(start, end):
        prefix = "=> " if i == idx else "   "
        # Pad line numbers for readability
        print(f"{prefix}{i+1:4d}: {lines[i].rstrip()}")
    print("```")

def main():
    # Path to your bid -> location mapping
    global mapping_file, bid_file
    target_program = ""
    if len(sys.argv) > 1:
        target_program = sys.argv[1].strip() + "_"
    mapping_file = f'{target_program}bid_loc_mapping.txt'
    bid_file = f"{target_program}critical_BBs.txt"
    
    if not os.path.exists(mapping_file):
        print(f"[ERROR] Mapping file not found: {mapping_file}", file=sys.stderr)
        sys.exit(1)
    if not os.path.exists(bid_file):
        print(f"[ERROR] Critical BIDs file not found: {bid_file}", file=sys.stderr)
        sys.exit(1)
    
    # load all mappings at once
    mappings = load_mappings(mapping_file)
    critical_bids = get_bids()
    for bid in critical_bids:
        if bid not in mappings:
            print(f"[WARN] No mapping found for bid {bid}", file=sys.stderr)
            continue
        filepath, lineno = mappings[bid]
        show_context(filepath, lineno, bid)

if __name__ == '__main__':
    main()