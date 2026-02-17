#!/usr/bin/env python3
"""Loader/query helpers for kanalyzer V-snapshot files.

Binary format (little-endian):
  magic[8] = b"KAVSNAP1"
  u32 version
  u32 flags
  u32 label_v
  u32 reserved
  u64 node_count
  u64 rep_count
  u64 metadata_json_size
  metadata_json bytes
  node_to_rep[node_count] as varuint
  rep_to_node[rep_count] as varuint
  rep rows:
    for each rep:
      degree as varuint
      sorted dsts as delta-varuint
  named entries:
    count as varuint
    repeated:
      node as varuint
      kind as u8
      name_len as varuint
      name bytes
"""

from __future__ import annotations

from dataclasses import dataclass
from bisect import bisect_left
import json
import struct
from collections import defaultdict
from typing import Dict, List, Tuple


MAGIC = b"KAVSNAP1"
VERSION = 1


@dataclass(frozen=True)
class NamedEntry:
    node: int
    kind: int
    name: str


class VSnapshot:
    def __init__(
        self,
        label_v: int,
        flags: int,
        metadata: Dict,
        node_to_rep: List[int],
        rep_to_node: List[int],
        rep_rows: List[List[int]],
        named_entries: List[NamedEntry],
    ) -> None:
        self.label_v = label_v
        self.flags = flags
        self.metadata = metadata
        self.node_to_rep = node_to_rep
        self.rep_to_node = rep_to_node
        self.rep_rows = rep_rows
        self.named_entries = named_entries

        self.node_count = len(node_to_rep)
        self.rep_count = len(rep_to_node)

        self.rep_members: List[List[int]] = [[] for _ in range(self.rep_count)]
        for node, rep in enumerate(node_to_rep):
            self.rep_members[rep].append(node)

        name_to_nodes: Dict[str, List[int]] = defaultdict(list)
        for e in named_entries:
            name_to_nodes[e.name].append(e.node)
        self.name_to_nodes = dict(name_to_nodes)

    @staticmethod
    def _read_varuint(buf: memoryview, pos: int) -> Tuple[int, int]:
        value = 0
        shift = 0
        while pos < len(buf):
            b = buf[pos]
            pos += 1
            value |= (b & 0x7F) << shift
            if (b & 0x80) == 0:
                return value, pos
            shift += 7
            if shift >= 64:
                raise ValueError("invalid varuint (too many bytes)")
        raise ValueError("truncated varuint")

    @classmethod
    def load(cls, path: str) -> "VSnapshot":
        with open(path, "rb") as f:
            raw = f.read()
        buf = memoryview(raw)

        if len(buf) < 48:
            raise ValueError("snapshot is too small")
        if bytes(buf[:8]) != MAGIC:
            raise ValueError("snapshot magic mismatch")

        version, flags, label_v, _reserved = struct.unpack_from("<IIII", buf, 8)
        if version != VERSION:
            raise ValueError(f"unsupported snapshot version {version}")
        node_count, rep_count, meta_size = struct.unpack_from("<QQQ", buf, 24)
        pos = 48

        if pos + meta_size > len(buf):
            raise ValueError("metadata exceeds file bounds")
        metadata_raw = bytes(buf[pos : pos + meta_size])
        pos += meta_size
        metadata = json.loads(metadata_raw.decode("utf-8")) if metadata_raw else {}

        node_to_rep = [0] * node_count
        for i in range(node_count):
            v, pos = cls._read_varuint(buf, pos)
            if v >= rep_count:
                raise ValueError("node_to_rep out of range")
            node_to_rep[i] = v

        rep_to_node = [0] * rep_count
        for i in range(rep_count):
            v, pos = cls._read_varuint(buf, pos)
            if v >= node_count:
                raise ValueError("rep_to_node out of range")
            rep_to_node[i] = v

        rep_rows: List[List[int]] = [[] for _ in range(rep_count)]
        for r in range(rep_count):
            degree, pos = cls._read_varuint(buf, pos)
            row: List[int] = []
            prev = 0
            for i in range(degree):
                delta, pos = cls._read_varuint(buf, pos)
                cur = delta if i == 0 else prev + delta
                if cur >= rep_count:
                    raise ValueError("rep row destination out of range")
                row.append(cur)
                prev = cur
            rep_rows[r] = row

        named_entries: List[NamedEntry] = []
        if pos < len(buf):
            named_count, pos = cls._read_varuint(buf, pos)
            for _ in range(named_count):
                node, pos = cls._read_varuint(buf, pos)
                if pos >= len(buf):
                    raise ValueError("truncated named entry kind")
                kind = int(buf[pos])
                pos += 1
                nlen, pos = cls._read_varuint(buf, pos)
                if pos + nlen > len(buf):
                    raise ValueError("truncated named entry name")
                name = bytes(buf[pos : pos + nlen]).decode("utf-8")
                pos += nlen
                named_entries.append(NamedEntry(node=int(node), kind=kind, name=name))
        if pos != len(buf):
            raise ValueError("trailing bytes after snapshot payload")

        return cls(
            label_v=label_v,
            flags=flags,
            metadata=metadata,
            node_to_rep=[int(x) for x in node_to_rep],
            rep_to_node=[int(x) for x in rep_to_node],
            rep_rows=[[int(y) for y in row] for row in rep_rows],
            named_entries=named_entries,
        )

    def rep(self, node: int) -> int:
        if node < 0 or node >= self.node_count:
            raise IndexError(f"node out of range: {node}")
        return self.node_to_rep[node]

    def may_alias(self, node_a: int, node_b: int) -> bool:
        rep_a = self.rep(node_a)
        rep_b = self.rep(node_b)
        row = self.rep_rows[rep_a]
        i = bisect_left(row, rep_b)
        return i < len(row) and row[i] == rep_b

    def aliases_of_rep(self, rep: int) -> List[int]:
        if rep < 0 or rep >= self.rep_count:
            raise IndexError(f"rep out of range: {rep}")
        return self.rep_rows[rep]

    def aliases_of_node(self, node: int) -> List[int]:
        return self.aliases_of_rep(self.rep(node))

    def resolve_name(self, name: str) -> List[int]:
        return list(self.name_to_nodes.get(name, []))

    def may_alias_name(self, name_a: str, name_b: str) -> bool:
        nodes_a = self.resolve_name(name_a)
        nodes_b = self.resolve_name(name_b)
        for a in nodes_a:
            for b in nodes_b:
                if self.may_alias(a, b):
                    return True
        return False
