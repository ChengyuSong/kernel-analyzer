#!/usr/bin/env bash
# Run the caps-configurable KallGraph on one bitcode inside the sandbox.
# usage: eval/kallgraph-caps.sh <bitcode> <outdir> [KG_EDGE_CAP] [KG_NO_BLOCK]
set -euo pipefail
BC=$(readlink -f "$1"); OUT=$(readlink -f "$2"); CAP="${3:-35}"; NOBLOCK="${4:-}"
IMG="${KA_KG_IMAGE:-kallgraph-caps}"
mkdir -p "$OUT"; echo "/bc/$(basename "$BC")" > "$OUT/bc.list"
KGBIN=$(docker run --rm --network none "$IMG" sh -c 'find /opt/kallgraph/build -name KallGraph -type f | head -1')
docker run --rm --network none -u "$(id -u):$(id -g)" \
  -v "$(dirname "$BC"):/bc:ro" -v "$OUT:/out" \
  -e KG_EDGE_CAP="$CAP" ${NOBLOCK:+-e KG_NO_BLOCK=1} \
  "$IMG" "$KGBIN" @/out/bc.list -OutputDir=/out -ThreadNum="${KA_KG_THREADS:-16}"
