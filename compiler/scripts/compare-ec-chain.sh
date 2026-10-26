#!/usr/bin/env bash

# Comparison of the plain extraction to EasyCrypt with the plain extraction
# through the passes of the extraction for safety.
#
# Usage: scripts/compare-ec-chain.sh OUTDIR
# (run from the compiler directory, after `make`)
#
# Each program of the corpus of check-ec-chain.sh is extracted with
# `jasmin2ec` into OUTDIR/<group>/<name>.plain.ec and with
# `jasmin2ec --via-safety-chain` into OUTDIR/<group>/<name>.via.ec. The
# script reports the programs that one of the two does not extract and those
# whose two extractions differ, with their difference in
# OUTDIR/<group>/<name>.diff.

set -u

if [ $# -ne 1 ]; then
  echo "usage: $0 OUTDIR" >&2
  exit 2
fi

COMPILER=$(cd "$(dirname "$0")/.." && pwd)
JASMIN2EC=$COMPILER/jasmin2ec
OUT=$1
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)

DIRS="
examples/extraction-unit-tests
examples/gimli/x86-64
examples/extraction-safety-unit-tests
tests/success/common
tests/success/x86-64
"

total=0
same=0
failed=()
differ=()

for d in $DIRS; do
  group=$(echo "$d" | tr / _)
  mkdir -p "$OUT/$group"
  for f in "$COMPILER/$d"/*.jazz; do
    name=$(basename "$f" .jazz)
    p="$OUT/$group/$name"
    total=$((total + 1))
    if ! "$JASMIN2EC" -o "$p.plain.ec" "$f" > "$p.plain.log" 2>&1; then
      failed+=("$group/$name (plain)")
    elif ! "$JASMIN2EC" --via-safety-chain -o "$p.via.ec" "$f" \
           > "$p.via.log" 2>&1; then
      failed+=("$group/$name (via the safety chain)")
    elif diff "$p.plain.ec" "$p.via.ec" > "$p.diff"; then
      same=$((same + 1))
      rm -f "$p.diff"
    else
      differ+=("$group/$name")
    fi
  done
done

echo "== identical: $same/$total"
for p in "${failed[@]+"${failed[@]}"}"; do
  echo "  FAIL $p"
done
for p in "${differ[@]+"${differ[@]}"}"; do
  echo "  DIFF $p: see $OUT/$p.diff"
done
