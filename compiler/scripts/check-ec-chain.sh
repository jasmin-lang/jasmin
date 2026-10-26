#!/usr/bin/env bash

# Regression check of the extraction to EasyCrypt for safety.
#
# Usage: scripts/check-ec-chain.sh OUTDIR
# (run from the compiler directory, after `make`)
#
# Each program of the corpus below is extracted with `jasmin2ec --safety`
# into OUTDIR/<group>/<name>.ec, where <group> names the directory of the
# program (two directories may hold programs of the same name). The script
# then checks every extracted file with EasyCrypt and reports the programs
# that do not extract and the files that do not check, with their logs in
# OUTDIR/<group>/<name>.log.

set -u

if [ $# -ne 1 ]; then
  echo "usage: $0 OUTDIR" >&2
  exit 2
fi

COMPILER=$(cd "$(dirname "$0")/.." && pwd)
ECLIB=$COMPILER/../eclib
JASMIN2EC=$COMPILER/jasmin2ec
OUT=$1
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)

# The corpus: directory of the programs, relative to the compiler directory.
DIRS="
examples/extraction-unit-tests
examples/gimli/x86-64
examples/extraction-safety-unit-tests
tests/success/common
tests/success/x86-64
"

total=0
extracted=()
failed_extract=()

for d in $DIRS; do
  group=$(echo "$d" | tr / _)
  mkdir -p "$OUT/$group"
  for f in "$COMPILER/$d"/*.jazz; do
    name=$(basename "$f" .jazz)
    total=$((total + 1))
    if "$JASMIN2EC" --safety -o "$OUT/$group/$name.ec" "$f" \
         > "$OUT/$group/$name.extract.log" 2>&1; then
      extracted+=("$group/$name")
    else
      failed_extract+=("$group/$name")
    fi
  done
done

echo "== extraction: ${#extracted[@]}/$total"
for p in "${failed_extract[@]+"${failed_extract[@]}"}"; do
  echo "  FAIL $p: $(grep -v '^Please report' "$OUT/$p.extract.log" | tail -n 1)"
done

# Each file is checked in its own directory, where the extraction put the
# theories it requires.
checked=0
failed_check=()
for p in "${extracted[@]+"${extracted[@]}"}"; do
  if (cd "$OUT/$(dirname "$p")" &&
      easycrypt compile -I "Jasmin:$ECLIB" "$(basename "$p").ec") \
       > "$OUT/$p.log" 2>&1; then
    checked=$((checked + 1))
  else
    failed_check+=("$p")
  fi
done

echo "== EasyCrypt: $checked/${#extracted[@]}"
for p in "${failed_check[@]+"${failed_check[@]}"}"; do
  echo "  FAIL $p: see $OUT/$p.log"
done

[ ${#failed_extract[@]} -eq 0 ] && [ ${#failed_check[@]} -eq 0 ]
