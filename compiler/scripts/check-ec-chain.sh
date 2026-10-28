#!/usr/bin/env bash

# Regression check of the extraction to EasyCrypt.
#
# Usage: scripts/check-ec-chain.sh OUTDIR
# (run from the compiler directory, after `make`)
#
# Each program of the corpus below is extracted in two modes: `jasmin2ec`
# (mode plain) and `jasmin2ec --safety` (mode safety), into
# OUTDIR/<mode>/<group>/<name>.ec, where <group> names the directory of the
# program (two directories may hold programs of the same name). The script
# then checks every extracted file with EasyCrypt and reports, for each mode,
# the programs that do not extract and the files that do not check, with
# their logs in OUTDIR/<mode>/<group>/<name>.log.

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

# The modes: name and options of jasmin2ec.
MODES="plain: safety:--safety"

status=0
for m in $MODES; do
  mode=${m%%:*}
  opts=${m#*:}
  total=0
  extracted=()
  failed_extract=()

  for d in $DIRS; do
    group=$(echo "$d" | tr / _)
    mkdir -p "$OUT/$mode/$group"
    for f in "$COMPILER/$d"/*.jazz; do
      name=$(basename "$f" .jazz)
      total=$((total + 1))
      # $opts is empty or a single option
      if "$JASMIN2EC" $opts -o "$OUT/$mode/$group/$name.ec" "$f" \
           > "$OUT/$mode/$group/$name.extract.log" 2>&1; then
        extracted+=("$mode/$group/$name")
      else
        failed_extract+=("$mode/$group/$name")
      fi
    done
  done

  echo "== $mode, extraction: ${#extracted[@]}/$total"
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

  echo "== $mode, EasyCrypt: $checked/${#extracted[@]}"
  for p in "${failed_check[@]+"${failed_check[@]}"}"; do
    echo "  FAIL $p: see $OUT/$p.log"
  done

  if [ ${#failed_extract[@]} -ne 0 ] || [ ${#failed_check[@]} -ne 0 ]; then
    status=1
  fi
done

exit $status
