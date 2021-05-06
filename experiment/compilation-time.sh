#!/bin/sh

SRC=../compiler/tests/cost/crypto/*.jazz
RUNS=32

for p in $SRC
do
	CSV=$(basename $p .jazz).csv
	hyperfine --warmup 1 --runs $RUNS --parameter-list compiler $JASMIN_REF,$JASMIN_CT --export-csv $CSV "{compiler}/jasminc $p"
done
