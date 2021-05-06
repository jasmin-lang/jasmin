#!/bin/sh

mkdir -p src

for p in ../../compiler/tests/cost/crypto/*.jazz
do
	../../compiler/jasminc -o src/$(basename $p .jazz).s $p
done
