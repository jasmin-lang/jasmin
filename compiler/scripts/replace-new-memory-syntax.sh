#!/bin/sh
for f in $(find . -name "*.jazz" -o -name "*.jinc")
do
  sed -i -f $(dirname $0)/replace-new-memory-syntax-sedscript "$f"
done

