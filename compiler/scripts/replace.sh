#!/bin/sh
for f in $(find . -name "*.jazz" -o -name "*.jinc")
do
  sed -i 's/( *\(u[0-9]*\) *) *\[ *#aligned/[#aligned:\1/g' "$f"
  sed -i 's/( *\(u[0-9]*\) *) *\[ *#unaligned/[#unaligned:\1/g' "$f"
  sed -i 's/( *\(u[0-9]*\) *) *\[/[:\1 /g' "$f"
  sed -i 's/\[ *#aligned *\(u[0-9]*\)/[#aligned:\1/g' "$f"
  sed -i 's/\[ *#unaligned *\(u[0-9]*\)/[#unaligned:\1/g' "$f"
  sed -i 's/\[ *\(u[0-9]*\)/[:\1/g' "$f"
done

