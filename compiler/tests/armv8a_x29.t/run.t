On ARMv8-A, x29 is the frame pointer (AAPCS64; macOS requires it to hold a
valid frame record) and is never allocated. fits has 28 values and the
pointer live at once; spills needs every other allocatable register.

  $ for s in linux macosx; do
  >   for f in fits spills; do
  >     ../../jasminc -arch armv8a -system $s $f.jazz -o $f-$s.s || echo "$f $s: failed"
  >     if grep -q -w -e x29 -e w29 $f-$s.s; then echo "$f $s: uses x29"; else echo "$f $s: x29 free"; fi
  >   done
  > done
  fits linux: x29 free
  spills linux: x29 free
  fits macosx: x29 free
  spills macosx: x29 free
