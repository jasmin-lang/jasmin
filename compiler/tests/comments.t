A #[comment = "…"] annotation on a function is printed in the assembly, right
after the label of the function, one comment line per line of text.

  $ F=success/common/comment_annotations.jazz
  $ COMMENTS='^[[:alnum:]_]*:$|^//'

  $ ../jasminc -arch x86-64 $F -o x86-64.s
  $ grep -E "$COMMENTS" x86-64.s
  main:
  // export function
  // second line
  incr:
  // local function

  $ ../jasminc -arch arm-m4 $F -o arm-m4.s 2> /dev/null
  $ grep -E "$COMMENTS" arm-m4.s
  main:
  // export function
  // second line
  incr:
  // local function

  $ ../jasminc -arch armv8a $F -o armv8a.s
  $ grep -E "$COMMENTS" armv8a.s
  main:
  // export function
  // second line
  incr:
  // local function

  $ ../jasminc -arch riscv $F -o riscv.s 2> /dev/null
  $ grep -E "$COMMENTS" riscv.s
  main:
  // export function
  // second line
  incr:
  // local function
