A #[comment = "…"] annotation on a function is printed in the assembly, right
after the label of the function, one block comment per annotation.

  $ ../jasminc -arch x86-64 -system linux success/common/comment_annotations.jazz -o out.s
  $ awk '/^(main|incr):$/ { p = 1 } /^\t|^\./ { p = 0 } p' out.s
  main:
  /* export function
  second line */
  /* another comment */
  incr:
  /* local function */
