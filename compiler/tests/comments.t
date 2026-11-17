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

A comment that contains "*/" would end the block comment early and have the rest
of the line read as code, so it is refused.

  $ cat > end.jazz << EOF
  > #[comment = "one */ ret /* two"]
  > export fn f(reg u32 x) -> reg u32 { return x; }
  > EOF
  $ ../jasminc -arch x86-64 end.jazz -o end.s
  assembly printing: the comment “one */ ret /* two” contains “*/”
  [1]
