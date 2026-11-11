A #[comment = "…"] annotation on a function is printed in the assembly, right
after the label of the function, one comment line per line of text.

  $ ../jasminc -arch x86-64 success/common/comment_annotations.jazz -o out.s
  $ grep -E '^[[:alnum:]_]*:$|^//' out.s
  main:
  // export function
  // second line
  incr:
  // local function
