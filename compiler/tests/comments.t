A #[comment = "…"] annotation on a function is printed in the assembly, right
after the label of the function, one comment line per line of text.

  $ ../jasminc -arch x86-64 -system linux success/common/comment_annotations.jazz -o out.s
  $ grep -E '^[[:alnum:]_]*:$|^//' out.s
  main:
  // export function
  // second line
  incr:
  // local function

A line ends with a newline, possibly preceded by a carriage return. Any other
carriage return is printed as text: some assemblers (e.g., LLVM) end the comment
at a carriage return and would read the rest of the line as code.

  $ ../jasminc -arch x86-64 success/common/comment_carriage_return.jazz -o cr.s
  $ grep '^//' cr.s
  // one\rtwo
  // three
