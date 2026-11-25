- A `#[comment = "…"]` annotation on a function is copied into the generated
  assembly, right after the label of the function; comment annotations on
  instructions are ignored. The comments of the generated assembly are block
  comments `/* … */`, the syntax that GNU as and LLVM accept on every target
  ([PR #1671](https://github.com/jasmin-lang/jasmin/pull/1671)).
