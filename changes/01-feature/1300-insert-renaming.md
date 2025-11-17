- The compiler automatically introduces renaming assignments at function export
  boundaries. This gives more flexibility to the register allocation and makes
  more programs accepted by the compiler. However, this may introduce
  unnecessary unwanted register-to-register “move” instructions. This can be
  disabled using the `-noinsertrenaming` command-line flag.
  ([PR #1300](https://github.com/jasmin-lang/jasmin/pull/1300)).
