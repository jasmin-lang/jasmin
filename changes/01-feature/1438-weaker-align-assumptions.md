- The compiler now warns when array arguments to export functions are assumed to
  have some unexpected alignment. Such arrays are expected to be aligned to the
  declared size of their elements, unless the `-only-trivial-alignment`
  command-line flag is used, in which case they are not expected to have any
  specific alignment.
  ([PR 1438](https://github.com/jasmin-lang/jasmin/pull/1438)).
