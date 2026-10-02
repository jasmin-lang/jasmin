- Global variables can now be extracted to EasyCrypt as operators
  instead of abbreviations, and their machine words can be printed as
  signed or unsigned integers. The default is selected by the
  `--global-model` command line argument of `jasmin2ec` and can be
  overridden for each global variable by the `#[abbrev]`, `#[op]`, and
  `#[sign=...]` annotations; see the
  [documentation](https://jasmin-lang.readthedocs.io/en/latest/tools/jasmin2ec.html#extraction-of-global-variables)
  ([PR #1549](https://github.com/jasmin-lang/jasmin/pull/1549)).
