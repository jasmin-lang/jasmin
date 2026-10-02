- The safety checker, when called after some compilation steps, no longer looks
  at the source prior to any compilation to guess assumed ranges for inputs
  (i.e., arguments to export functions); this behavior can be achieved using
  the `input_range` entry in the configuration file
  ([PR 1465](https://github.com/jasmin-lang/jasmin/pull/1465)).

