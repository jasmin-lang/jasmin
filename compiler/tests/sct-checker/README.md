# Tests of the SCT checker

This directory contains the test suite of the speculative constant-time (SCT)
checker.

Run it with `dune runtest` (see documentation of dune for details).

If the output of some test changes, use `dune promote` to update the
`*.expected` files that contain the expected output. (If the change is not
expected, fix the test or the checker instead.)

The `success/` directory contains files that are supposed to successfully
type-check. Sub-directory are ignored. Expected output of the type checker is
saved in the file `accept.expected`. Please add positive test cases in this
directory.

The `fail/` directory contains programs made of functions that are supposed to
fail to type-check (unless they are declared `inline`). Sub-directory are
ignored. Every non-inline function is type-checked in turn. Expected output of
the type checker is saved in the file `reject.expected`. Please add negative
test cases in this directory.

The `sct_errors` case (and the `error_messages.jazz` program) is meant to
trigger many (all should be nice) of the possible error messages of the checker.
