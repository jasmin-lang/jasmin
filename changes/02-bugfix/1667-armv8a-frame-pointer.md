- On armv8a, register allocation no longer uses `x29`, the frame pointer, so
  it keeps addressing a valid frame record as Apple platforms require
  ([PR #1667](https://github.com/jasmin-lang/jasmin/pull/1667)).
