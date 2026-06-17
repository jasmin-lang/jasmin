- Array accesses are by default considered as “unaligned”, i.e., without any
  requirement on the alignment of the underlying pointer; this usually relaxes
  the assumptions made about arguments to export functions
  ([PR 1485](https://github.com/jasmin-lang/jasmin/pull/1485)).
