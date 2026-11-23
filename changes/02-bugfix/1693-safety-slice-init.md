- The safety checker no longer keeps the destination of a slice copy at an
  unknown offset initialized when the copy may read undefined cells, and marks
  the right cells when a string is written into a slice
  ([PR #1693](https://github.com/jasmin-lang/jasmin/pull/1693)).
