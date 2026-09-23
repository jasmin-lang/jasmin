- With the Windows calling convention, export functions that use callee-saved
  vector registers (`xmm6`–`xmm15`) compile: each callee-saved register is
  saved in a stack slot of its own size and alignment
  ([PR #1583](https://github.com/jasmin-lang/jasmin/pull/1583);
  fixes [#1581](https://github.com/jasmin-lang/jasmin/issues/1581)).
