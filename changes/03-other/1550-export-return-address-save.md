- On architectures where the caller passes the return address in a register
  and that register is available (ARM64, RISC-V), export functions now save
  and restore it through the same verified mechanism as callee-saved registers
  (a slot in the stack frame), instead of unverified glue emitted by the
  assembly printer around the function body. The one-varmap checker enforces
  that an export function whose body kills the return-address register saves
  it. Export functions that do not kill it (e.g. leaf functions) no longer
  touch the stack at all to save it. Note that the `callee_saved = n`
  annotation must now account for the return-address register when the
  function kills it. On ARM (Cortex-M4), LR is used as a scratch register by
  the compiler itself, so it is still saved around the body by the printer
  ([PR #1550](https://github.com/jasmin-lang/jasmin/pull/1550)).
