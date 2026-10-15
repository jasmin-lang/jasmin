- On armv8a, saving or restoring a callee-saved register, or the saved stack
  pointer, of an export function no longer compiles to a load or store that does
  not assemble, such as `ldr x19, [sp, #36864]` in a large stack frame
  ([PR #1639](https://github.com/jasmin-lang/jasmin/pull/1639)).
