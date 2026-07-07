# Memory Layout

At the source level, Jasmin programs only use “external” memory that is managed by the calling program.
At the end of the compilation, the memory addressing space is shared between this external memory, global (immutable) variables, and local (stack) variables.

The layout of global data is undocumented and subject to change.

Each function has a stack frame that is allocated at the beginning of the execution of the function and freed at the end of the execution of the function.
This memory management is done implicitly in the semantics an Jasmin-stack programs (aka `sprog`) and explicitly in the code in linear and assembly programs.
The code for explicit memory management is in the callee for `export` functions but in the caller for `local` functions.

Each function stores in its stack frame its own local variables (the ones that are annotated with the `stack` modifier) but also some extra data: the contents of callee-saved registers (that may be modified during the execution of this function), the original value of the stack pointer and the return address.
Therefore each stack frame is split into two disjoint contiguous regions: the *data* part and the *extra* part.
The data part is at the bottom (lower addresses) and the extra part at the top (higher addresses).
This design allows to simply describe what part of the frame can be accessed by the user code and what part is reserved to the compiler-injected code.

Notice that to enforce alignment constraints, some padding may be added between the two parts.
Consider for example a function with one byte of local (stack) variable that save the stack pointer into its stack frame.
The frame must be aligned for 8-byte accesses (assuming 64-bit pointers) and the slot for the stack pointer similarly.
The local variable will thus be allocated at offset zero and the saved stack pointer at offset eight.
This means that there are seven *lost* (padding) bytes in the frame whose total size will be 16 bytes.
This is the worst possible case so this non-optimal padding should not be a source for concern.

Alignment constraints for stack memory accesses are satisfied through three mechanisms.
Top-level (`export`) functions enforce alignment of the stack pointer after the allocation of their frames (through a bit-level `AND` operation).
When allocating the stack frame of a local function, its size is rounded so as to preserve the alignment of the stack pointer.
The layout of each stack frame is computed assuming that the lowest address in the frame will be aligned.

Therefore there are three kinds of *padding*:

  - initially to align the “external” stack pointer (the exact quantity is statically unknown but bounded by the alignment constraint);
  - internally to each stack frame, between the data and extra parts; statically known, seven bytes at most;
  - on each (internal) function call to preserve the alignment of the stack pointer; statically known, bounded by the alignment constraint.

## Callee-saved registers

When an export function makes use of some callee-saved registers, either
directly or through the function it (transitively) calls, the values of these
registers are saved in its stack frame (in the “extra” part, as described above)
at the beginning of the function and restored at the end.

Since July 2026 (versions 2026.03.2 and 2026.07.0), the Jasmin compiler provides
some *eperimental* facility to control how much memory is allocated in the stack
frame of `export` functions to save the values of callee-saved registers. A
global option controls the general “strategy” which can be locally overridden by an
annotation.

### The `callee_saved = n` annotation

When an `export` function is annotated with `callee_saved = n` where `n` is some
non-negative value, the compiler will trust this information and provide room in
the stack frame for exactly n values. Do not forget to take into account the
stack-pointer register which is also a callee-saved register.

If the value given in the annotation is too large (i.e., pessimistic), then some
space is *wasted* in the frame but the spuriously reserved slots are not used.
A warning (disabled by default) can tell you when this happens.

If the value given in the annotation is too small, then compilation will fail,
with an error message providing a good value.

Note that when annotated with `callee_saved = 0`, a function may still use the
stack (and therefore modify the stack-pointer register). In this case, the
original value of the stack pointer will be saved in a free volatile register.

### Global strategies

For `export` functions that are not annotated with the number of calle-saved registers to use,
the compiler defaults to some strategy which can be selected through the `-callee-saved` command-line
flag which accepts one of the following values:
- `tight`
- `pessimistic`
- `optimistic`

The “tight” strategy is the default one: prior to stack-allocation, the compiler
runs register allocation to precisely compute how many callee-saved registers
will be used. This is costly as during compilation, register-allocation is run
twice.

The “pessimistic” strategy is safe and assumes that every function needs all
callee-saved registers; therefore, enough room is provided in the stack frame to
save *all* these registers, which are many in some architectures. This also
implies that each function has a prologue that sets up a stack frame, aligns the
stack pointer, etc.

The “optimistic” strategy assumes that no callee-saved register is required:
this produces assembly code that might be more efficient (no tampering with the
stack pointer, less stack usage) but is prone to failure (if volatile registers
are not enough).
