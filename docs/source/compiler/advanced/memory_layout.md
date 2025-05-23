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
