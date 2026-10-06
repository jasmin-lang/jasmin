# How to compile a Jasmin program to assembly

The `jasminc` program takes as argument (on the command line) the name of a Jasmin source file to compile.
The default behavior is to discard the result of the compilation.

When the `-pasm` command-line flag is given, the generated assembly code is printed to the standard output.

When the `-o asmFileName` option is given (where `asmFileName` is a valid file name of your choice),
the generated assembly is written to that file.

The assembly program is ready to be consumed by common assemblers,
such as the GNU assembler.

When the `-g` option is enabled, the generated assembly is annotated with DWARF2 line number information.
This allows debuggers such as `gdb` to map assembly instructions back to their corresponding source code lines,
making it easier to understand and debug the program.

Declassification instructions are emitted as comments in the assembly output.

When the `-function-sections` option is given, each function is emitted in a
section of its own, named `.text.<name>`, so that a linker invoked with
`--gc-sections` drops the functions that are not reached. The option applies to
ELF targets only and is ignored when the target system is macOS.

The linker is then free to place a function and its callers at any distance,
and when a callee is out of the range of a direct branch, it routes the call
through a *veneer* (also called a thunk): a short sequence of its own that
loads the address of the callee into a register and branches through that
register. The compiler keeps those registers (`r12` on ARM, `x16` and `x17` on
ARMv8-A) free across every call internal to a compilation unit, which the
verified compiler enforces. The register allocation can therefore differ with
and without the option. A veneer makes the call an indirect branch, which the
generated assembly does not show. The consequences for speculative
constant-time are described in
[Lowering of SLH instructions](../compiler/passes/lower_slh).
