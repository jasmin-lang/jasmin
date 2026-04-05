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
