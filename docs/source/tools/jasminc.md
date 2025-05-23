# How to compile a Jasmin program to assembly

The `jasminc` program takes as argument (on the command line) the name of a Jasmin source file to compile.
The default behavior is to discard the result of the compilation.

When the `-pasm` command-line flag is given, the generated assembly code is printed to the standard output.

When the `-o asmFileName` option is given (where `asmFileName` is a valid file name of your choice),
the generated assembly is written to that file.

The assembly program is ready to be consumed by common assemblers,
such as the GNU assembler.
