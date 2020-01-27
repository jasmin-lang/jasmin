# Jasmin

This repository contains the following subdirectories:

- compiler/ : Compiler from jasmin-lang to assembly.
- proofs/ : Coq implementations of compiler passes / checkers.

# Dependencies

- For the compiler: check compiler/README.md
- For the proofs:
  + Coq (>= 8.7)
  + The Mathematical Components library for Coq (>= 1.9)

# Testing

1. To compile and test the compiler:
   - `$ cd compiler`
   - `$ make CIL build`
   - `$ make tests`
2. To compile Coq proofs:
   - `$ cd proofs`
   - `$ make`

# License

All our code is MIT licensed. Since we use GPL licensed third party Coq
theories and extract code from the LGPL licensed Coq standard library,
our compiler is GPL licensed.
