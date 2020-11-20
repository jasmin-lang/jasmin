# Jasmin

This repository contains the following subdirectories:

- compiler/pipeline-examples/: Examples and experiments of the
  pipeline cost analysis.
- compiler/ : Compiler from jasmin-lang to assembly.
  The compiler includes the pipeline cost analyzer.
- proofs/ : Coq implementations of compiler passes / checkers.

# Dependencies

- For the compiler: check compiler/README.md

  We recommand using Nix: simply use nix-shell in the root directory
  (*not* in the compiler/ directory) to automatically jump in a shell
  with all dependencies installed.
- For the proofs:
  + Coq (>= 8.7)
  + The Mathematical Components library for Coq (>= 1.9)

  Note that using nix-shell in the root directory will correctly install all
  Coq dependencies.

# Building the Jasmin compiler and the cost analyzer:

1. To compile, first compile the proofs:
   - `$ cd proofs; make)`
   - `$ make`
   - `$ cd ..`
   Then, back at the root directory, build the compiler:    
   - `$ cd compiler`
   - `$ make CIL build`
   - `$ make`
   Optionally, test the compiler:
   - `$ make tests`
2. To test the pipeline analyzer, once the compiler is built:
   - `$ cd compiler/pipeline-examples/`
   - `$ ./run-analysis` (bash version >= 4 required)
   - `$ ./run-analysis-crypto` (bash version >= 4 required, takes several hours)
   
   For more information please consult compiler/pipeline-examples/README.md

# Pipeline Analysis Experiments

See compiler/pipeline-examples/README.md

# License

All our code is MIT licensed. Since we use GPL licensed third party Coq
theories and extract code from the LGPL licensed Coq standard library,
our compiler is GPL licensed.
