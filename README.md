# Jasmin

This repository contains the following subdirectories:

- compiler/ : Compiler from jasmin-lang to assembly.
- proofs/ : Coq implementations of compiler passes / checkers.
- rust-lib/ : Rust library (and macros) for compiling jasmin-lang with `rustc`. 
- examples/ : Example implementations (curve25519).

# Dependencies

- Rust nightly (tested with rustup)
- Coq, ssreflect, Ocaml (tested with opam)

# Testing

1. Compile Coq theories and extract modules for compiler:
   - `$ cd proofs` 
   - `$ make`
2. Compile and test compiler
   - `$ cd compiler`
   - `$ ./scripts/run_tests.py`
3. Compile and test rust support library:
   - `$ cd rust-lib`
   - `$ cargo test --release`
4. Compile and test example with Rust compiler:
   - `$ cd examples/curve25519`
   - `$ cargo test --release`

