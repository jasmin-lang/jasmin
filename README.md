This is a copy of the Jasmin project extend with the work corresponding
to the paper "KEM-IND-CCA-Preserving Compilation of Jasmin's ML-KEM."


# Download, installation, and sanity-testing instructions

Detailed instruction are available at
[link](https://jasmin-lang.readthedocs.io/en/stable/misc/installation_guide.html)

## Dependencies

This formalization has been developed with the tools listed in the opam
file (located at the root of the project).

It is necessary to install either Nix ([link](https://nixos.org/)) or all
dependencies in the opam file to run this artifact.

A convenient way to get the correct dependencies is to use the nix package
manager and to run in this directory:
```
nix-shell
```
This will enter in a shell environment in which all these dependencies are
available.

Alternatively, `opam` can be used. To set up `opam` detail instruction are
available at [link](https://opam.ocaml.org/doc/Install.html). We require that a
valid `opam` switch is configured with a compiler version >= 4.12.0 and is set
as current switch.

First add the Rocq repository to the current opam switch
```
opam repo add coq-released https://coq.inria.fr/opam/released
```
then do
```
opam update
```
and install the dependencies listed in the opam file.


## Tested environment

- Operating system: Ubuntu 24.04.5 LTS (x86-64), dependencies provided by `nix-shell`.
- Rocq 9.0.1, compiled with OCaml 4.14.2.
- Expected build time for the proofs: about 20 minutes with a single job
  (measured: 18m27s); use `make -j N` to parallelize.
- Expected peak memory consumption: about 2 GB (measured: 1.8 GB maximum).

## Build

To run Rocq and check the validity of the proofs, run in the `proofs` directory:
```
make
```
This verifies all Rocq files. A successful check ends with `make` exiting with
status 0 and no `Error:` message in the output (warnings are expected).

Alternatively, to compile the full compiler, run in the root of the project:
```
make
```

# List of claims in the paper supported by this artifact

## Game-Based Security Definitions

The definition of oracle systems is in `proofs/compiler/cil.v`. The KEM-IND-CCA
definition is at the end of the file.

The probabilistic semantics of ITrees (and thus of cryptographic games) is in
`proofs/lang/dinterp.v`. In this file, `dinterp_eutt` corresponds to Theorem
2.1.

## Jasmin Semantics

The syntax of Jasmin is in `proofs/lang/expr.v`. The semantics is in
`proofs/lang/it_sems_core.v`.

The definition of game-based security for Jasmin programs is in
`proofs/compiler/end_to_end.v` (the `Source` instance). The definition for
assembly programs is in the same file (the `Target` instance). The instantiation
to KEMs is `KEM_of_Jazz` for either.

## Correctness and KEM-IND-CCA Preservation

The compiler correctness statement is `correct_comp` in
`proofs/compiler/end_to_end.v`. This is an instantiation of the more general
preservation result `it_compile_prog_to_asmP` in
`proofs/compiler/it_compiler_proof.v`.

The general security preservation theorem is `compiler_preserves` in
`proofs/compiler/end_to_end.v`, and its instantiation to KEM-IND-CCA is
`mlkem_end_to_end` in the same file.

Note that `mlkem_end_to_end` does not include the source-level KEM-IND-CCA
security proof of Jasmin's ML-KEM (it is prior work, proven in EasyCrypt).

## Relational Hoare Logic

The implementation of the logic is in `proofs/lang/relational_logic.v`.
Equivalence up-to-cutoff is defined as `xrutt` in `proofs/itrees/xrutt.v`.

- rule SKIP is `wequiv_nil` in `proofs/lang/relational_logic.v`.
- rule SEQ is `wequiv_cons` in `proofs/lang/relational_logic.v`.
- rule ASSIGN is `wequiv_assgn` in `proofs/lang/relational_logic.v`.
- rule COND is `wequiv_if` in `proofs/lang/relational_logic.v`.
- rule LOOP is `wequiv_while` in `proofs/lang/relational_logic.v`.
- rule RAND is `wequiv_syscall` in `proofs/lang/relational_logic.v`.
- rule CALL is `wequiv_call` in `proofs/lang/relational_logic.v`.
- rule CONSEQ is inlined in each rule.
- rule TRANS is `wequiv_trans` in `proofs/lang/relational_logic.v`.
- rule REC is `wequiv_fun_ind` in `proofs/lang/relational_logic.v`.

## Compiler Passes and Proofs

Front-End:
- Int Word: `proofs/compiler/wint_word_proof.v`: the proofs are in `Section IT`.
- Array Copy: `proofs/compiler/array_copy_proof.v`: the proofs are in `Section IT`.
- Array Initialization: `proofs/compiler/array_init_proof.v`: the proofs are in `Section IT`.
- Spilling: `proofs/compiler/lower_spill_proof.v`: the proofs are in `Section IT`.
- Inlining: `proofs/compiler/inline_proof.v`: the proofs are in `Section IT`.
- Function Pruning: `proofs/compiler/dead_calls_proof.v`: the proofs are in `Section IT`.
- Constant Propagation: `proofs/compiler/constant_prop_proof.v`: the proofs are in `Section IT`.
- Dead Code Elimination: `proofs/compiler/dead_code_proof.v`: the proofs are in `Section IT`.
- Unrolling: `proofs/compiler/unrolling_proof.v`: the proofs are in `Section IT`.
- Remove Array Initialization:
  + `proofs/compiler/array_init_proof.v`: the proofs are in `Section IT`.
  + `proofs/compiler/array_expansion_proof.v`: the proofs are in `Section IT`.
- Reference Arguments: `proofs/compiler/makeReferenceArguments_proof.v`: the proofs are in `Section IT`.
- Register Array Expansion: `proofs/compiler/array_expansion_proof.v`: the proofs are in `Section IT`.
- Remove Globals: `proofs/compiler/remove_globals_proof.v`: the proofs are in `Section IT`.
- Load Immediates: `proofs/compiler/load_constants_in_cond_proof.v`: the proofs are in `Section IT`.
- x86-64 Instruction Selection: `proofs/compiler/x86_lowering_proof.v`: the proofs are in `Section IT`.
- ARMv7 Instruction Selection : `proofs/compiler/arm_lowering_proof.v`: the proofs are in `Section IT`.
- RISC-V Instruction Selection: `proofs/compiler/riscv_lowering_proof.v`: the proofs are in `Section IT`.
- SLH Instruction Selection: `proofs/compiler/slh_lowering_proof.v`: the proofs are in `Section IT`.
- Inline Propagation: `proofs/compiler/inline_proof.v`: the proofs are in `Section IT`.
- Stack Allocation:
   + `proofs/compiler/stack_alloc_proof_1.v`: the proofs are in `Section IT`.
   + `proofs/compiler/stack_alloc_proof_2.v`: the proofs are in `Section IT`.
- Lower Addresses: `proofs/compiler/riscv_lower_addressing_proof.v`: the proofs are in `Section IT`.
- Register Renaming: `proofs/compiler/allocation_proof.v`: the proofs are in `Section IT`.

Back-End:
- One Varmap : `proofs/compiler/it_merge_varmaps_proof.v`
- Linearization : `proofs/compiler/it_linearization_proof.v`
- Stack Zeroization : `proofs/compiler/stack_zeroization_proof.v`: the proofs are in `Section IT`.
- Tunneling : `proofs/compiler/tunneling_proof_2.v`
- Assembly Generation : `proofs/arch/asm_gen_proof.v`: the proofs are in `Section IT`.

<!-- ------------------------------------------------------------------------------- -->
<!-- Original Readme -->
<!-- ------------------------------------------------------------------------------- -->

# Jasmin

[![pipeline status](https://gitlab.com/jasmin-lang/jasmin/badges/main/pipeline.svg)](https://gitlab.com/jasmin-lang/jasmin/-/commits/main)
[![project chat](https://readthedocs.org/projects/jasmin-lang/badge/)](https://jasmin-lang.readthedocs.org)
[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://formosa-crypto.zulipchat.com)

## About

Jasmin denotes both a language and a compiler designed for
writing high-assurance and high-speed cryptography.
Jasmin implementations aim at being efficient, safe, correct, and secure.

Reference documentation of the language and compiler are on [readthedocs](https://jasmin-lang.readthedocs.io).

## Installation

For a complete installation guide covering several use cases, please read our
[documentation](https://jasmin-lang.readthedocs.io/en/stable/misc/installation_guide.html).

If you just want to install the Jasmin tools, here is a TL;DR:

- with APT (debian, ubuntu), a package is available in a dedicated repository,
  see the [documentation](https://jasmin-lang.readthedocs.io/en/stable/misc/installation_guide.html#on-debian-and-related-linux-distributions)

- from AUR (arch linux), a package is available in the Arch User Repository,
  see the [documentation](https://jasmin-lang.readthedocs.io/en/stable/misc/installation_guide.html#on-arch-linux)

- with nix
  ```
  nix-env -iA nixpkgs.jasmin-compiler
  ```

- with opam
  ```
  opam install jasmin
  ```

## Getting support

The [Formosa-Crypto Zulip Chat](https://formosa-crypto.zulipchat.com/) is meant for anybody interested in high-assurance cryptography using EasyCrypt, Jasmin, and related tools.

## License

Jasmin is free software. All files in this distribution are, unless specified
otherwise, licensed under the [MIT license](LICENSE).
The documentation (under `docs/`) is licensed separately from the
compiler, under the [CC-BY 4.0](docs/LICENSE).
