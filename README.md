This is a copy of the Jasmin project extend with the work corresponding
to the paper "KEM-IND-CCA-Preserving Compilation of Jasmin ML-KEM."


# Download, installation, and sanity-testing instructions

Detail instruction are available at
[link](https://github.com/jasmin-lang/jasmin/wiki/Installation-instructions)

## Dependencies

This formalization has been developed with the tools listed in the opam
file (located at the root of the project).

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

First add the Coq repository to the current opam switch
```
opam repo add coq-released https://coq.inria.fr/opam/released
```
then do
```
opam update
```
and install the dependencies listed in the opam file.


## Build

To run Coq and check the validity of the proofs, run in the `proof` directory:
```
make
```
This verifies all Coq files.

Alternatively, to compile the full compiler, run in the root of the project:
```
make
```

# List of claims in the paper supported by this artifact

## Admitted lemmas

As stated in the paper, we admit one lemma about the connection between the
Linearization and One Varmap passes: this is in
`proofs/compiler/linearization_composition.v` (`it_linear_exportcallP`).
The statement is the combination of the correctness of linearization
(`linear_exportcallP`, proven in `proofs/compiler/it_linearization_proof.v`),
the correctness of one varmap (`merge_varmaps_export_call_checkP`, prove in
`proofs/compiler/it_merge_varmaps_proof.v`), and `mix_ilsem_ilsem` (proven in
`proofs/compiler/linear_sem.v`).

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

## Relational Hoare Logic

The implementation of the logic is in `proofs/lang/relational_logic.v`.
Equivalence up-to-cutoff is defined as `xrutt` in `proofs/itrees/xrutt.v`.

 + rule SKIP in the paper corresponds to lemmas
 `wequiv_nil` in `/proof/lang/relational_logic.v`.
 + rule SEQ in the paper corresponds to lemmas
 `wequiv_cons` in `/proof/lang/relational_logic.v`.
 + rule ASSIGN in the paper corresponds to lemmas
 `wequiv_assgn` in `/proof/lang/relational_logic.v`.
 + rule COND in the paper corresponds to lemmas
 `wequiv_if` in `/proof/lang/relational_logic.v`.
 + rule LOOP in the paper corresponds to lemmas
 `wequiv_while` in `/proof/lang/relational_logic.v`.
 + rule RAND in the paper corresponds to lemmas
  `wequiv_syscall` in `/proof/lang/relational_logic.v`.
 + rule CALL in the paper corresponds to lemmas
 `wequiv_call` in `/proof/lang/relational_logic.v`.
 + rule CONSEQ is inlined in each rule.
 + rule TRANS in the paper corresponds to lemmas
 `wequiv_trans` in `/proof/lang/relational_logic.v`.
 + rule REC is `wequiv_fun_ind`

## Compiler Passes and Proofs

Front-End:
- Int Word: `proofs/compiler/wint_word_proof.v`: the proofs are in `Section IT`.
- Array Copy: `proofs/compiler/array_copy_proof.v`: the proofs are in `Section IT`.
- Array Initialization: `proofs/compiler/array_init_proof.v`: the proofs are in `Section IT`.
- Spilling: `proofs/compiler/lower_spill_proof.v`: the proofs are in `Section IT`.
- Inlining: `proofs/compiler/inline_proof.v`: the proofs are in `Section IT`.
- Function Pruning: `proofs/compiler/dead_calls_proof.v`: the proofs are in `Section IT`.
- Constant Propagation: `proofs/compiler/const_prop_proof.v`: the proofs are in `Section IT`.
- Dead Code Elimination: `proofs/compiler/dead_code_prooof.v`: the proofs are in `Section IT`.
- Unrolling: `proofs/compiler/unrolling_proof.v`: the proofs are in `Section IT`.
- Remove Array Initialization:
  + `proofs/compiler/array_init_proof`: the proofs are in `Section IT`.
  + `proofs/compiler/array_expansion_proof`: the proofs are in `Section IT`.
- Reference Arguments: `proofs/compiler/makeReferenceArguments_proof.v`: the proofs are in `Section IT`.
- Register Array Expansion: `proofs/compiler/array_expansion_proof.v`: the proofs are in `Section IT`.
- Remove Globals: `proofs/compiler/remove_globals_proof.v`: the proofs are in `Section IT`.
- Load Immediates: `proofs/compiler/load_constant_in_cond.v`: the proofs are in `Section IT`.
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
- One Varmap : `prood/compiler/it_merge_varmap_proof.v`
- Linearization : `proofs/compiler/it_linearization_proofs.v`
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
