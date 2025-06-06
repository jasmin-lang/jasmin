# About Jasmin

Jasmin is a workbench for high-assurance and high-speed cryptography.
Jasmin implementations aim at being efficient, safe, correct, and secure.

The Jasmin **programming language** smoothly combines high-level and low-level constructs,
so as to support “assembly in the head” programming.
Programmers can control many low-level details that are performance-critical: instruction selection and scheduling, what registers to spill and when, etc.
They can also rely on high-level abstractions (variables, functions, arrays, loops, etc.) to structure their code and make it more amenable to formal verification.

The **semantics** is formally defined to allow rigorous reasoning about program behaviors.
The Coq definitions can be found in the `proofs/lang/sem.v` file.
This semantics is executable, thus Jasmin programs can be directly [interpreted](tools/reference_interpreter).

Jasmin programs can be automatically checked for **safety** and **termination** (using a trusted [static analyzer](tools/safety_checker)).

The Jasmin **compiler** produces predictable assembly and ensures that the use of high-level abstractions incurs no run-time penalty.
It is formally verified for correctness (the precise Coq statement and the corresponding machine-checked proofs can be found in the `proofs/compiler/compiler_proof.v` file).
This justifies that many properties can be proved on a source program and still apply to the corresponding assembly program: safety, termination, functional correctness…

The Jasmin workbench leverages the [EasyCrypt](https://www.easycrypt.info/) toolset for **formal verification**. Jasmin programs can be [extracted](tools/jasmin2ec) to corresponding EasyCrypt programs to prove functional correctness, cryptographic security, or security against side-channel attacks (constant-time).
