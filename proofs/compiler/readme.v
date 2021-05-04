(* This is the formal development corresponding to submission #NNN to CCS 2021.
It is derived form the Jasmin compiler publicly available at https://github.com/jasmin-lang/jasmin/ under the CeCILL-B license.

This file recalls the main definitions and theorems.
*)
From mathcomp Require Import all_ssreflect all_algebra.
Require compiler_proof.
Import Utf8.
Import sem psem x86_sem.
Import compiler compiler_util x86_gen.
Import cost.

(* Figure 9 *)
Print leakage.leak_e.

(* Theorem 4.1: Leakages' Transformer Correctness *)
Check compiler_proof.compile_prog_to_x86P.
