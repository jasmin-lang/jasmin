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

Unset Printing Implicit Defensive.

(* Figure 8: Syntax of Leakages for Expressions *)
Print leakage.leak_e.

(* Figure 8: Syntax of Leakages for Instructions *)
Print leakage.leak_i.

(* Figure 9: Instrumented Semantics for Expressions *)
Print psem.sem_pexpr.

(* Figure 9: Instrumented Semantics for Instruction *)
Print psem.sem.

(* Figure 10: Leakage Transformers for Expressions *)
Print leakage.leak_e_tr.

(* Figure 10: Leakage Transformers for Instructions *)
Print leakage.leak_i_tr.

(* Figure 11: Semantics for Expressions' Leakage Transformers *)
Print leakage.leak_E.

(* Figure 11: Semantics for Instructions' Leakage Transformers *)
Print leakage.leak_I.

(* Theorem 4.1: Leakages' Transformer Correctness *)
Check compiler_proof.compile_prog_to_x86P.

(* Definition 5.1: Definition for Constant-Time for Source level *)
Print compiler_proof.constant_time.

(* Definition 5.1: Definition for Constant-Time for Target level *)
Print compiler_proof.x86_constant_time.

(* Definition 5.2: Indistinguishability of target states *)
Print compiler_proof.lift_spred_x86_pred.

(* Theorem 5.3: CCT-Preservation *)
Check compiler_proof.x86_CT.

(* Definition 5.4: Cost *)
Print cost.cost_i.

(* Definition 5.5: Cost Transformer *)
Print cost.transform_cost_I.

(* Section 5.2 *)
Check cost.transform_cost_ok.


