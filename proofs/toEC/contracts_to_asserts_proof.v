(* * Correctness of the pass contracts_to_asserts.

   The transformed program, run with its assertions evaluated but its contracts
   not ([withassert_nocontract]), behaves as the source run with its contracts
   evaluated ([withassert]): same results, same failures. Each assertion added
   checks, on the same values, a condition that the semantics of the contracts
   checks at a call; the copies added write variables that the functions do
   not otherwise use ([check_contract], the freshness checks).

   The relation [wiequiv_f] only constrains the runs of its first program
   that do not fail: the two directions are stated separately. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import contracts_to_asserts.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

(* When the transformed program runs without failure, its assertions
   evaluated, the source runs with the same results, its contracts
   evaluated. *)
Axiom contracts_to_asserts_tgt_src :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state} {sm : SemMode}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
    (p p' : prog) (ev : extra_val_t),
  contracts_to_asserts_prog fresh_var_ident p = ok p' ->
  forall fn,
  wiequiv_f (wa1 := withassert_nocontract) (wa2 := withassert)
    p' p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).

(* When the source runs without failure, its contracts evaluated, the
   transformed program runs with the same results, its assertions
   evaluated. *)
Axiom contracts_to_asserts_src_tgt :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state} {sm : SemMode}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
    (p p' : prog) (ev : extra_val_t),
  contracts_to_asserts_prog fresh_var_ident p = ok p' ->
  forall fn,
  wiequiv_f (wa1 := withassert) (wa2 := withassert_nocontract)
    p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
