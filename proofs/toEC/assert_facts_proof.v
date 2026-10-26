(* * Correctness of the pass assert_facts.

   The pass removes from the assertions the conjuncts that an assertion
   evaluated earlier on every path establishes, nothing it reads having
   changed since; the rest of the code is unchanged. A removed conjunct holds
   where it is, on the same state.

   The relation [wiequiv_f] only constrains the runs of its first program that
   do not fail: the statement is that of the direction needed, from the
   transformed program to the source. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import assert_facts.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

(* When the transformed program runs without failure, in the mode
   [total_init] (the pass runs after [explicit_init]) with its assertions
   evaluated, the source runs with the same results. *)
Axiom assert_facts_tgt_src :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (p : prog) (ev : extra_val_t),
  forall fn,
  wiequiv_f (sm1 := total_init) (sm2 := total_init)
    (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    (assert_facts_prog p) p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
