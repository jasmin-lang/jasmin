(* * Correctness of the pass simplify_asserts.

   The pass rewrites the assertions only, with facts that hold on every path
   that reaches them (constants, full masks, copies of arrays); a rewritten
   assertion that holds implies the original one, on the same state. The rest
   of the code is unchanged. The facts rely on a total mode: a write out of
   the bounds of an array leaves it unchanged, which keeps a full mask full.
   The pass runs after [explicit_init], on programs whose semantics is the
   mode [total_init].

   The relation [wiequiv_f] only constrains the runs of its first program that
   do not fail: the statement is that of the direction needed, from the
   transformed program to the source. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import simplify_asserts.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

(* When the transformed program runs without failure, in the mode
   [total_init] with its assertions evaluated, the source runs with the same
   results. *)
Axiom simplify_asserts_tgt_src :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (p : prog) (ev : extra_val_t),
  forall fn,
  wiequiv_f (sm1 := total_init) (sm2 := total_init)
    (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    (simplify_asserts_prog p) p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
