(* * Correctness of the pass drop_asserts.

   The pass removes the assertions, nothing else. On a run of the source in
   which every assertion holds, the program without them does the same
   computation.

   "The source runs without failure" is the hypothesis built in [wiequiv_f]:
   the relation constrains only the runs of its first program that do not
   fail, the source here, run with its assertions evaluated and its contracts
   not ([withassert_nocontract]): an assertion that does not hold is a
   failure. On each such run, from the same function, arguments, memory and
   system state, the transformed program runs with the same events and ends
   with the same results, memory and system state. The transformed program has
   no assertion: its semantics is the same with [withassert_nocontract] and
   with [noassert]. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import drop_asserts.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Axiom drop_asserts_src_tgt :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state} {sm : SemMode}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (p : uprog) (ev : extra_val_t),
  forall fn,
  wiequiv_f (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    p (drop_asserts_prog p) ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
