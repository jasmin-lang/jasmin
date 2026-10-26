(* * Correctness of the pass drop_removable.

   The pass removes the parameters and the results of the functions that are
   removable variables, and the code that computes nothing but removable
   variables. For a function [fn] of the source, [rmv_keep_params fn] and
   [rmv_keep_res fn] give the positions of its parameters and of its results
   that are kept ([keep_only]). The transformed program computes the same
   results as the source, but those removed, from the same arguments, but
   those removed: the pass checks that the removed arguments, results and
   instructions compute nothing that the rest of the program reads. This holds
   whatever [removable] tells.

   As for [dead_code] ([dead_code_total_proof]), the direction from the
   transformed program to the source needs the removed code not to fail
   ([total_ok], the well-typedness of the source), and the source to accept
   the removed arguments: they have the types of the parameters. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import dead_code drop_removable dead_code_total_proof dead_args_proof.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Section DEFS.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}.

Context (removable : var -> bool) (p : uprog).

(* The positions kept; all for a function absent from [p]. *)
Definition rmv_keep_params (fn : funname) : seq bool :=
  if rmv_params_keep removable p fn is Some k then k else [::].

Definition rmv_keep_res (fn : funname) : seq bool :=
  if rmv_res_keep removable p fn is Some k then k else [::].

Definition drop_removable_src_tgt_spec : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 => fn1 = fn2 /\ fs2 = fs_keep (rmv_keep_params fn1) fs1;
     rpostF_ := fun fn1 _ _ _ fr1 fr2 => fr2 = fs_keep (rmv_keep_res fn1) fr1 |}.

(* The arguments given to the source are those given to the transformed
   program, the removed ones being values of the types of the parameters. *)
Definition drop_removable_tgt_src_spec : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 =>
       [/\ fn1 = fn2, fs1 = fs_keep (rmv_keep_params fn1) fs2 &
           forall fd, get_fundef (p_funcs p) fn1 = Some fd ->
             is_ok (mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyin)) (fvals fs2))];
     rpostF_ := fun fn1 _ _ _ fr1 fr2 => fr1 = fs_keep (rmv_keep_res fn1) fr2 |}.

End DEFS.

(* When the source runs without failure, its assertions evaluated, the
   transformed program runs, from the arguments kept, with the same results,
   but those removed. *)
Axiom drop_removable_src_tgt :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    {sm : SemMode} {LC : LoopCounter}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    removable (p p' : uprog) (ev : extra_val_t),
  drop_removable_prog removable p = ok p' ->
  forall fn,
  wiequiv_f (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    p p' ev ev (rpreF (eS := drop_removable_src_tgt_spec removable p)) fn fn
    (rpostF (eS := drop_removable_src_tgt_spec removable p)).

(* When the transformed program runs without failure, in the total mode with
   its assertions evaluated, the source runs, from the same arguments and
   values of the types of the removed parameters, with the same results, but
   those removed. *)
Axiom drop_removable_tgt_src :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    {LC : LoopCounter}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    removable (p p' : uprog) (ev : extra_val_t),
  total_ok p ->
  drop_removable_prog removable p = ok p' ->
  forall fn,
  wiequiv_f (sm1 := total) (sm2 := total)
    (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    p' p ev ev (rpreF (eS := drop_removable_tgt_src_spec removable p)) fn fn
    (rpostF (eS := drop_removable_tgt_src_spec removable p)).
