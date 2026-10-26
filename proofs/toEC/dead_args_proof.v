(* * Correctness of the pass dead_args.

   The pass removes dead code, the parameters that a body does not read and
   the results that no caller uses. [dead_args_info] gives, for each function
   of the source, the positions of its parameters and of its results that are
   kept ([keep_only]). The transformed program computes the same results as
   the source, but those removed, from the same arguments, but those removed:
   the removed arguments are not read, and the removed results are not used.

   As for [dead_code] ([dead_code_total_proof]), the direction from the
   transformed program to the source needs the removed instructions not to
   fail ([total_ok]), and the source to accept the removed arguments: they
   have the types of the parameters. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import compiler_util psem psem_facts.
Require Import dead_code dead_args dead_code_total_proof.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Section DEFS.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}.

Context (info : keep_info).

(* The positions kept; all for a function absent from [info]. *)
Definition kparams (fn : funname) : seq bool :=
  if get_fundef info fn is Some k then k.1 else [::].

Definition kres (fn : funname) : seq bool :=
  if get_fundef info fn is Some k then k.2 else [::].

Definition fs_keep (k : seq bool) (fs : fstate) : fstate :=
  {| fscs := fscs fs; fmem := fmem fs; fvals := keep_only (fvals fs) k |}.

Definition dead_args_src_tgt_spec : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 => fn1 = fn2 /\ fs2 = fs_keep (kparams fn1) fs1;
     rpostF_ := fun fn1 _ _ _ fr1 fr2 => fr2 = fs_keep (kres fn1) fr1 |}.

(* The arguments given to the source are those given to the transformed
   program, the removed ones being values of the types of the parameters. *)
Definition dead_args_tgt_src_spec (p : uprog) : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 =>
       [/\ fn1 = fn2, fs1 = fs_keep (kparams fn1) fs2 &
           forall fd, get_fundef (p_funcs p) fn1 = Some fd ->
             is_ok (mapM2 ErrType dc_truncate_val (map eval_atype fd.(f_tyin)) (fvals fs2))];
     rpostF_ := fun fn1 _ _ _ fr1 fr2 => fr1 = fs_keep (kres fn1) fr2 |}.

End DEFS.

(* When the source runs without failure, its assertions evaluated, the
   transformed program runs, from the arguments kept, with the same results,
   but those removed. *)
Axiom dead_args_src_tgt :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    {sm : SemMode} {LC : LoopCounter}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    protect dead_info (p p' : uprog) info (ev : extra_val_t),
  dead_args_info protect dead_info p = ok (p', info) ->
  forall fn,
  wiequiv_f (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    p p' ev ev (rpreF (eS := dead_args_src_tgt_spec info)) fn fn
    (rpostF (eS := dead_args_src_tgt_spec info)).

(* When the transformed program runs without failure, in the mode
   [total_init] (the pass runs after [explicit_init]) with its assertions
   evaluated, the source runs, from the same arguments and values of the
   types of the removed parameters, with the same results, but those removed.
   [total_ok] is stated in the mode [total]: the two modes fail alike, but
   for a write of an output that [total] leaves undefined and [total_init]
   defines, which fails in [total] only. *)
Axiom dead_args_tgt_src :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    {LC : LoopCounter}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    protect dead_info (p p' : uprog) info (ev : extra_val_t),
  total_ok p ->
  dead_args_info protect dead_info p = ok (p', info) ->
  forall fn,
  wiequiv_f (sm1 := total_init) (sm2 := total_init)
    (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    p' p ev ev (rpreF (eS := dead_args_tgt_src_spec info p)) fn fn
    (rpostF (eS := dead_args_tgt_src_spec info p)).
