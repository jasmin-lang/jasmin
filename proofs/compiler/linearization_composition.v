(* ** Imports and settings *)
From ITree Require Import
  ITree
  ITreeFacts
  Basics.HeterogeneousRelations
  Interp.Recursion
  Eq.Rutt
  Eq.RuttFacts.

From Coq
Require Import Setoid Morphisms Lia.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From Coq Require Import ZArith Utf8.
Import Relations.

Require sem_one_varmap_facts label.
Import word_ssrZ.
Import ssrring.
Import psem psem_facts sem_one_varmap compiler_util label sem_one_varmap_facts low_memory.
Require Import seq_extra.
Require Import constant_prop.
Require Import fexpr fexpr_sem fexpr_facts.
Require Export linearization linear_sem linear_facts.
Require Import core_logics relational_logic it_sems_core.
Require Import sem_params.
Import Memory.

Require Import linearization_proof.
Require Import it_linearization_proof.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

#[local] Existing Instance withsubword.
#[local] Opaque eval_jump.

Section WITH_PARAMS.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}.

Section LINEARIZATION_PARAMS.

Context
  (liparams : linearization_params)
  (hliparams : h_linearization_params liparams).

  Section IT.

    Context
      {E E0 : Type -> Type}
      {wE : with_Error E E0}
      {rE0 : EventRels E0}
      {rE : RndEvent syscall_state -< E}.

    Definition lget_vars (xs : seq var_i) (vm : Vm.t) : seq value :=
      [seq vm.[v_var x] | x <- xs].
    Definition lget_args (lfd : lfundef) := lget_vars lfd.(lfd_arg).
    Definition lget_res  (lfd : lfundef) := lget_vars lfd.(lfd_res).

    Context
      (p : sprog)
      (p' : lprog)
      (gd : pointer)
    .

    Let pre (fd : sfundef) (lfd : lfundef) (s : fstate) (t : estate) : Prop :=
      let: args := s.(fvals) in
      let: ms := s.(fmem) in
      let: vmt := t.(evm) in
      let: argt := lget_args lfd vmt in
      let: mt := t.(emem) in
      [/\ vmt.[vid (lp_rsp p')] = Vword (top_stack ms)
        , match_mem ms mt
        , List.Forall2 value_uincl args argt (* TODO varmap will take an estate isntead of fstate, update *)
        , vmt.[vid (lp_rip p')] = Vword gd
        , vm_initialized_on vmt lfd.(lfd_callee_saved)
        , s.(fscs) = t.(escs)
        , (fd.(f_extra).(sf_stk_max)
            + wsize_size fd.(f_extra).(sf_align) - 1
            <= wunsigned (top_stack ms))%Z
        & allocatable_stack ms
            (fd.(f_extra).(sf_stk_max)
              + wsize_size fd.(f_extra).(sf_align) - 1)
        ].

    Let post (fd : sfundef) (lfd : lfundef) (s : fstate) (t : estate) (s' : fstate) (t' : estate) : Prop :=
      let: ms := s.(fmem) in
      let: mt := t.(emem) in
      let: ress := s'.(fvals) in
      let: ms' := s'.(fmem) in
      let: vmt' := t'.(evm) in
      let: rest := lget_res lfd vmt' in
      let: mt' := t'.(emem) in
      [/\ vmt'.[vid (lp_rsp p')] = Vword (top_stack ms)
        , match_mem ms' mt'
        , target_mem_unchanged
            ms (align_top_stack (top_stack ms) fd.(f_extra))
            fd.(f_extra).(sf_stk_max) mt mt'
        , List.Forall2 value_uincl ress rest
        , s'.(fscs) = t'.(escs)
        , stack_stable ms ms'
        & allocatable_stack ms
            (fd.(f_extra).(sf_stk_max)
              + wsize_size fd.(f_extra).(sf_align) - 1)
        ].

    Lemma it_linear_exportcallP {fn} :
      exists fd lfd,
        [/\ get_fundef p.(p_funcs) fn = Some fd
          , get_fundef p'.(lp_funcs) fn = Some lfd
          , lfd.(lfd_export)
          & wkequiv_io (pre fd lfd)
              (isem_fun
                 (asm_op := asm_op) (wsw := withsubword) (dc := direct_c)
                 (ep := ep) (spp := spp) (wa := noassert) (sip := sip)
                 (pT := progStack) (scP := sCP_stack)
                 (E := E)
                 p gd fn)
              (ilsem_exportcall p' fn)
              (post fd lfd)
        ].
    Proof. Admitted.
    (* Follows from:
       - linear_exportcallP
       - merge_varmaps_export_call_checkP
       - mix_ilsem_ilsem *)

  End IT.

End LINEARIZATION_PARAMS.

End WITH_PARAMS.
