From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From mathcomp Require Import fintype finfun ssralg.
From ITree Require Import
  Basics
  ITree
  ITreeFacts
.

Require Import
  arch_params_proof
  compiler
  compiler_util
  psem
  psem_facts
  relational_logic
  sem_one_varmap
.
Require Import
  stack_zeroization_proof
  stack_alloc_proof_2
  tunneling_proof
  tunneling_proof_2
  linearization_proof
  merge_varmaps_proof
  psem_of_sem_proof
.

Require Import
  compiler_proof
  it_compiler_proof
.

Require Import
  arch_decl
  arch_extra
  arch_sem
  asm_gen_proof
  sem_params_of_arch_extra
.

Section IT.

Context
  {reg regx xreg rflag cond asm_op extra_op syscall_state : Type}
  {sc_sem : syscall.syscall_sem syscall_state}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {call_conv : calling_convention}
  {asm_scsem : asm_syscall_sem}
  {lowering_options : Type}
  (aparams : architecture_params lowering_options)
  (haparams : h_architecture_params aparams)
  (cparams : compiler_params lowering_options)
  (print_uprogP : forall s p, cparams.(print_uprog) s p = p)
  (print_sprogP : forall s p, cparams.(print_sprog) s p = p)
  (print_linearP : forall s p, cparams.(print_linear) s p = p)
.

Notation E := (ErrEvent +' RndEvent syscall_state) (only parsing).
Notation E0 := (RndEvent syscall_state) (only parsing).

#[local] Existing Instance wE.
#[local] Existing Instance HandlerContract.
#[local] Existing Instance RndE00.
#[local] Existing Instance RndE0Refl.
#[local] Existing Instance HandlerContract_trans.


Section FULL.

Context
  (entries : seq funname)
  (up : uprog (asmop := _asmop))
  (xp : asm_prog)
.

Definition zeroized_u fn args argt ms mt mt' :=
  cparams.(stack_zero_info) fn <> None ->
  forall p,
    Forall3
      (disjoint_from_writable_param (ep := ep_of_asm_e) p)
      (get_wptrs up fn)
      args argt ->
    zeroized_p ms mt mt' p.

Definition wf_args_x rip fn ms mi args argt :=
  let n := Z.of_nat (size (asm_globs xp)) in
  let ws := get_wptrs up fn in
  let al := get_asm_align_args xp fn in
  wf_args n rip ms mi ws al args argt.

Let pre fn xfd s t :=
  let: args := s.(fvals) in
  let: ms := s.(fmem) in
  let: rm := t.(asm_reg) in
  let: argt := get_typed_reg_values t xfd.(asm_fd_arg) in
  let: mt := t.(asm_mem) in
  exists mi,
    [/\ mem_agreement_with_ghost ms mt t.(asm_rip) xp.(asm_globs) mi
      , enough_stack_space xp fn (top_stack ms) mt
      , t.(asm_scs) = s.(fscs)
      , rm ad_rsp = top_stack ms
      , wf_args_x t.(asm_rip) fn ms mi args argt
      & Forall3 (value_uincl_or_in_mem mt) (get_wptrs up fn) args argt
    ].

(* TODO why [t'.(asm_rip)] and not from [t]? *)

Let post fn xfd s t s' t' :=
  let: args := s.(fvals) in
  let: ms := s.(fmem) in
  let: argt := get_typed_reg_values t xfd.(asm_fd_arg) in
  let: mt := t.(asm_mem) in
  let: ress := s'.(fvals) in
  let: ms' := s'.(fmem) in
  let: rest := get_typed_reg_values t' xfd.(asm_fd_res) in
  let: mt' := t'.(asm_mem) in
  let: n := get_nb_wptr up fn in
  [/\ mem_agreement ms' mt' t'.(asm_rip) xp.(asm_globs)
    , t'.(asm_scs) = s'.(fscs)
    , zeroized_u fn args argt ms mt mt'
    , List.Forall2 (value_in_mem mt') (take n ress) (take n argt)
    & values_uincl (drop n ress) rest
  ].

Lemma it_compile_prog_to_asmP {fn} :
  compile_prog_to_asm aparams cparams entries up = ok xp ->
  fn \in entries ->
  exists xfd,
    [/\ get_fundef xp.(asm_funcs) fn = Some xfd
      , xfd.(asm_fd_export)
      & wkequiv_io
          (pre fn xfd)
          (isem_unit up fn)
          (iasmsem_exportcall xp fn)
          (post fn xfd)
   ].
Proof.
rewrite /compile_prog_to_asm; t_xrbindP => sp ok_sp ok_xp ok_fn.
(* Extract xfd independently of rip. print_linearP is needed by the lemma. *)
have [_ [xfd [_ get_xfd xfd_export _]]] :=
  compiler_back_end_to_asm_get_fundef print_linearP ok_xp ok_fn.
exists xfd; split => //.
(* Unfold wkequiv_io: fix a source state fs and asm state xm. *)
move=> fs xm hpre.
(* FE: haparams is explicit; entries/up/sp/rip/fn inferred from ok_sp/ok_fn.
   Returns forall (rip : pointer) (ev : extra_val_t), wiequiv_f up sp ev rip rpreF fn fn rpostF. *)
have FE := it_compiler_front_endP haparams print_uprogP print_sprogP ok_sp ok_fn.
(* BE: all section vars must be explicit; rip = asm_rip xm. *)
have [xfd2 [get_xfd2 _ BE]] :=
  it_compiler_back_end_to_asmP haparams print_linearP (asm_rip xm) ok_xp ok_fn.
(* Identify xfd2 = xfd via get_fundef determinism. *)
have heq_xfd : xfd2 = xfd by move: get_xfd2; rewrite get_xfd => [[->]].
subst xfd2.
(* Proof plan (all admits):
   1. Build intermediate sp-level fstate fs_sp:
        hFE_pre : rpreF fn fn fs fs_sp  (FE.pre fn fn)
        hBE_pre : [/\ asm_reg xm ad_rsp = top_stack (fmem fs_sp),
                       asm_rip xm = asm_rip xm, values_uincl ...,
                       match_mem ..., fscs fs_sp = asm_scs xm &
                       allocatable_stack (fmem fs_sp) xfd.fd_total_stack]
   2. FE (asm_rip xm) tt fs fs_sp hFE_pre :
        xrutt EE NoCut_ EPreRel EPostRel (rpostF fn fn fs fs_sp)
              (isem_unit up fn fs) (isem_stack sp (asm_rip xm) fn fs_sp)
   3. BE fs_sp xm hBE_pre :
        xrutt EE EE EPreRel EPostRel (BE.post fn xfd fs_sp xm)
              (isem_stack sp (asm_rip xm) fn fs_sp) (iasmsem_exportcall xp fn xm)
   4. xrutt_trans + xrutt_weaken_v1 → FULL.post. *)
Admitted.

End FULL.

End IT.
