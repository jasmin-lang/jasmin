From Coq Require Import Uint63.
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
.
Require Import
  allocation_proof
  lower_spill_proof
  load_constants_in_cond_proof
  inline_proof
  dead_calls_proof
  makeReferenceArguments_proof
  array_copy
  array_copy_proof
  array_init_proof
  unrolling_proof
  constant_prop_proof
  propagate_inline_proof
  dead_code_proof
  array_expansion
  array_expansion_proof
  remove_globals_proof
  stack_alloc_proof_2
  tunneling_proof
  linearization_proof
  merge_varmaps_proof
  psem_of_sem_proof
  slh_lowering_proof
  direct_call_proof
  stack_zeroization_proof
  wint_word_proof
  compiler_proof
.

Require Import
  arch_decl
  arch_extra
  arch_sem
  asm_gen_proof
  sem_params_of_arch_extra.

Instance eq_uincl_spec
  {syscall_state asm_op : Type}
  {ep : EstateParams syscall_state}
  {sip : SemInstrParams asm_op syscall_state}
  : EquivSpec :=
  {|
    rpreF_ := pre_eq;
    rpostF_ := post_incl;
  |}.

Section MOVE.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {asm_op : Type}
  {sip : SemInstrParams asm_op syscall_state}
  {fn1 fn2 fn3 : funname}
.

Lemma rpreF_trans_eq_eq_eq fs1 fs3 :
  pre_eq fn1 fn2 fs1 fs3 ->
  exists2 fs2,
    pre_eq fn1 fn2 fs1 fs2
    & pre_eq fn1 fn2 fs2 fs3.
Proof. move=> [<- <-]; by exists fs1. Qed.

Lemma rpreF_trans_eq_uincl_eq fs1 fs3 :
  pre_eq fn1 fn2 fs1 fs3 ->
  exists2 fs2,
    pre_incl fn1 fn2 fs1 fs2
    & pre_eq fn1 fn2 fs2 fs3.
Proof. move=> [<- <-]; exists fs1; split=> //; exact: fs_uinclR. Qed.

Lemma rpreF_trans_uincl_uincl_uincl fs1 fs3 :
  pre_incl fn1 fn2 fs1 fs3 ->
  exists2 fs2,
    pre_incl fn1 fn2 fs1 fs2
    & pre_incl fn1 fn2 fs2 fs3.
Proof. move=> [<- ?]; exists fs1; split=> //; exact: fs_uinclR. Qed.

Lemma rpostF_trans_eq_eq_eq_uincl fs1 fs2 fs3 r1 r3 :
  pre_eq fn1 fn2 fs1 fs2 ->
  pre_eq fn2 fn3 fs2 fs3 ->
  rcompose
    (post_eq fn1 fn2 fs1 fs2)
    (post_incl fn2 fn3 fs2 fs3)
    r1 r3 ->
  post_incl fn1 fn3 fs1 fs3 r1 r3.
Proof. by move=> [<- h1] [<- <-] [] _ <-. Qed.

Lemma rpostF_trans_uincl_uincl_uincl_uincl fs1 fs2 fs3 r1 r3 :
  pre_incl fn1 fn2 fs1 fs2 ->
  pre_incl fn2 fn3 fs2 fs3 ->
  rcompose
    (post_incl fn1 fn2 fs1 fs2)
    (post_incl fn2 fn3 fs2 fs3)
    r1 r3 ->
  post_incl fn1 fn3 fs1 fs3 r1 r3.
Proof.
move=> [<- h1] [<- h2] [] r2 [?? hvals1] [?? hvals2]; split.
1-2: congruence. exact: values_uincl_trans hvals1 hvals2.
Qed.

Lemma rpostF_trans_eq_eq_uincl_uincl fs1 fs2 fs3 r1 r3 :
  pre_eq fn1 fn2 fs1 fs2 ->
  pre_eq fn2 fn3 fs2 fs3 ->
  rcompose
    (post_incl fn1 fn2 fs1 fs2)
    (post_incl fn2 fn3 fs2 fs3)
    r1 r3 ->
  post_incl fn1 fn3 fs1 fs3 r1 r3.
Proof.
move=> [<- _] [<- <-] [] {}fs3 [?? hvals1] [?? hvals2]; split.
1-2: congruence. exact: values_uincl_trans hvals1 hvals2.
Qed.

Lemma rpostF_trans_uincl_eq_uincl_uincl fs1 fs2 fs3 r1 r3 :
  pre_incl fn1 fn2 fs1 fs2 ->
  pre_eq fn2 fn3 fs2 fs3 ->
  rcompose
    (post_incl fn1 fn2 fs1 fs2)
    (post_incl fn2 fn3 fs2 fs3)
    r1 r3 ->
  post_incl fn1 fn3 fs1 fs3 r1 r3.
Proof.
move=> [<- _] [<- <-] [] {}fs3 [?? hvals1] [?? hvals2]; split.
1-2: congruence. exact: values_uincl_trans hvals1 hvals2.
Qed.

Lemma rpostF_trans_eq_uincl_eq_uincl fs1 fs2 fs3 r1 r3 :
  pre_eq fn1 fn2 fs1 fs2 ->
  pre_incl fn2 fn3 fs2 fs3 ->
  rcompose
    (post_eq fn1 fn2 fs1 fs2)
    (post_incl fn2 fn3 fs2 fs3)
    r1 r3 ->
  post_incl fn1 fn3 fs1 fs3 r1 r3.
Proof. by move=> [<- _] [<- [?? hvals1]] [] _ <- [?? hvals2]. Qed.

End MOVE.

Section MOVE.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {asm_op : Type}
  {sip : SemInstrParams asm_op syscall_state}
  {pT1 pT2 pT3 : progT}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {wsw1 wsw2 wsw3 : WithSubWord}
  {scP1 : semCallParams (wsw := wsw1) (pT := pT1)}
  {scP2 : semCallParams (wsw := wsw2) (pT := pT2)}
  {scP3 : semCallParams (wsw := wsw3) (pT := pT3)}
  {dc1 dc2 dc3 : DirectCall}
  {rE12 : EventRels E0} {rE23 : EventRels E0} {rE13 : EventRels E0}
  {sem_F1 : sem_Fun (sip := sip) (pT := pT1) E}
  {sem_F2 : sem_Fun (sip := sip) (pT := pT2) E}
  {sem_F3 : sem_Fun (sip := sip) (pT := pT3) E}
  {rE_trans : EventRels_trans rE12 rE23 rE13}
.

Notation prog1 := (prog (pT := pT1)).
Notation prog2 := (prog (pT := pT2)).
Notation prog3 := (prog (pT := pT3)).

Context
  {p1 : prog1} {p2 : prog2} {p3 : prog3}
  {ev1 : extra_val_t (progT := pT1)}
  {ev2 : extra_val_t (progT := pT2)}
  {ev3 : extra_val_t (progT := pT3)}
  {fn : funname}
.

Let wiequiv_f_trans' :=
  wiequiv_f_trans
    (wsw1 := wsw1) (wsw2 := wsw2) (wsw3 := wsw3)
    (scP1 := scP1) (scP2 := scP2) (scP3 := scP3)
    (dc1 := dc1) (dc2 := dc2) (dc3 := dc3)
    (p1 := p1) (p2 := p2) (p3 := p3)
    (ev1 := ev1) (ev2 := ev2) (ev3 := ev3)
    (fn1 := fn) (fn2 := fn) (fn3 := fn).

(* X -> wequiv eq uincl -> wequiv eq uincl *)
Let wiequiv_f_trans_X_EU {rpreF rpostF} :=
  wiequiv_f_trans'
    (rpreF12 := rpreF) (rpreF23 := pre_eq) (rpreF13 := pre_eq)
    (rpostF12 := rpostF) (rpostF23 := post_incl) (rpostF13 := post_incl).

(* wequiv eq eq -> wequiv eq uincl -> wequiv eq uincl *)
Definition wiequiv_f_trans_EE_EU :=
  wiequiv_f_trans_X_EU rpreF_trans_eq_eq_eq rpostF_trans_eq_eq_eq_uincl.

(* wequiv eq eq -> wequiv eq uincl -> wequiv eq uincl *)
Definition wiequiv_f_trans_EU_EU :=
  wiequiv_f_trans_X_EU rpreF_trans_eq_eq_eq rpostF_trans_eq_eq_uincl_uincl.

(* wequiv uincl uincl -> wequiv eq uincl -> wequiv eq uincl *)
Definition wiequiv_f_trans_UU_EU :=
  wiequiv_f_trans_X_EU
    rpreF_trans_eq_uincl_eq rpostF_trans_uincl_eq_uincl_uincl.

(* wequiv uincl uincl -> wequiv uincl uincl -> wequiv uincl uincl *)
Definition wiequiv_f_trans_UU_UU :=
  wiequiv_f_trans'
    rpreF_trans_uincl_uincl_uincl
    rpostF_trans_uincl_uincl_uincl_uincl.

End MOVE.

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
.

Definition of_void1 {A T} (e : void1 A) : T := match e with end.
Definition of_void_sum {E} : E +' void1 ~> E :=
  fun _ x => match x with inl1 a => a | inr1 e => of_void1 e end.

#[local]
Instance with_Error0 : with_Error ErrEvent void1 :=
  {|
    mfun1 := inl1;
    mfun2 := of_void_sum;
    mid12 := fun _ e =>
      match e with inl1 e => refl_equal | inr1 a => of_void1 a end;
    mid21 := fun _ _ => refl_equal;
  |}.

#[local]
Instance HandlerContract : EventRels void1 :=
  {|
    EPreRel0_ := fun _ _ _ _ => False;
    EPostRel0_ := fun _ _ _ _ _ _ => True;
  |}.

#[local]
Instance HandlerContract_trans {rE23 rE13} :
  EventRels_trans HandlerContract rE23 rE13 :=
  {|
    ERpre_trans := fun _ _ _ e => of_void1 e;
    ERpost_trans := fun _ _ _ e => of_void1 e;
  |}.

Section FIRST_PART.

#[local] Existing Instance withsubword.
#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.

Lemma it_inliningP {to_keep p p' ev fn} :
  fn \in to_keep ->
  inlining cparams to_keep p = ok p' ->
  wiequiv_f (dc1 := indirect_c) (dc2 := indirect_c)
    p p' ev ev pre_incl fn fn post_incl.
Proof.
rewrite /inlining; t_xrbindP=> hfn p0 hp0 p1.
rewrite !print_uprogP => hp1 ?; subst p'.
apply: wiequiv_f_trans_UU_UU; first exact: it_inline_call_errP hp0.
apply: it_sem_refl_EE_UU; exact: (it_dead_calls_err_seqP hp1 _ hfn).
Qed.

Lemma it_postprocessP {dc : DirectCall} (p p' : uprog) fn ev :
  dead_code_prog (ap_is_move_op aparams) (const_prop_prog p) false = ok p' ->
  wiequiv_f (dc1 := dc) (dc2 := dc)
    p p' ev ev pre_incl fn fn post_incl.
Proof.
move=> hp'.
apply: wiequiv_f_trans_UU_UU; first exact: it_const_prop_callP.
apply: it_sem_refl_EU_UU.
exact: (it_dead_code_callPu (hap_is_move_opP haparams) ev hp' (fn := fn)).
Qed.

Lemma it_unrollP {dc : DirectCall} (fn : funname) (p p' : prog) ev :
  unroll_loop (ap_is_move_op aparams) p = ok p' ->
  wiequiv_f (dc1 := dc) (dc2 := dc)
    p p' ev ev pre_incl fn fn post_incl.
Proof.
rewrite /unroll_loop; t_xrbindP; elim: Loop.nb p => [// | n hind] /= p pu hpu.
case hu: unroll_prog => [pu' []]; last first.
- move=> [<-]; exact: it_postprocessP hpu.
move: hu; rewrite (surjective_pairing (unroll_prog pu)) => -[? _]; subst pu'.
t_xrbindP=> p0 hp0 hp'.
apply: wiequiv_f_trans_UU_UU; last exact: hind hp0 hp'.
apply: wiequiv_f_trans_UU_UU; first exact: it_postprocessP hpu.
apply: it_sem_refl_EE_UU; exact: it_unroll_callP.
Qed.

Lemma it_live_range_splittingP {dc : DirectCall} (p p': uprog) fn ev :
  live_range_splitting aparams cparams p = ok p' ->
  wiequiv_f (dc1 := dc) (dc2 := dc)
    p p' ev ev pre_eq fn fn post_incl.
Proof.
rewrite /live_range_splitting; t_xrbindP.
rewrite !print_uprogP => ok_p' pa ok_pa; rewrite print_uprogP => ?; subst pa.
move: p ok_p' ok_pa => [fs gd ep] /= ok_p' ok_pa.
apply: wiequiv_f_trans_UU_EU; first exact: (it_alloc_call_uprogP _ _ ok_p').
apply: (
  wkequiv_io_weaken
    (P := pre_incl fn fn)
    (Q := post_incl fn fn)
) => //.
- move=> ? _ [_ <-]; split=> //; split=> //; exact: values_uincl_refl.
apply: it_sem_refl_EU_UU.
exact: (it_dead_code_callPu (hap_is_move_opP haparams) ev ok_pa (fn := fn)).
Qed.

Lemma it_compiler_first_part {entries p p' ev fn} :
  compiler_first_part aparams cparams entries p = ok p' ->
  fn \in entries ->
  wiequiv_f
    (wsw1 := nosubword) (wsw2 := withsubword)
    (dc1 := indirect_c) (dc2 := direct_c)
    p p' ev ev pre_eq fn fn post_incl.
Proof.
rewrite /compiler_first_part; t_xrbindP => paw ok_paw pa0.
rewrite !print_uprogP => ok_pa0 pb.
rewrite print_uprogP => ok_pb pa ok_pa pc ok_pc ok_puc ok_puc'.
rewrite !print_uprogP => pd ok_pd.
rewrite !print_uprogP => pe ok_pe.
rewrite !print_uprogP => pf ok_pf.
rewrite !print_uprogP => pg ok_pg.
rewrite !print_uprogP => ph ok_ph pi ok_pi.
rewrite !print_uprogP => plc ok_plc.
rewrite !print_uprogP => ok_fvars pj ok_pj pp.
rewrite !print_uprogP => ok_pp <- {p'} ok_fn.

apply: (
  wiequiv_f_trans
    (wsw1 := nosubword) (wsw2 := withsubword) (wsw3 := withsubword)
    rpreF_trans_eq_eq_eq
    rpostF_trans_eq_eq_eq_uincl
    (it_psem_call_u p ev (fn := fn))
).
apply: wiequiv_f_trans_UU_EU; first exact (it_wi2w_progP _ _ ok_paw).
apply: wiequiv_f_trans_UU_EU; first exact: (it_array_copy_fdP _ ok_pa0).
apply: wiequiv_f_trans_EE_EU; first exact: it_add_init_callP.
apply: wiequiv_f_trans_EE_EU; first exact: (it_alloc_callP _ ok_pb).
apply: wiequiv_f_trans_UU_EU.
apply [elaborate it_inliningP (ev := ev) ok_fn ok_pa ].
apply: wiequiv_f_trans_UU_EU; first exact: it_unrollP ok_pc.
apply: wiequiv_f_trans_EE_EU;
  first exact: (it_dead_calls_err_seqP ok_pd _ ok_fn).
apply: wiequiv_f_trans_EU_EU; first exact: it_live_range_splittingP ok_pe.
apply: wiequiv_f_trans_UU_EU; first exact: (it_remove_init_fdPu is_reg_array).
apply: wiequiv_f_trans_EE_EU.
- apply: (wkequiv_io_weaken (P := rpreF (eS := mra_spec _) fn fn)) => //;
    last exact: (it_makeReferenceArguments_callP _ ok_pf).
  by move=> ???? [_ <-] [<-].
apply: wiequiv_f_trans_UU_EU; first exact: it_indirect_to_direct.
apply: wiequiv_f_trans_EE_EU; first exact: (it_expand_callP ok_pg ok_fn).
apply: wiequiv_f_trans_EU_EU; first exact: it_live_range_splittingP ok_ph.
apply: wiequiv_f_trans_EE_EU; first exact: RGP.it_remove_globP ok_pi.
apply: wiequiv_f_trans_EE_EU; first exact: (it_load_constants_progP ok_plc).
apply: wiequiv_f_trans_EE_EU; first exact:
  (hlop_it_lower_callP
    (hap_hlop haparams)
    (lowering_opt cparams)
    (warning cparams)
    ok_fvars).
apply: wiequiv_f_trans_UU_EU; first exact: (it_pi_callP _ ok_pj).
apply: wiequiv_f_trans_EE_EU; first exact: (it_lower_call_export (hap_hshp haparams) _ ok_pp ok_fn).
apply: wkequiv_io_weaken; last exact: wiequiv_f_eq.
1-3: done.
move=> ???? [_ <-] <-; split=> //; exact: values_uincl_refl.
Qed.

End FIRST_PART.

Section FRONT_END.

Context
  (entries : seq funname)
  (up : uprog (asmop := _asmop))
  (sp : sprog (pd := _pd) (asmop := _asmop))
  (gd : pointer)
  (hcompile : compiler_front_end aparams cparams entries up = ok sp)
.

Definition wf_args fn ms mt vs vt :=
  wf_args
    (size_glob sp) gd ms mt (get_wptrs up fn) (get_align_args sp fn) vs vt.

Definition extend_mem ms mt := extend_mem ms mt gd (sp_globs (p_extra sp)).

Definition pre : relPreF :=
  fun fn fn' s t =>
    let: args := fvals s in
    let: argt := fvals t in
    let: ms := fmem s in
    let: mt := fmem t in
    [/\ fn = fn'
      , alloc_ok sp fn mt
      , wf_args fn ms mt args argt
      , Forall3 (value_eq_or_in_mem mt) (get_wptrs up fn) args argt
      , extend_mem ms mt
      & fscs s = fscs t
    ].

Definition post : relPostF :=
  fun fn _ s t s' t' =>
    let: args := fvals s in
    let: argt := fvals t in
    let: ms := fmem s in
    let: mt := fmem t in
    let: ress := fvals s' in
    let: rest := fvals t' in
    let: ms' := fmem s' in
    let: mt' := fmem t' in
    let: n := get_nb_wptr up fn in
    [/\ List.Forall2 (value_in_mem ms') (take n ress) (take n argt)
      , List.Forall2 value_uincl (drop n ress) rest
      , extend_mem ms' mt'
      , mem_unchanged_params ms mt mt' (get_wptrs up fn) args argt
      & fscs s' = fscs t'
    ].

#[local]
Instance FrontEndEquiv : EquivSpec :=
  {|
    rpreF_ := pre;
    rpostF_ := post;
  |}.

Lemma it_compiler_front_endP ev ev' fn :
  fn \in entries ->
  wiequiv_f
    (wsw1 := nosubword) (wsw2 := withsubword)
    (dc1 := indirect_c) (dc2 := direct_c)
    up sp ev ev' rpreF fn fn rpostF.
Proof.
move: hcompile; rewrite /compiler_front_end.
t_xrbindP=> p1 ok_p1 check_p1 p2 ok_p2 p3.
rewrite print_sprogP => ok_p3 p4.
rewrite print_sprogP => ok_p4 ? ok_fn; subst p4.

End FRONT_END.

End IT.
