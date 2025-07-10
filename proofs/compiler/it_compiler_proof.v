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
apply: wiequiv_f_trans_EE_EU;
  first exact: (it_lower_call_export (hap_hshp haparams) _ ok_pp ok_fn).

apply: wkequiv_io_weaken; last exact: wiequiv_f_eq.
1-3: done.
move=> ???? [_ <-] <-; split=> //; exact: values_uincl_refl.
Qed.

End FIRST_PART.

Section THIRD_PART.

Context
  {entries : seq funname}
  {p p' : sprog}
  {ev : pointer}
.

#[local] Existing Instance withsubword.
#[local] Existing Instance direct_c.

Let rminfo (rp : funname -> option (seq (option nat))) fn :=
  match rp fn with
  | Some l =>
      let l' := map (fun i => if i is None then true else false) l in
      if all (fun b => b) l' then None else Some l' (* do we want that? *)
  | None => removereturn cparams p fn
  end.

Definition post_dc rp := rpostF (eS := dc_spec (rminfo rp)).

Lemma fn_keep_only_uincl rm fn vs1 vs2 vs3 :
  List.Forall2 value_uincl vs1 vs2 ->
  List.Forall2 value_uincl (fn_keep_only rm fn vs2) vs3 ->
  List.Forall2 value_uincl (fn_keep_only rm fn vs1) vs3.
Proof.
rewrite /fn_keep_only; case: rm => [tk|]; last exact: values_uincl_trans.
elim: tk vs1 vs2 vs3 => [|[] tk hind] vs1 vs2 vs3 /=;
  first (exact: values_uincl_trans);
  case: vs2 vs1 => [|v2 vs2] [|v1 vs1] /List_Forall2_inv //= [h hs];
  last exact: hind.
case: vs3 => [|v3 vs3] /List_Forall2_inv //= [h' hs'].
constructor; first exact: (value_uincl_trans h h').
exact: (hind _ _ _ hs hs').
Qed.

Lemma it_compiler_third_part {rp fn} :
  compiler_third_part aparams cparams rp p = ok p' ->
  wiequiv_f (scP1 := sCP_stack) (scP2 := sCP_stack)
    p p' ev ev pre_eq fn fn (post_dc rp).
Proof.
rewrite /compiler_third_part; t_xrbindP=> pa ok_pa.
rewrite !print_sprogP.
set pb := {| p_funcs := regalloc _ _; |} => ok_pb pc ok_p'.
rewrite print_sprogP => ?; subst pc.
apply: (
  wiequiv_f_trans
    (scP1 := sCP_stack) (scP2 := sCP_stack) (scP3 := sCP_stack)
    (rpreF23 := pre_eq) (rpostF23 := post_incl)
    _ _
    (it_dead_code_tokeep_callPs
       (sip := sip_of_asm_e) (hap_is_move_opP haparams) _ ok_pa)
).
- exact: rpreF_trans_eq_eq_eq.
- move=> s1 s2 _ r1 r3 _ [_ <-] [r2 [?? hvals2] [?? hvals3]].
  split; only 1,2: congruence.
  exact: values_uincl_trans hvals2 hvals3.
rewrite -{1}(surj_prog (pT := progStack) pa).
apply: (
  wiequiv_f_trans
    (scP1 := sCP_stack) (scP2 := sCP_stack) (scP3 := sCP_stack)
    (rpreF23 := pre_eq) (rpostF23 := post_incl)
    _ _
    (it_alloc_callP_sprogP _ _ ok_pb (fn:= fn))
).
- exact: rpreF_trans_eq_uincl_eq.
- exact: rpostF_trans_uincl_eq_uincl_uincl.
apply: (
  wiequiv_f_trans
    (scP1 := sCP_stack) (scP2 := sCP_stack) (scP3 := sCP_stack)
    (rpreF23 := pre_incl) (rpostF23 := post_incl)
    _ _
    (it_dead_code_callPs
       (sip := sip_of_asm_e) (hap_is_move_opP haparams) _ ok_p')
       ).
- move=> s1 s2 [_ <-]; exists s1 => //; split=> //; exact: fs_uinclR.
- move=> s1 _ s3 r1 r3 [_ <-] _ [r2 [?? hvals2] [?? hvals3]].
  split; only 1,2: congruence.
  exact: values_uincl_trans hvals2 hvals3.
exact: (it_sem_uincl_f (sCP := sCP_stack) p' ev (fn := fn)).
Qed.

End THIRD_PART.

Section FRONT_END.

Context
  (entries : seq funname)
  (up : uprog (asmop := _asmop))
  (sp : sprog (pd := _pd) (asmop := _asmop))
  (rip : pointer)
.

Definition wf_args fn ms mt vs vt :=
  wf_args
    (size_glob sp) rip ms mt (get_wptrs up fn) (get_align_args sp fn) vs vt.

Definition extend_mem ms mt := extend_mem ms mt rip (sp_globs (p_extra sp)).

Let pre : relPreF :=
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

Let post : relPostF :=
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
    [/\ List.Forall2 (value_in_mem mt') (take n ress) (take n argt)
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

Lemma it_compiler_front_endP ev fn :
  compiler_front_end aparams cparams entries up = ok sp ->
  fn \in entries ->
  wiequiv_f
    (wsw1 := nosubword) (wsw2 := withsubword)
    (dc1 := indirect_c) (dc2 := direct_c)
    up sp ev rip rpreF fn fn rpostF.
Proof.
rewrite /compiler_front_end; t_xrbindP=> p1 ok_p1 check_p1 p2 ok_p2 p3.
rewrite print_sprogP => ok_p3 p4.
set rp := fun (fn : funname) => _.
rewrite print_sprogP => ok_sp ? ok_fn; subst p4.
apply: (wequiv_fun_get (scP1 := sCP_unit) (scP2 := sCP_stack)) => /= fd get_fd.

have [mglob ok_mglob] := [elaborate alloc_prog_get_fundef ok_p2 ].
have [_ p2_p3_extra] :=
  hlap_lower_address_prog_invariants (hap_hlap haparams) ok_p3.
have sp_p3_extra := [elaborate compiler_third_part_meta print_sprogP ok_sp ].
have p2_p1_extra := [elaborate alloc_prog_sp_globs ok_p2 ].
have [] := check_wf_ptrP check_p1 ok_fn get_fd.
set n := find _ _.
rewrite /= all2_map -eqseq_all => /eqP check_params check_return h.

apply: (
  wiequiv_f_trans
    (scP1 := sCP_unit) (scP2 := sCP_unit) (scP3 := sCP_stack)
    (rpreF23 := pre) (rpostF23 := post)
    _ _
    (it_compiler_first_part ok_p1 ok_fn)
).
- move=> s1 ? [? _]; by exists s1.
- move=> s1 _ s3 r1 r3 [_ <-] [_ halloc hwf hptr hmem hscs] [] r2
    [hscs1 hmem1 hval1] [] hptr' hres hmem' hparams hscs'.
  split=> //; only 3,4: congruence.
  + apply: Forall2_trans hptr'; first exact: value_uincl_value_in_mem_trans.
    exact: (Forall2_take hval1).
  apply: Forall2_trans hres; first exact: value_uincl_trans.
  exact: (Forall2_drop hval1).

apply: (wequiv_fun_get (scP1 := sCP_unit) (scP2 := sCP_stack)) => /= fd1
  get_fd1.
move: h => /(_ _ _ get_fd1)[] fd2 /[dup] ok_fd2 h get_fd2.
have [fd3 get_fd3 [_ _ _ _ _ fd2_fd3_extra]] :=
  hlap_lower_address_fd_invariants (hap_hlap haparams) ok_p3 get_fd2.
have [fd4 [get_fd4 fd3_fd4_align]] :=
  compiler_third_part_invariants print_sprogP ok_sp get_fd3.

apply: (
  wiequiv_f_trans
    (scP1 := sCP_unit) (scP2 := sCP_stack) (scP3 := sCP_stack)
    (rpreF23 := pre_eq) (rpostF23 := post_dc (p := p3) rp)
    (p2 := p2) (ev2 := rip) (fn2 := fn)
    _ _
    (it_alloc_progP
       (hap_hshp haparams) (hap_hsap haparams) (hap_is_move_opP haparams)
       ok_p2 ev (rip := rip))
).
- move=> s1 s3 [] [_ hok hwf hptr hmem hscs] _; exists s3 => //; split=> //.
  + by rewrite -p2_p1_extra p2_p3_extra -sp_p3_extra.
  + move: hwf; rewrite /wf_args /get_wptrs get_fd /= check_params.
    rewrite /size_glob sp_p3_extra -p2_p3_extra p2_p1_extra.
    rewrite /get_align_args get_fd4 /= -fd3_fd4_align -fd2_fd3_extra.
    move: ok_fd2; rewrite /alloc_fd; by t_xrbindP=> _ _ <- /=.
  + move: hptr; rewrite /get_wptrs get_fd /=.
    apply: value_eq_or_in_mem_any_option.
    rewrite check_params.
    have /Forall2_flip :=
      map_Forall2 (omap pp_writable)
        (sao_params (ao_stack_alloc (stackalloc cparams p1) fn)).
    apply Forall2_impl.
    by move=> _ ? <-; apply isSome_omap.
  + rewrite /alloc_ok get_fd2 => _ [<-].
    have :=
      compiler_third_part_alloc_ok haparams print_sprogP ok_sp hok get_fd3.
    by rewrite -fd2_fd3_extra.
- move=> s1 s2 _ r1 r3 [hscs_s1] hmem_s1 hwf_s1 heqinmem halloc [_ <-] [].
  move=> r2 [hscs1 m'_mi' vr2_wf vr2_eqinmem U] [hscs2 hmem2 vr_vr1].
  set rminfo := fun fn => _ in vr_vr1.
  set va := fvals s1.
  set va' := fvals s2.
  set vr := fvals r1.
  set vr1 := fvals r1.
  set vr2 := fvals r2.
  set m := fmem s1.
  set mi := fmem s2.
  set m' := fmem s1.
  set mi' := fmem r2.
  have hle1: n <= size fd.(f_params) by apply find_size.
  have [/esym size_vr1 /esym size_vr2] := Forall3_size vr2_wf.
  have [/esym size_va /esym size_va'] := Forall3_size heqinmem.
  have /(f_equal size) := check_params; rewrite 2!size_map => /esym size_sao_params.
  have hle2: n <= size vr.
  * have /(f_equal size) := check_return.
    rewrite size_cat size_map size_iota -size_vr1 => ->.
    exact: leq_addr.

  (* [vr2_eqinmem] can be split into two thanks to [check_results]:
     - the first [n] elements satisfy [value_in_mem];
     - the other ones satisfy equality. *)
  have [vr2_inmem vr2_eq]:
    List.Forall2 (value_in_mem mi') (take n vr) (take n vr2) /\
      drop n vr1 = drop n vr2.
  + split.
    + apply (nth_Forall2 (Vbool true) (Vbool true)).
      + by rewrite (size_takel hle2) size_takel // size_vr2 -size_vr1.
      rewrite (size_takel hle2) => i hi.
      rewrite nth_take // nth_take //.
      have := Forall3_nth vr2_eqinmem None (Vbool true) (Vbool true).
      rewrite -size_vr1 => /(_ _ (leq_trans hi hle2)).
      rewrite check_return nth_cat size_map size_iota hi (nth_map 0);
        last by rewrite size_iota.
      rewrite nth_iota // hmem2 /=.
    apply (eq_from_nth (x0 := Vbool true)).
    + by rewrite 2!size_drop size_vr1 size_vr2.
    move=> i; rewrite size_drop ltn_subRL => hi.
    rewrite 2!nth_drop.
    have := Forall3_nth vr2_eqinmem None (Vbool true) (Vbool true).
    rewrite -size_vr1 => /(_ _ hi).
    rewrite check_return nth_cat size_map size_iota lt_nm_n.
    by rewrite nth_nseq (ltn_sub2rE _ (leq_addr _ _)) -size_vr1 hi.

    (* [vr2_wf] can be rewritten into an equality thanks to [check_results] *)
    have {}vr2_wf: take n vr2 = take n va'.
    + apply (eq_from_nth (x0 := Vbool true)).
    + rewrite size_takel; last by rewrite size_vr2 -size_vr1.
      rewrite size_takel; last by rewrite size_va' size_sao_params.
      reflexivity.
    rewrite size_takel; last by rewrite size_vr2 -size_vr1.
    move=> i hi.
    rewrite nth_take // nth_take //.
    have := Forall3_nth vr2_wf None (Vbool true) (Vbool true).
    rewrite -size_vr1 => /(_ _ (leq_trans hi hle2)).
    rewrite check_return nth_cat size_map size_iota hi (nth_map 0);
      last by rewrite size_iota.
    by rewrite nth_iota //; case.

    (* [fn_keep_only rminfo fn] is just [drop] thanks to [check_results] *)
    have rminfo_vr2: fn_keep_only rminfo fn vr2 = drop n vr2.
    + rewrite /fn_keep_only /rminfo /rp ok_fn.
      set k := size (sao_return (ao_stack_alloc (stackalloc cparams p1) fn)).
      have ->:
        [seq match i with
           | Some _ => false
           | None => true
           end
        | i <- sao_return (ao_stack_alloc (stackalloc cparams p1) fn)]
           = nseq n false ++ nseq (k - n) true.
    + rewrite check_return map_cat.
      apply f_equal2.
    + by rewrite -map_comp map_const_nseq size_iota.
      by apply map_nseq.
      case heq: all.
    + by case: (n) heq => [|//] _; rewrite drop0.
      rewrite -{1}(cat_take_drop n vr2).
      rewrite keep_only_cat; last first.
    + rewrite size_takel; last by rewrite size_vr2 -size_vr1.
      by rewrite size_nseq.
      rewrite keep_only_false; last first.
    + by rewrite size_take; apply geq_minl.
      by rewrite keep_only_true.

  have hn : get_nb_wptr up fn = n.
  - by rewrite /get_nb_wptr /get_wptrs /= get_fd seq.find_map.

  split; last congruence.
  - rewrite hn -vr2_wf -hmem2; exact: vr2_inmem.
  - rewrite hn vr2_eq -rminfo_vr2; exact: vr_vr1.
  - by rewrite -hmem2 /extend_mem sp_p3_extra -p2_p3_extra p2_p1_extra.
  by rewrite /get_wptrs get_fd /= check_params -hmem2.

apply: (
  wiequiv_f_trans
    _ _
    (hlap_it_lower_addressP (hap_hlap haparams) ok_p3)
    (it_compiler_third_part ok_sp)
).
- exact: rpreF_trans_eq_eq_eq.
by move=> s1 _ _ r1 r3 [_ <-] [_ <-] [_ <-] [hscs hmem] h'.
Qed.

End FRONT_END.

End IT.
