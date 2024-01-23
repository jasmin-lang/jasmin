From mathcomp Require Import all_ssreflect all_algebra.

Require Import
  arch_params_proof
  compiler
  compiler_util
  psem
  psem_facts.
Require Import
  allocation_proof
  lower_spill_proof
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
  stack_zeroization_proof.

Require Import
  arch_decl
  arch_extra
  arch_sem
  asm_gen_proof
  sem_params_of_arch_extra.
Import Utf8.
Import wsize.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Existing Instance withsubword.

Section PROOF.

Context
  {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}
  `{asm_e : asm_extra} {call_conv : calling_convention} {asm_scsem : asm_syscall_sem}
  {lowering_options : Type}
  (aparams : architecture_params lowering_options)
  (haparams : h_architecture_params aparams)
  (cparams : compiler_params lowering_options).

Hypothesis print_uprogP : forall s p, cparams.(print_uprog) s p = p.
Hypothesis print_sprogP : forall s p, cparams.(print_sprog) s p = p.
Hypothesis print_linearP : forall s p, cparams.(print_linear) s p = p.

#[local]
Existing Instance progUnit.

Lemma postprocessP {dc : DirectCall} (p p': uprog) ev scs m fn va scs' m' vr va' :
  dead_code_prog (ap_is_move_op aparams) (const_prop_prog p) false = ok p' →
  sem_call p ev scs m fn va scs' m' vr →
  List.Forall2 value_uincl va va' →
  exists2 vr',
    sem_call p' ev scs m fn va' scs' m' vr'
    & List.Forall2 value_uincl vr vr'.
Proof.
  move => ok_p' E A.
  have [ vr1 [ {} E R1 ] ] := const_prop_callP E A.
  have! [ vr2 [ E' R2 ] ] :=
    (dead_code_callPu
      (hap_is_move_opP haparams)
      ok_p'
      (List_Forall2_refl _ value_uincl_refl)
      E).
  exists vr2; first exact: E'.
  apply: Forall2_trans R1 R2.
  exact: value_uincl_trans.
Qed.

Lemma unrollP  {dc : DirectCall} (fn : funname) (p p' : prog) ev scs mem va va' scs' mem' vr :
  unroll_loop (ap_is_move_op aparams) p = ok p'
  -> sem_call p ev scs mem fn va scs' mem' vr
  -> List.Forall2 value_uincl va va'
  -> exists vr',
       sem_call p' ev scs mem fn va' scs' mem' vr'
       /\ List.Forall2 value_uincl vr vr'.
Proof.
  rewrite /unroll_loop; t_xrbindP.
  elim: Loop.nb p va va' vr => //= n Hn p va va' vr p1 ok_p1.
  case e: unroll_prog => [ p2 [] ]; last first.
  { move/ok_inj => {n Hn} <- E A.
    have [ vr' {} E R ] := postprocessP ok_p1 E A.
    by exists vr'. }
  t_xrbindP => p3 ok_p3 ok_p' E A.
  have [ vr1 {} E R1 ] := postprocessP ok_p1 E (List_Forall2_refl _ value_uincl_refl).
  have := unroll_callP E.
  rewrite e /= => {} E.
  have [ vr2 [] {} E R2 ] := Hn _ _ _ _ _ ok_p3 ok_p' E A.
  exists vr2; split; first exact: E.
  apply: Forall2_trans R1 R2.
  exact: value_uincl_trans.
Qed.

Definition compose_pass : ∀ vr (P Q: _ → Prop),
        (∀ vr', P vr' → Q vr') →
        (exists2 vr', List.Forall2 value_uincl vr vr' & P vr') →
        (exists2 vr', List.Forall2 value_uincl vr vr' & Q vr')
    := λ vr P Q h x, let 'ex_intro2 vr' u p := x in ex_intro2 _ _ vr' u (h vr' p).

Definition compose_pass_uincl : ∀ vr (P Q: _ → Prop),
        (∀ vr, P vr → ∃ vr', Q vr' ∧ List.Forall2 value_uincl vr vr') →
        (exists2 vr', List.Forall2 value_uincl vr vr' & P vr') →
        (exists2 vr', List.Forall2 value_uincl vr vr' & Q vr')
  :=
      λ vr P Q h x,
      let 'ex_intro2 vr1 u p := x in
      let 'ex_intro vr2 (conj q v) := h _ p in
      ex_intro2 _ _ vr2 (Forall2_trans value_uincl_trans u v) q.

Definition compose_pass_uincl' : ∀ vr (P Q: _ → Prop),
        (∀ vr, P vr → exists2 vr', List.Forall2 value_uincl vr vr' & Q vr') →
        (exists2 vr', List.Forall2 value_uincl vr vr' & P vr') →
        (exists2 vr', List.Forall2 value_uincl vr vr' & Q vr')
  :=
      λ vr P Q h x,
      let 'ex_intro2 vr1 u p := x in
      let 'ex_intro2 vr2 v q := h _ p in
      ex_intro2 _ _ vr2 (Forall2_trans value_uincl_trans u v) q.

Lemma live_range_splittingP {dc : DirectCall} (p p': uprog) scs m fn va scs' m' vr :
  live_range_splitting aparams cparams p = ok p' →
  sem_call p tt scs m fn va scs' m' vr →
  exists2 vr',
      List.Forall2 value_uincl vr vr' &
      sem_call p' tt scs m fn va scs' m' vr'.
Proof.
  rewrite /live_range_splitting; t_xrbindP.
  rewrite !print_uprogP => ok_p' pa ok_pa.
  rewrite print_uprogP => ? exec_p; subst pa.
  have va_refl := List_Forall2_refl va value_uincl_refl.
  apply: compose_pass_uincl.
  - move=> vr' Hvr'.
    apply: (dead_code_callPu (hap_is_move_opP haparams) ok_pa va_refl).
    exact: Hvr'.
  apply: compose_pass_uincl;
    first by move => vr';
             apply: (alloc_call_uprogP (sip := sip_of_asm_e) ok_p').
  exists vr.
  - exact: (List_Forall2_refl _ value_uincl_refl).
  by rewrite surj_prog.
Qed.

Lemma values_uincl_refl vs :
  List.Forall2 value_uincl vs vs.
Proof. exact: List_Forall2_refl value_uincl_refl. Qed.

Lemma inliningP (to_keep: seq funname) (p p': uprog) scs m fn va scs' m' vr :
  inlining cparams to_keep p = ok p' →
  fn \in to_keep →
  sem_call (wsw := withsubword) (dc := indirect_c) p tt scs m fn va scs' m' vr →
  exists2 vr', List.Forall2 value_uincl vr vr' & sem_call (dc := indirect_c) p' tt scs m fn va scs' m' vr'.
Proof.
  rewrite /inlining /=; t_xrbindP => pa.
  rewrite print_uprogP => ok_pa pb ok_pb.
  rewrite print_uprogP => <- {p'} ok_fn h.
  apply: compose_pass.
  - by move => vr'; exact: (dead_calls_err_seqP (sip := sip_of_asm_e) (sCP := sCP_unit) ok_pb).
  exact: (inline_call_errP ok_pa (values_uincl_refl va) h).
Qed.

Lemma compiler_first_partP entries (p: prog) (p': uprog) scs m fn va scs' m' vr :
  compiler_first_part aparams cparams entries p = ok p' →
  fn \in entries →
  sem_call (wsw:= nosubword) (dc:=indirect_c) p tt scs m fn va scs' m' vr →
  exists2 vr',
    List.Forall2 value_uincl vr vr' &
    sem_call (dc:=direct_c) p' tt scs m fn va scs' m' vr'.
Proof.
  rewrite /compiler_first_part; t_xrbindP => pa0.
  rewrite print_uprogP => ok_pa0 pb.
  rewrite print_uprogP => ok_pb pa.
  rewrite print_uprogP => ok_pa pc ok_pc.
  rewrite !print_uprogP => pd ok_pd.
  rewrite !print_uprogP => pe ok_pe.
  rewrite !print_uprogP => pf ok_pf.
  rewrite !print_uprogP => pg ok_pg.
  rewrite !print_uprogP => ph ok_ph pi ok_pi.
  rewrite !print_uprogP => ok_fvars pj ok_pj pp.
  rewrite !print_uprogP => ok_pp <- {p'} ok_fn exec_p.

  have va_refl := List_Forall2_refl va value_uincl_refl.
  apply: compose_pass_uincl.
  - move=> vr'; apply: (pi_callP (sCP := sCP_unit) ok_pp va_refl).
   apply: compose_pass.
  - move=> vr'.
    assert (h := lower_slh_prog_sem_call (dc:=direct_c) (hap_hshp haparams) (ev:= tt) ok_pj).
    apply h => //.
  apply: compose_pass.
  - move => vr'.
    exact:
      (hlop_lower_callP
         (hap_hlop haparams)
         (lowering_opt cparams)
         (warning cparams)
         ok_fvars).
  apply: compose_pass; first by move => vr'; apply: (RGP.remove_globP ok_pi).
  apply: compose_pass_uincl'.
  - move => vr'; apply: (live_range_splittingP ok_ph).
  apply: compose_pass.
  - move=> vr' hvr'. assert (h := expand_callP (sip := sip_of_asm_e) ok_pg); apply h => //; apply hvr'.
  apply: compose_pass_uincl'.
  - by move=>  vr'; apply: indirect_to_direct.
  apply: compose_pass.
  - by move=> vr'; apply: (makeReferenceArguments_callP (siparams := sip_of_asm_e) ok_pf).
  apply: compose_pass_uincl; first by move =>vr'; apply: (remove_init_fdPu _ va_refl).
  apply: compose_pass_uincl'.
  - move => vr' Hvr'.
    apply: (live_range_splittingP ok_pe); exact: Hvr'.
  apply: compose_pass.
  - by move => vr'; exact: (dead_calls_err_seqP (sip := sip_of_asm_e) (sCP := sCP_unit) ok_pd).
  apply: compose_pass_uincl; first by move=> vr' Hvr'; apply: (unrollP ok_pc _ va_refl); exact: Hvr'.
  apply: compose_pass_uincl'; first by move => vr' Hvr'; apply: (inliningP ok_pa ok_fn); exact: Hvr'.
  apply: compose_pass.
  - by move=> vr'; apply: (lower_spill_fdP (sip := sip_of_asm_e) (sCP := sCP_unit) ok_pb).
  apply: compose_pass; first by move => vr'; apply: (add_init_fdP).
  apply: compose_pass_uincl.
  - by move=> vr'; apply:(array_copy_fdP (sCP := sCP_unit) ok_pa0 va_refl).
  apply: compose_pass; first by move => vr'; exact: psem_call_u.
  exists vr => //.
  exact: (List_Forall2_refl _ value_uincl_refl).
Qed.

Lemma compiler_third_partP returned_params (p p' : @sprog _pd _ _asmop) :
  compiler_third_part aparams cparams returned_params p = ok p' →
  [/\
    ∀ fn (gd: pointer) scs m va scs' m' vr,
      sem_call (dc:= direct_c) p gd scs m fn va scs' m' vr →
      exists2 vr',
      let rminfo fn :=
        match returned_params fn with
        | Some l =>
          let l' := map (fun i => if i is None then true else false) l in
          if all (fun b => b) l' then None else Some l' (* do we want that? *)
        | None => removereturn cparams p fn
        end
      in
      List.Forall2 value_uincl (fn_keep_only rminfo fn vr) vr' &
      sem_call (dc:= direct_c) p' gd scs m fn va scs' m' vr' &
    ∀ fn m,
      alloc_ok p' fn m → alloc_ok p fn m
  ].
Proof.
  rewrite /compiler_third_part; t_xrbindP=> pa ok_pa.
  rewrite !print_sprogP => ok_pb pc ok_pc.
  rewrite print_sprogP => <- {p'}.
  split.
  + move => fn gd scs m va scs' m' vr exec_p.
    have va_refl : List.Forall2 value_uincl va va.
    - exact: List_Forall2_refl.
    apply: compose_pass_uincl.
    - move => vr'.
      apply: (dead_code_callPs (dc:= direct_c) (hap_is_move_opP haparams) ok_pc va_refl).
    apply: compose_pass_uincl;
      first by move => vr';
        apply:
          (alloc_call_sprogP (ep := ep_of_asm_e) (sip := sip_of_asm_e) ok_pb).
    rewrite surj_prog.
    have! [vr' [exec_pa]] :=
      (dead_code_tokeep_callPs (hap_is_move_opP haparams) ok_pa va_refl exec_p).
    by exists vr'.
  rewrite /alloc_ok => fn m alloc_pc fd get_fd.
  have [fda ok_fda get_fda] := [elaborate
    (dead_code_prog_tokeep_get_fundef (pT:=progStack) ok_pa get_fd)].
  have [fdb [get_fdb ok_fdb]] :=
    allocation_proof.all_checked (sip := sip_of_asm_e) ok_pb get_fda.
  have [fdc ok_fdc get_fdc] := [elaborate
    (dead_code_prog_tokeep_get_fundef (pT:=progStack) ok_pc get_fdb)].
  move: (alloc_pc _ get_fdc).
  have [_ _ ->]:= dead_code_fd_meta ok_fdc.
  rewrite /sf_total_stack.
  have [ <- <- <- ] := [elaborate @check_fundef_meta _ _ _ _ _ _ _ (_, fda) _ _ _ ok_fdb].
  have [_ _ ->]:= dead_code_fd_meta ok_fda.
  done.
Qed.

Lemma compiler_third_part_meta entries (p p' : sprog) :
  compiler_third_part aparams cparams entries p = ok p' →
  p_extra p' = p_extra p.
Proof.
  rewrite /compiler_third_part.
  t_xrbindP => pa hpa _ pb hpb.
  have! [_ ok_pa] := (dead_code_prog_tokeep_meta hpa).
  have! [] := (dead_code_prog_tokeep_meta hpb).
  rewrite !print_sprogP /= => _ ok_pb <- {p'}.
  by rewrite ok_pb ok_pa.
Qed.

Lemma compiler_third_part_invariants entries p p' :
  compiler_third_part aparams cparams entries p = ok p' ->
  forall fn fd, get_fundef p.(p_funcs) fn = Some fd ->
  exists fd', get_fundef p'.(p_funcs) fn = Some fd' /\
  fd.(f_extra).(sf_align_args) = fd'.(f_extra).(sf_align_args).
Proof.
  rewrite /compiler_third_part.
  t_xrbindP => pa hpa.
  rewrite 2!print_sprogP /= => check_pa pb hpb.
  rewrite print_sprogP => <-{p'}.
  move=> fn fd ok_fd.
  have [fda ok_fda get_fda] := [elaborate dead_code_prog_tokeep_get_fundef (pT:=progStack) hpa ok_fd].
  rewrite /check_sprog in check_pa.
  have [fda' [get_fda' check_fda']] := [elaborate allocation_proof.all_checked (pT:=progStack)
  (p2:={|
          p_funcs := regalloc cparams (p_funcs pa); p_globs := p_globs pa; p_extra := p_extra pa
        |}) check_pa get_fda].
  have [fdb ok_fdb get_fdb] := [elaborate dead_code_prog_tokeep_get_fundef (pT:=progStack) hpb get_fda'].
  exists fdb; split=> //.
  have [_ _ ->] := dead_code_fd_meta ok_fdb.
  have /= [_ _ _ <-] := [elaborate check_fundef_meta check_fda'].
  have [_ _ ->] := dead_code_fd_meta ok_fda.
  done.
Qed.

(* TODO: move *)
Remark sp_globs_stack_alloc rip rsp data ga la (p: uprog) (p': sprog) :
  alloc_prog (ap_shp aparams) (ap_sap aparams) (fresh_var_ident cparams (Reg (Normal, Direct)) dummy_instr_info) rip rsp data ga la p = ok p' →
  sp_globs (p_extra p') = data.
Proof.
  by rewrite /alloc_prog; t_xrbindP => ???? _ <-.
Qed.

Lemma compiler_third_part_alloc_ok entries (p p' : sprog) (fn: funname) (m: mem) :
  compiler_third_part aparams cparams entries p = ok p' →
  alloc_ok p' fn m →
  alloc_ok p fn m.
Proof. case/compiler_third_partP => _; exact. Qed.
(*
Lemma check_no_ptrP entries ao u fn :
  check_no_ptr entries ao = ok u →
  fn \in entries →
  allNone (sao_params (ao fn)) ∧ allNone (sao_return (ao fn)).
Proof.
  clear.
  case: u => /allMP h /InP ok_fn; move: (h _ ok_fn).
  by t_xrbindP.
Qed.
*)
Lemma allNone_nth {A} (m: seq (option A)) i :
  allNone m ->
  nth None m i = None.
Proof.
  elim: m i.
  - by move => ? _; exact: nth_nil.
  by case => // m ih [].
Qed.

Lemma check_wf_ptrP entries p ao u fn fd :
  check_wf_ptr entries p ao = ok u ->
  fn \in entries ->
  get_fundef p.(p_funcs) fn = Some fd ->
  all2 (λ (x : var_i) pi, reg_ptr_writable_status x == omap pp_writable pi)
    (f_params fd) (sao_params (ao fn)) /\
  let n := count (fun x => reg_ptr_writable_status x == Some true) fd.(f_params) in
  sao_return (ao fn) = [seq Some i | i <- iota 0 n] ++ nseq (size (sao_return (ao fn)) - n) None.
Proof.
  move=> hcheck ok_fn get_fd.
  set n := count (fun x => reg_ptr_writable_status x == Some true) fd.(f_params).
  move: hcheck; rewrite /check_wf_ptr.
  t_xrbindP=> /allP /(_ _ ok_fn); rewrite get_fd => hparams.
  move=> /allP /(_ _ ok_fn); rewrite get_fd -/n => /andP [/eqP hl hr].
  split=> //.
  rewrite -{1}(cat_take_drop n (sao_return _)).
  apply f_equal2 => //.
  apply (@eq_from_nth _ None).
  + by rewrite size_drop size_nseq.
  move=> i; rewrite size_drop => hi.
  rewrite nth_nseq hi.
  exact: allNone_nth hr.
Qed.

Lemma sem_call_length {dc:DirectCall}(p: uprog) scs m fn va scs' m' vr :
  sem_call p tt scs m fn va scs' m' vr →
  ∃ fd,
    [/\ get_fundef (p_funcs p) fn = Some fd,
     size (f_params fd) = size va,
     size (f_tyin fd) = size va,
     size (f_tyout fd) = size vr &
     size (f_res fd) = size vr].
Proof.
  move=> h; have := sem_callE h => -[] fd [] -> [] va' [] ? [] ? [] ? [] vr' [] ok_args [] _ ok_va' _ [] /size_mapM ok_vr' ok_res _.
  have := size_fold2 ok_va'.
  have [<- <-] := size_mapM2 ok_args.
  have [size_vr' <-] := size_mapM2 ok_res.
  rewrite {2}size_vr' -ok_vr' => {1}<-.
  by exists fd.
Qed.


(* Link between a reg ptr argument value [va] in the source and
   the corresponding pointer [p] in the target. [m1] is the source memory,
   [m2] is the target memory.
*)
Record wf_arg_pointer' (glob_size:Z) rip m1 m2 (writable:bool) align va p := {
  wap_align             : is_align p align;
    (* [p] is aligned *)
  wap_no_overflow       : no_overflow p (size_val va);
    (* [p] is able to store a block as large as [va] *)
  wap_valid             : forall w, between p (size_val va) w U8 -> validw m2 w U8;
    (* the bytes in [p ; p + size_val va - 1] are valid *)
  wap_fresh             : forall w, validw m1 w U8 -> disjoint_zrange p (size_val va) w (wsize_size U8);
    (* the bytes in [p ; p + size_val va - 1] are disjoint from the valid bytes of [m1] *)
  wap_writable_not_glob : writable -> (0 < glob_size)%Z -> disjoint_zrange rip glob_size p (size_val va);
    (* if the reg ptr is marked as writable, then the bytes in [p ; p + size_val va - 1] are disjoint from
       the bytes containing the globals *)
  wap_read              : forall off w, get_val_byte va off = ok w -> read m2 (p + wrepr _ off)%R U8 = ok w
    (* the memory at address [p] contains [va] *)
}.

(* Link between the values given as arguments in the source and the target. *)
Definition wf_arg' glob_size rip m1 m2 writable align va va' :=
  match writable with
  | None => va' = va (* no reg ptr : both values are equal *)
  | Some writable => (* reg ptr : [va] is compiled to a pointer [p] that satisfies [wf_arg_pointer] *)
    exists p,
      va' = Vword p /\ wf_arg_pointer' glob_size rip m1 m2 writable align va p
  end.

Inductive Forall4 (A B C D : Type) (R : A -> B -> C -> D -> Prop) : seq A -> seq B -> seq C -> seq D -> Prop :=
| Forall4_nil : Forall4 R [::] [::] [::] [::]
| Forall4_cons : forall a b c d la lb lc ld, R a b c d -> Forall4 R la lb lc ld -> Forall4 R (a :: la) (b :: lb) (c :: lc) (d :: ld).

Definition wf_args' (glob_data:seq u8) rip m1 m2 (p:uprog) (p':sprog) fn va va' :=
  let glob_size := Z.of_nat (size glob_data) in
  forall fd, get_fundef p.(p_funcs) fn = Some fd ->
  forall fd', get_fundef p'.(p_funcs) fn = Some fd' ->
  let l1 :=
    map reg_ptr_writable_status fd.(f_params)
  in
  let l2 := fd'.(f_extra).(sf_align_args) in
  Forall4 (wf_arg' glob_size rip m1 m2) l1 l2 va va'.

(* We consider two reg ptr values in the list [va] of source values and the
   corresponding pointers in the list [va'] of target values.
   If one of the reg ptr is writable, the zones in the target memory pointed to
   by the two pointers are disjoint.
*)
Definition disjoint_values' (writable:seq (option bool)) va va' :=
  forall i1 w1 i2 writable2 w2,
    nth None writable i1 = Some true ->
    nth (Vbool true) va' i1 = @Vword Uptr w1 ->
    nth None writable i2 = Some writable2 ->
    nth (Vbool true) va' i2 = @Vword Uptr w2 ->
    i1 <> i2 ->
    disjoint_zrange w1 (size_val (nth (Vbool true) va i1)) w2 (size_val (nth (Vbool true) va i2)).

Definition disjoint_values'' (p:uprog) fn va va' :=
  forall fd, get_fundef p.(p_funcs) fn = Some fd ->
  let l1 :=
    map reg_ptr_writable_status fd.(f_params)
  in
  disjoint_values' l1 va va'.


(* Link between a reg ptr result value [vr] in the source and the corresponding pointer
   [p] in the target. [m1] is the source memory. The reg ptr is associated to
   the [i]-th elements of [vargs1] and [vargs2] (the arguments in the source and
   the target).
*)
Record wf_result_pointer' m1 varg2 vr p := {
  wrp_args    : varg2 = Vword p;
    (* the pointer [p] that is returned is the same that was taken as argument (in the target) *)
(*   wrp_subtype : subtype (type_of_val vr) varg1; *)
    (* [vr] is smaller than the value taken as argument (in the source) *)
    (* actually, size_of_val vr <= size_of_val (nth (Vbool true) vargs1 i) is enough to do the proofs,
       but this is true and we have lemmas about [subtype] (e.g. [wf_sub_region_subtype] *)
  wrp_read    : forall off w, get_val_byte vr off = ok w -> read m1 (p + wrepr _ off)%R U8 = ok w
    (* the memory at address [p] contains [vr] *)
}.

Definition wf_results_pointer' m vargs2 vres1 :=
  List.Forall2 (fun va2 vr1 =>
    exists p, va2 = Vword p /\ wf_result_pointer' m va2 vr1 p) vargs2 vres1.

(* TODO: better name *)
(* oseq.onth_nth_size but with no default arg to pass
   (in case there is no obvious inabitant of type [T]) *)
Lemma onth_not_default {T} (s:seq T) i :
  i < size s ->
  exists x, oseq.onth s i = Some x.
Proof.
  elim: s i => [//|a s ih].
  move=> [|i].
  + move=> _; exists a; reflexivity.
  move=> /ih. done.
Qed.

Lemma nth_Forall2 A B (R : A -> B -> Prop) (la : seq A) (lb : seq B) a b :
  size la = size lb ->
  (∀ i : nat, i < size la → R (nth a la i) (nth b lb i)) ->
  List.Forall2 R la lb.
Proof.
  elim: la lb => [|a' la ih] [|b' lb] //= [] /ih{}ih hnth.
  constructor.
  + by apply (hnth 0 erefl).
  apply ih. move=> i; apply (hnth i.+1).
Qed.

Lemma Forall4_size A B C D R (la : seq A) (lb : seq B) (lc : seq C) (ld : seq D) :
  Forall4 R la lb lc ld -> [/\ size la = size lb, size la = size lc & size la = size ld].
Proof.
  elim {la lb lc ld}.
  - done.
  move=> a b c d la lb lc ld _ _ /= [<- <- <-].
  done.
Qed.

Lemma List_Forall4_inv A B C D (R : A -> B -> C -> D -> Prop) l1 l2 l3 l4 :
  Forall4 R l1 l2 l3 l4 ->
  match l1, l2, l3, l4 with
  | [::], [::], [::], [::] => True
  | a :: l1, b :: l2, c :: l3, d :: l4 => R a b c d /\ Forall4 R l1 l2 l3 l4
  | _, _, _, _ => False
  end.
Proof. by case. Qed.

Lemma Forall4_impl A B C D (R1 R2 : A -> B -> C -> D -> Prop) :
  (forall a b c d, R1 a b c d -> R2 a b c d) ->
  forall la lb lc ld,
  Forall4 R1 la lb lc ld ->
  Forall4 R2 la lb lc ld.
Proof.
  move=> himpl la lb lc ld.
  elim {la lb lc ld}.
  - constructor.
  move=> a b c d la lb lc ld h _ ih.
  by constructor; auto.
Qed.

Lemma keep_only_false {A} (l : seq A) n :
  size l <= n ->
  keep_only l (nseq n false) = [::].
Proof. by elim: n l => [|n ih] [|a l] //= /ih. Qed.

Lemma keep_only_true {A} (l : seq A) n :
  keep_only l (nseq n true) = l.
Proof. by elim: n l => [//|n ih] [//|a l] /=; rewrite ih. Qed.

Lemma keep_only_cat {A} (l1 l2 : seq A) (tokeep1 tokeep2 : seq bool) :
  size l1 = size tokeep1 ->
  keep_only (l1 ++ l2) (tokeep1 ++ tokeep2) =
  keep_only l1 tokeep1 ++ keep_only l2 tokeep2.
Proof. by elim: tokeep1 l1 => [|b tokeep1 ih] [|a1 l1] //= [] /ih ->; case: b. Qed.


Definition disjoint_from_writable_param' p (b:option bool) varg1 varg2 :=
  forall p2, b = Some true -> varg2 = @Vword Uptr p2 ->
  disjoint_zrange p2 (size_val varg1) p (wsize_size U8).
Definition disjoint_from_writable_params' (P:uprog) fn p va va' :=
  forall fd, get_fundef P.(p_funcs) fn = Some fd ->
  let l1 :=
    map reg_ptr_writable_status fd.(f_params)
  in
  Forall3 (disjoint_from_writable_param' p) l1 va va'.
Definition mem_unchanged_params' P fn ms m0 m vargs1 vargs2 :=
  forall p, validw m0 p U8 -> ~ validw ms p U8 -> disjoint_from_writable_params' P fn p vargs1 vargs2 ->
  read m0 p U8 = read m p U8.

Lemma compiler_front_endP
  entries
  (p: prog)
  (p': @sprog _pd _ _asmop)
  (gd : pointer)
  scs m mi fn va scs' m' vr :
  compiler_front_end aparams cparams entries p = ok p' →
  fn \in entries →
  sem_call (dc:=indirect_c) (wsw:= nosubword) p tt scs m fn va scs' m' vr →
  extend_mem m mi gd (sp_globs (p_extra p')) →
  forall va',
  wf_args' (sp_globs (p_extra p')) gd m mi p p' fn va va' ->
  disjoint_values'' p fn va va' ->
  alloc_ok p' fn mi →
  ∃ vr' mi',
    [/\
     (* on pourrait remplacer par
     find (reg_ptr_writable_status x != Some true) fd.(f_params) *)
     let n :=
       match get_fundef p.(p_funcs) fn with
       | None => 0 (* impossible *)
       | Some fd => count (fun x => reg_ptr_writable_status x == Some true) fd.(f_params)
       end
     in
     wf_results_pointer' mi' (take n va') (take n vr) /\
     List.Forall2 value_uincl (drop n vr) vr',
     sem_call (dc:=direct_c) p' gd scs mi fn va' scs' mi' vr',
     extend_mem m' mi' gd (sp_globs (p_extra p')) &
     mem_unchanged_params' p fn m mi mi' va va'
    ].
Proof.
  rewrite /compiler_front_end;
  t_xrbindP => p1 ok_p1 check_p1 p2 ok_p2 p3.
  rewrite print_sprogP => ok_p3 <- {p'} ok_fn exec_p.
  rewrite (compiler_third_part_meta ok_p3) => m_mi va' va'_wf va'_disj ok_mi.
  have ok_mi': [elaborate alloc_ok p2 fn mi].
  + exact: compiler_third_part_alloc_ok ok_p3 ok_mi.
  have [vr1 vr_vr1 exec_p1] := compiler_first_partP ok_p1 ok_fn exec_p.
  have gd2 := sp_globs_stack_alloc ok_p2.
  rewrite -gd2 in ok_p2.
  case/sem_call_length: (exec_p1) => fd1 [] get_fd1 size_params size_tyin size_tyout size_res.
  have! [mglob ok_mglob] := (alloc_prog_get_fundef ok_p2).
  move=> /(_ _ _ get_fd1)[] fd2 /dup[] ok_fd2 /alloc_fd_checked_sao[] ok_sao_p ok_sao_r get_fd2.
  have [fd [get_fd _]] := sem_callE exec_p.
  rewrite get_fd.
  set n := count (fun x => reg_ptr_writable_status x == Some true) fd.(f_params).
  have := check_wf_ptrP check_p1 ok_fn get_fd.
  rewrite -/n /= => -[check_params check_return].

  have [hargs hdisj]: [elaborate wf_args (sp_globs (p_extra p2)) gd
     (ao_stack_alloc (stackalloc cparams p1)) m mi fn va va'
     /\ disjoint_values (sao_params (ao_stack_alloc (stackalloc cparams p1) fn)) va va'].
  + move: va'_wf; rewrite /wf_args' => /(_ _ get_fd).
    have [fd3 [get_fd3 align_eq]] := compiler_third_part_invariants ok_p3 get_fd2.
    move=> /(_ _ get_fd3). rewrite -align_eq.
    move: (ok_fd2); rewrite /alloc_fd.
    t_xrbindP=> _ _ <- /=.
    move=> h1; split.
    + move: h1 check_params.
      rewrite /wf_args.
      elim: sao_params (f_params fd) va va' {exec_p exec_p1 va'_disj size_params size_tyin}.
      + move=> [|x params] [|va vas] [|va' vas'] /List_Forall4_inv //= _.
        by constructor.
      move=> pi sao_params ih.
      move=> [|x params] [|va vas] [|va' vas'] /List_Forall4_inv //= [h1 h2].
      move=> /andP [check_param check_params].
      constructor.
      + case: pi check_param h1 {check_params} => [pi|] /=.
        + rewrite /wf_arg'. move=> /eqP ->.
          move=> [pr [-> H2]]. exists pr; split; [reflexivity|].
          case: H2=> ??????. by split.
        move=> /eqP -> /=. done.
      by apply (ih _ _ _ h2 check_params).
    move=> i1 pi1 w1 i2 pi2 w2 hpi1 hw1 hpi2 hw2 i1_i2_neq hwpi1.
    have [x _]: exists x, oseq.onth fd.(f_params) i1 = Some x.
    + apply onth_not_default.
      move: check_params; rewrite all2E => /andP [/eqP -> _].
      rewrite (nth_not_default hpi1); last by discriminate. done.
    move: va'_disj => /(_ _ get_fd). apply=> //.
    + have /(@all2_nth _ _ _ _ _) := check_params.
      move=> /(_ x None i1). rewrite (nth_not_default hpi1); last by discriminate.
      rewrite orbT. move=> /(_ erefl) /eqP.
      rewrite (nth_map x). move=> ->. rewrite hpi1 /=. congruence.
      move: check_params; rewrite all2E => /andP [/eqP -> _].
      rewrite (nth_not_default hpi1); last by discriminate. done.
    have /(@all2_nth _ _ _ _ _) := check_params.
    move=> /(_ x None i2). rewrite (nth_not_default hpi2); last by discriminate.
    rewrite orbT. move=> /(_ erefl) /eqP.
    rewrite (nth_map x). move=> ->. rewrite hpi2 /=. reflexivity.
    move: check_params; rewrite all2E => /andP [/eqP -> _].
    rewrite (nth_not_default hpi2); last by discriminate. done.

  have := alloc_progP _ (hap_hsap haparams) ok_p2 exec_p1 m_mi.
  move => /(_ (hap_hshp haparams) va' hargs hdisj ok_mi').
  case => mi' [] vr2 [] exec_p2 [] m'_mi' [] ok_vr2 U.
  have [] := compiler_third_partP ok_p3.
  case/(_ _ _ _ _ _ _ _ _ exec_p2) => vr3 vr2_vr3 exec_p3.
  exists vr3, mi'; split=> //.
  have [fd3 [get_fd3 _]] := sem_callE exec_p3.
  have /= hle1: n <= size fd.(f_params) by apply count_size.
  have := Forall4_size (va'_wf _ get_fd _ get_fd3);
    rewrite size_map /= => -[heq1 heq2 heq3].
  have /= [heq4 heq5] := Forall3_size ok_vr2.
  have /= heq6 := Forall2_size vr_vr1.
  have hle2: n <= size vr.
  + have /(f_equal size) := check_return. rewrite size_cat size_map size_iota.
    rewrite heq6 -heq4 => ->.
    exact: leq_addr.
  split.
  + apply (nth_Forall2 (a:=Vbool true) (b:=Vbool true)).
    rewrite !size_takel. done. done. congruence.
    move=> i. rewrite size_takel; last by congruence. move=> hi.
    rewrite (nth_take (Vbool true) hi).
    have := Forall3_nth ok_vr2 None (Vbool true) (Vbool true).
    have hi': i < size (sao_return (ao_stack_alloc (stackalloc cparams p1) fn)).
    + rewrite heq4 -heq6. by apply (leq_trans hi hle2).
    move=> /(_ _ hi').
    rewrite -(nth_take None hi).
    rewrite check_return; rewrite take_size_cat; last by rewrite size_map size_iota.
    rewrite (nth_map 0 None); last by rewrite size_iota.
    rewrite (nth_iota _ _ hi). (* bug: About nth_iota : p et m ont l'air implicites, mais en fait non *)
    (* + bug sur elim: eer {} er {} : qu'est-ce que c'est censé vouloir dire ? *)
    rewrite add0n.
    simpl.
    move=> [pr [hpr1 hpr2]].
    exists pr; split.
    + case: hpr2. done.
    split.
    + case: hpr2. done. (* redundant *)
    case: hpr2=> _ _ h off w. rewrite nth_take; last by assumption. eauto.
    have huincl := Forall2_nth vr_vr1 (Vbool true) (Vbool true) (leq_trans hi hle2).
    move=> /(value_uincl_get_val_byte huincl).
    by eauto.
  set rminfo := λ fn : funname,
              match
                (if fn \in entries
                 then Some (sao_return (ao_stack_alloc (stackalloc cparams p1) fn))
                 else None)
              with
              | Some l =>
                  let l' := [seq match i with
                                 | Some _ => false
                                 | None => true
                                 end | i <- l] in
                  if all id l' then None else Some l'
              | None => removereturn cparams p2 fn
              end.
  have: fn_keep_only rminfo fn vr2 = drop n vr2.
  + rewrite /fn_keep_only /rminfo ok_fn.
    set k := size (sao_return (ao_stack_alloc (stackalloc cparams p1) fn)).
    have ->: [seq match i with
           | Some _ => false
           | None => true
           end
         | i <- sao_return (ao_stack_alloc (stackalloc cparams p1) fn)]
         = nseq n false ++ nseq (k - n) true.
    + rewrite check_return. rewrite map_cat.
      apply f_equal2.
      + rewrite -map_comp.
        rewrite (proj1 (eq_in_map _ (fun _ => false) _)) //.
        rewrite map_const_nseq. by rewrite size_iota.
      apply map_nseq.
    case heq: all.
    + case: (n) heq => [|//]. move=> _. rewrite drop0. done.
    rewrite -{1}(cat_take_drop n vr2).
    rewrite keep_only_cat; last first.
    + rewrite size_takel; last by rewrite -heq5 heq4 -heq6.
      by rewrite size_nseq.
    rewrite keep_only_false; last first.
    + rewrite size_take_min. by apply geq_minl.
    rewrite keep_only_true. done.
  have: drop n vr1 = drop n vr2.
  + apply (@eq_from_nth _ (Vbool true)).
    + rewrite !size_drop. congruence.
    move=> i; rewrite size_drop => hi.
    have := Forall3_nth ok_vr2 None (Vbool true) (Vbool true).
    have hi': n + i < size (sao_return (ao_stack_alloc (stackalloc cparams p1) fn)).
    + rewrite heq4. by rewrite -ltn_subRL.
    move=> /(_ _ hi').
    rewrite check_return.
    rewrite nth_cat. rewrite size_map size_iota lt_nm_n.
    rewrite nth_nseq.
    rewrite (ltn_sub2rE _ (leq_addr _ _)). rewrite hi' /= !nth_drop. done.
  move=> h1 h2.
  have h3: List.Forall2 value_uincl (drop n vr) (drop n vr1).
  + apply (nth_Forall2 (a:=Vbool true) (b:=Vbool true)).
    + rewrite !size_drop. congruence.
    move=> i; rewrite size_drop => hi.
    rewrite !nth_drop.
    have hi': n + i < size vr.
    + by rewrite -ltn_subRL.
    have := Forall2_nth vr_vr1 (Vbool true) (Vbool true) hi'. done.
  + apply: (Forall2_trans value_uincl_trans h3).
    rewrite h1. rewrite -h2. apply vr2_vr3.
  rewrite /mem_unchanged_params'.
  move=> pr hvalid hnvalid hd.
  apply U => //.
  apply (nth_Forall3 None (Vbool true) (Vbool true)).
  + have [] := Forall3_size hargs. done.
  + have [] := Forall3_size hargs. done.
  move=> i hi.
  rewrite /disjoint_from_writable_param.
  move=> pi pr' ok_pi ok_pr' pi_w.
  have := Forall3_nth (hd _ get_fd) None (Vbool true) (Vbool true).
  rewrite size_map.
  have := check_params; rewrite all2E => /andP [/eqP -> _].
  move=> /(_ i hi).
  rewrite /disjoint_from_writable_param'.
  rewrite ok_pr'.
  (* ugly, we want an inhabitant of var_i *)
  have [x _]: exists x, oseq.onth fd.(f_params) i = Some x.
  + apply onth_not_default.
    move: check_params; rewrite all2E => /andP [/eqP -> _].
    rewrite (nth_not_default ok_pi); last by discriminate. done.
  have := all2_nth x None (n:=i) _ check_params.
  rewrite hi orbT => /(_ erefl) /eqP. rewrite ok_pi /= pi_w.
  rewrite (nth_map x); last first.
  + by have := check_params; rewrite all2E => /andP [/eqP -> _].
  move=> ->. move=> /(_ _ erefl erefl). done.
Qed.

Lemma compiler_back_end_meta entries (p: sprog) (tp: lprog) :
  compiler_back_end aparams cparams entries p = ok tp →
  [/\
     lp_rip tp = p.(p_extra).(sp_rip),
     lp_rsp tp = p.(p_extra).(sp_rsp) &
     lp_globs tp = p.(p_extra).(sp_globs)
  ].
Proof.
  rewrite /compiler_back_end; t_xrbindP => _ _ lp ok_lp.
  rewrite print_linearP => zp ok_zp.
  rewrite print_linearP => tp' ok_tp.
  rewrite print_linearP => ?; subst tp'.
  have! [<- [<- [<- _]]] := (tunnel_program_invariants ok_tp).
  have! [<- <- <-] := (stack_zeroization_lprog_invariants ok_zp).
  split.
  - exact: lp_ripE ok_lp.
  - exact: lp_rspE ok_lp.
  exact: lp_globsE ok_lp.
Qed.

Lemma compiler_back_end_to_asm_meta entries (p : sprog) (xp : asm_prog) :
  compiler_back_end_to_asm aparams cparams entries p = ok xp
  -> asm_globs xp = (sp_globs (p_extra p)).
Proof.
  rewrite /compiler_back_end_to_asm.
  t_xrbindP=> tp /compiler_back_end_meta[] _ _ <-.
  by move=> /assemble_progP [_ <-].
Qed.

(* The memory has an allocated stack region that is large enough to hold the local variables of the function and all functions it may call.
  The stack region is described by two pointers: [top-stack m] at the bottom and [root] (held in RSP) at the top
 *)
Definition enough_stack_space
  (xp : asm_prog) (fn : funname) (root : pointer) (m : mem) : Prop :=
  forall fd : asm_fundef,
    get_fundef xp.(asm_funcs) fn = Some fd
    -> let stk_sz := (wunsigned root - wunsigned (top_stack m))%Z in
       (0 <= asm_fd_total_stack fd <= stk_sz)%Z.

Lemma enough_stack_space_alloc_ok
  entries (sp : sprog) (xp : asm_prog) (fn : funname) (m m' : mem) :
  compiler_back_end_to_asm aparams cparams entries sp = ok xp
  -> fn \in entries
  -> (wunsigned (stack_limit m) <= wunsigned (top_stack m'))%Z
  -> enough_stack_space xp fn (top_stack m) m'
  -> alloc_ok sp fn m.
Proof.
  rewrite /compiler_back_end_to_asm /compiler_back_end.
  t_xrbindP => ? /allMP ok_export _ lp ok_lp.
  rewrite print_linearP => zp ok_zp.
  rewrite print_linearP => tp ok_tp.
  rewrite print_linearP => <- ok_xp /InP ok_fn M S.
  move => fd get_fd.
  move: ok_export => /(_ _ ok_fn); rewrite get_fd => /assertP export.
  split; last by rewrite export.
  have! get_lfd := (get_fundef_p' ok_lp get_fd).
  have! [zfd ok_zfd get_zfd] := (stack_zeroization_lprog_get_fundef ok_zp get_lfd).
  have! get_tfd := (get_fundef_tunnel_program ok_tp get_zfd).
  have! [fd' get_fd'] := (ok_get_fundef ok_xp get_tfd).
  case/assemble_fdI => _ _ [] ? [] ? [] ? [] _ _ _ ? _; subst fd'.
  move: get_fd' => /S /=.
  rewrite /lfd_total_stack /=.
  have [ _ <- _ _ _ _ <- _ <- _] /= := stack_zeroization_lfd_invariants ok_zfd.
  rewrite /allocatable_stack /sf_total_stack export.
  move: (wunsigned (stack_limit m)) (wunsigned (top_stack m)) (wunsigned (top_stack m')) M => L T T'.
  Lia.lia.
Qed.

Import sem_one_varmap.

Lemma compiler_back_endP
  entries
  (p : @sprog _pd _ _asmop)
  (tp : lprog)
  (rip : word Uptr)
  (scs : syscall_state)
  (m : mem)
  (scs' : syscall_state)
  (m' : mem)
  (fn : funname)
  args
  res :
  compiler_back_end aparams cparams entries p = ok tp →
  fn \in entries →
  psem.sem_call (dc:= direct_c) p rip scs m fn args scs' m' res →
  ∃ fd : lfundef,
    [/\
      get_fundef tp.(lp_funcs) fn = Some fd,
      fd.(lfd_export) &
      ∀ lm vm,
        vm.[vid tp.(lp_rsp)] = Vword (top_stack m) →
        match_mem m lm →
        List.Forall2 value_uincl args (map (λ x : var_i, vm.[x]) fd.(lfd_arg)) →
        vm.[vid tp.(lp_rip)] = Vword rip →
        vm_initialized_on vm (var_tmp aparams :: lfd_callee_saved fd) →
        allocatable_stack m (lfd_total_stack fd) ->
        ∃ vm' lm',
          [/\
            lsem_exportcall tp scs lm fn vm scs' lm' vm',
            match_mem m' lm',
            (cparams.(stack_zero_info) fn <> None ->
              (forall p, ~ validw m p U8 ->
                read lm' p U8 = read lm p U8 \/ read lm' p U8 = ok 0%R)
              /\
              (forall p,
                (wunsigned (stack_limit m) <= wunsigned p < wunsigned (stack_root m))%Z ->
                read lm' p U8 = read lm p U8 \/ read lm' p U8 = ok 0%R)) &
            List.Forall2 value_uincl res (map (λ x : var_i, vm'.[x]) fd.(lfd_res))
          ]
      ].
Proof.
  rewrite /compiler_back_end; t_xrbindP => ok_export checked_p lp ok_lp.
  rewrite print_linearP => zp ok_zp.
  rewrite print_linearP => tp' ok_tp.
  rewrite print_linearP => ?; subst tp'.
  move=> /InP ok_fn exec_p.
  set vtmp := var_tmp aparams.
  have vtmp_not_magic : ~~ Sv.mem vtmp (magic_variables p).
  - apply/Sv_memP; exact: var_tmp_not_magic checked_p.
  have p_call :
    sem_export_call p vtmp rip scs m fn args scs' m' res.
  - apply: (merge_varmaps_export_callP checked_p _ exec_p).
    move/allMP: ok_export => /(_ _ ok_fn).
    rewrite /is_export.
    case: get_fundef => // fd /assertP /is_RAnoneP Export.
    by exists fd.
  have :=
    linear_exportcallP
      (hap_hlip haparams)
      vtmp_not_magic
      ok_lp
      p_call.
  case => fd [] lfd [] get_fd get_lfd Export lp_call.
  have! [zfd ok_zfd get_zfd] := (stack_zeroization_lprog_get_fundef ok_zp get_lfd).
  exists (tunneling.tunnel_lfundef fn zfd).
  rewrite /lfd_total_stack /=.
  have [_ <- _ <- _ <- <- <- <- _] := stack_zeroization_lfd_invariants ok_zfd.
  rewrite Export.
  split=> //.
  - exact: get_fundef_tunnel_program ok_tp get_zfd.
  move=> tm tvm H0 H1 H3 H4 H5 H6.
  have H2 := get_var_is_allow_undefined tvm (lfd_arg lfd).
  have {lp_call} := lp_call tm tvm _ _ H1 H2 H3 _ H5.
  have! [-> -> _] := (stack_zeroization_lprog_invariants ok_zp).
  have! [-> [-> _]] := (tunnel_program_invariants ok_tp).
  have /= H6': (sf_stk_max (f_extra fd) + wsize_size (sf_align (f_extra fd)) - 1 <= wunsigned (top_stack m))%Z.
  + move: H6; rewrite /allocatable_stack.
    have := [elaborate (get_fundef_p' ok_lp get_fd)].
    rewrite get_lfd => -[->] /=.
    have /= := [elaborate (wunsigned_range (stack_limit m))].
    by Lia.lia.
  move => /(_ H0 H4 H6') [] vm' [] lm' [] res' [] lp_call ok_rsp' M' U'.
  rewrite get_var_is_allow_undefined => -[] <- res_res'.
  have ok_rsp'' : vm'.[vid (lp_rsp zp)] = Vword (top_stack m).
  + by have! [_ [-> _]] := (tunnel_program_invariants ok_tp).
  have /= H6'':
    (lfd_stk_max lfd + wsize_size (lfd_align lfd) - 1 <= wunsigned (top_stack m))%Z.
  + have := [elaborate (get_fundef_p' ok_lp get_fd)].
    by rewrite get_lfd => -[->] /=.
  set bottom :=
    (align_word (lfd_align lfd) (top_stack m) - wrepr Uptr (lfd_stk_max lfd))%R.
  have H6''':
    (0 <= wunsigned (align_word (lfd_align lfd) (top_stack m)) - lfd_stk_max lfd < wbase Uptr)%Z.
  + have: (0 <= lfd_stk_max lfd)%Z.
    + have := [elaborate (get_fundef_p' ok_lp get_fd)].
      rewrite get_lfd => -[->] /=.
      have! := (linearization_proof.checked_prog ok_lp get_fd).
      rewrite /check_fd /=; t_xrbindP=> _ _ ok_stk_sz _ _ _.
      case/and4P: ok_stk_sz => /ZleP stk_sz_pos /ZleP stk_extra_sz_pos _ /ZleP stk_frame_le_max.
      have := frame_size_bound stk_sz_pos stk_extra_sz_pos.
      by Lia.lia.
    have /= := [elaborate (align_word_range (lfd_align lfd) (top_stack m))].
    have /= := [elaborate (wunsigned_range (top_stack m))].
    by Lia.lia.
  have bottom_instack:
    zbetween
      (stack_limit m) (wunsigned (top_stack m) - wunsigned (stack_limit m))
      bottom (lfd_stk_max lfd).
  + rewrite /bottom /zbetween !zify.
    move: H6; rewrite /allocatable_stack.
    have /= ? := [elaborate (align_word_range (lfd_align lfd) (top_stack m))].
    rewrite wunsigned_sub //.
    by Lia.lia.
  have no_overflow_bottom: no_overflow bottom (lfd_stk_max lfd).
  + move: bottom_instack; rewrite /no_overflow /zbetween !zify.
    have /= := [elaborate (wunsigned_range (top_stack m))].
    by Lia.lia.
  have hvalid: ∀ pr, between bottom (lfd_stk_max lfd) pr U8 → validw tm pr U8.
  + move=> pr /(zbetween_trans bottom_instack).
    rewrite -/(between _ _ _ _) -pointer_range_between => hpr.
    apply H1.(valid_stk).
    apply /pointer_rangeP.
    apply: pointer_range_incl_r hpr.
    exact: top_stack_below_root.
  have [zm' [zvm' [zp_call heqvm hmm]]] :=
    stack_zeroization_lprogP (hap_hszp haparams) ok_zp lp_call ok_rsp''
      get_lfd H6'' hvalid.
  move: hmm; rewrite get_lfd -/bottom => hmm.

  exists zvm', zm'; split; cycle 1.
  - move: hmm.
    case: stack_zero_info => [[szs ows]|] /=; last first.
    + by move=> <-.
    move=> hmm.
    split.
    + move=> /= pr hb hval.
      have := M'.(read_incl_mem) hb hval.
      rewrite hmm.(read_untouched) //.
      apply not_between_U8_disjoint_zrange => //.
      move=> /(zbetween_trans bottom_instack).
      rewrite -/(between _ _ _ _) -pointer_range_between => /pointer_rangeP.
      have ss := sem_call_stack_stable_sprog exec_p.
      rewrite ss.(ss_limit) (ss_top_stack ss).
      have := [elaborate top_stack_below_root _ m']; rewrite -/(top_stack _) /=.
      by Lia.lia.
    + move=> pr w hb ok_w.
      have := M'.(read_incl_stk) hb ok_w.
      rewrite hmm.(read_untouched) //.
      apply not_between_U8_disjoint_zrange => //.
      move=> /(zbetween_trans bottom_instack).
      rewrite -/(between _ _ _ _) -pointer_range_between => /pointer_rangeP hpr.
      have /negP := (stack_region_is_free hpr); apply.
      rewrite (sem_call_validw_stable_sprog exec_p).
      exact: (readV ok_w).
    + by move=> pr /M'.(valid_incl); rewrite hmm.(valid_eq).
    move=> pr.
    rewrite -hmm.(valid_eq).
    by apply M'.(valid_stk).
  - move: hmm.
    case hszs: stack_zero_info => [[szs ows]|] //= hmm _.
    split.
    + move=> pr hnvalid.
      case hb: (between bottom (lfd_stk_max lfd) pr U8).
      + by right; rewrite (hmm.(read_zero) hb).
      left.
      rewrite -hmm.(read_untouched); last first.
      + apply not_between_U8_disjoint_zrange => //.
        by apply /negP /negPf.
      rewrite (U' _ hnvalid) //.
      have! := (linearization_proof.checked_prog ok_lp get_fd).
      rewrite /check_fd /=; t_xrbindP=> _ _ ok_stk_sz _ _ _.
      case/and4P: ok_stk_sz => /ZleP stk_sz_pos /ZleP stk_extra_sz_pos _ /ZleP stk_frame_le_max.
      rewrite /align_top_stack align_top_aligned; cycle 1.
      + by Lia.lia.
      + have := frame_size_bound stk_sz_pos stk_extra_sz_pos.
        have! := (wunsigned_range (top_stack m)).
        have /= := wsize_size_pos (sf_align (f_extra fd)).
        by Lia.lia.
      + move: ok_zfd; rewrite /stack_zeroization_lfd hszs Export /=.
        case: ZltP => [_|hle0].
        + rewrite /stack_zeroization_lfd_body; t_xrbindP=> halign _ _ _ _ _.
          move: Export halign.
          have := [elaborate (get_fundef_p' ok_lp get_fd)].
          rewrite get_lfd => -[->] /=.
          by rewrite /frame_size => ->.
        move=> _.
        have -> //: (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd) = 0)%Z.
        move: Export stk_frame_le_max hle0.
        have := [elaborate (get_fundef_p' ok_lp get_fd)].
        rewrite get_lfd => -[->] /=.
        rewrite /frame_size => ->.
        by Lia.lia.
      rewrite pointer_range_between.
      move/negP: hb H6'''; rewrite /bottom.
      have := [elaborate (get_fundef_p' ok_lp get_fd)].
      rewrite get_lfd => -[->] /= hb H6'''.
      rewrite wunsigned_sub //.
      by rewrite Z.sub_add_distr Z.sub_diag Z.sub_0_l Z.opp_involutive.
    move=> pr hstk.
    case hb: (between bottom (lfd_stk_max lfd) pr U8).
    + by right; rewrite (hmm.(read_zero) hb).
    left.
    rewrite -hmm.(read_untouched); last first.
    + apply not_between_U8_disjoint_zrange => //.
      by apply /negP /negPf.
    rewrite -U' //.
    + apply /negP. apply stack_region_is_free. rewrite -/(top_stack _).
      move: hb; rewrite /bottom.
      rewrite /between /zbetween.
      rewrite wunsigned_sub. 2:done. move=> /negP. rewrite !zify wsize8.
      have /= := [elaborate (align_word_range (lfd_align lfd) (top_stack m))].
      simpl in *. split. Lia.lia.
      have := align_word_range
      split. simpl in *. Lia.lia.
    tm
  - have <- //: [seq vm'.[x.(v_var)] | x <- lfd_res lfd]
                = [seq zvm'.[x.(v_var)] | x <- lfd_res lfd].
    apply map_ext.
    move=> x hin; apply heqvm.
    apply /sv_of_listP /in_map.
    by exists x.

  clear -zp_call ok_tp.
  case: zp_call => zfd get_zfd Export zp_exec ok_callee_saved.
  exists (tunneling.tunnel_lfundef fn zfd).
  - exact: get_fundef_tunnel_program ok_tp get_zfd.
  - exact: Export.
  have! [|] := (lsem_run_tunnel_program ok_tp zp_exec).
  - by exists zfd.
  - move => tp_exec _.
    rewrite /ls_export_final size_tunnel_lcmd.
    exact: tp_exec.
  exact: ok_callee_saved.
Qed.

Lemma compiler_back_end_to_asmP
  entries
  (p : @sprog _pd _ _asmop)
  (xp : asm_prog)
  (rip : word Uptr)
  scs (m : mem) scs' (m' : mem)
  (fn: funname)
  args
  res :
  compiler_back_end_to_asm aparams cparams entries p = ok xp
  -> fn \in entries
  -> psem.sem_call (dc:=direct_c) p rip scs m fn args scs' m' res
  -> exists xd : asm_fundef,
      [/\ get_fundef (asm_funcs xp) fn = Some xd
        , asm_fd_export xd
        & forall xm,
               xm.(asm_scs) = scs
            -> xm.(asm_rip) = rip
            -> asm_reg xm ad_rsp = top_stack m
            -> match_mem m xm.(asm_mem)
            -> List.Forall2 value_uincl args (get_typed_reg_values xm xd.(asm_fd_arg))
            -> allocatable_stack m xd.(asm_fd_total_stack)
            -> exists xm',
                [/\ asmsem_exportcall xp fn xm xm'
                  , match_mem m' xm'.(asm_mem), xm'.(asm_scs) = scs'
                  , (cparams.(stack_zero_info) fn <> None ->
                      forall p, ~ validw m p U8 ->
                       read xm'.(asm_mem) p U8 = read xm.(asm_mem) p U8
                       \/ read xm'.(asm_mem) p U8 = ok 0%R)
                  & List.Forall2 value_uincl res (get_typed_reg_values xm' xd.(asm_fd_res))
                ]
      ].
Proof.
  rewrite /compiler_back_end_to_asm.
  t_xrbindP=> lp ok_lp ok_xp.
  move=> ok_fn p_call.
  have [fd [] ok_fd fd_export lp_call] := compiler_back_endP ok_lp ok_fn p_call.
  have [xd ->] := ok_get_fundef ok_xp ok_fd.
  have [disj_rip ok_lp_rsp ok_globs get_xfun] := assemble_progP ok_xp.
  case/assemble_fdI =>
    rsp_not_arg /allP ok_callee_saved
    [] xbody
    [] xargs
    [] xres
    [] ok_xbody ok_xargs ok_xres
    -> {xd}.
  eexists; split; first reflexivity.
  - by rewrite fd_export.
  move=> xm ok_scs ok_rip ok_rsp M /= ok_args hallocatable.

  set s :=
    estate_of_asm_mem
      (top_stack m)
      (lp_rip lp)
      (lp_rsp lp)
      xm.

  assert (LM :=
    lom_eqv_estate_of_asm_mem
      (top_stack m)
      (lp_rsp lp)
      xm
      disj_rip).

  assert (XM :=
    get_var_vmap_of_asm_mem
      (top_stack m)
      (lp_rip lp)
      (lp_rsp lp)
      xm).

  have := lp_call _ _ _ M.
  move=> /(_ (vmap_of_asm_mem (top_stack m) (lp_rip lp) (lp_rsp lp) xm)).
  case.
  - assert (Hrsp := XM (ARReg ad_rsp)).
    move: Hrsp.
    by rewrite /= /to_var /= ok_lp_rsp /rtype /= ok_rsp.
  - have -> //:
      [seq (vmap_of_asm_mem (top_stack m) (lp_rip lp) (lp_rsp lp) xm).[v_var x] | x <- lfd_arg fd] =
      (get_typed_reg_values xm xargs).
    elim: (lfd_arg fd) (xargs) ok_xargs => //= [ | [x ?] xs hrec]; t_xrbindP; first by move=> _ <-.
    by move=> ?? h ? /hrec -> <- /=; rewrite -XM (asm_typed_reg_of_varI h).
  - case: LM => _ _ Y _ _ _ _.
    by move: Y => /= ->; rewrite ok_rip.
  - move => /=.
    apply/andP; split.
    + rewrite /var_tmp.
      have [tmp_r htmp] := ok_lip_tmp haparams.
      rewrite -(of_identI htmp) /get_var (XM (ARReg _)).
      by rewrite /get_typed_reg_value /= truncate_word_u.

    apply/allP => x /ok_callee_saved hin.
    have [r ->]: exists2 r, x = (var_of_asm_typed_reg r) & vtype x != sbool.
    + by move/andP: hin => [->] /is_okP [] r /asm_typed_reg_of_varI ->; exists r.
    rewrite /get_var XM /=.
    by case: r => //= ?; rewrite truncate_word_u.
  - exact: hallocatable.
  move=>
      vm'
      [] lm'
      [] {} lp_call M' hzero res_res'.
  subst scs.
  have :=
    asm_gen_exportcall
      (hap_hagp haparams)
      ok_xp
      lp_call
      _
      LM.
  case.
  - apply/allP => ? /mapP [] r hin ->.
    rewrite /get_var (XM r) /=.
    assert (H:= callee_saved_not_bool); move/allP: H => /(_ _ hin) {hin}.
    by case: r => //= r _; rewrite truncate_word_u.

  move=> xm' xp_call LM'.
  have : List.Forall2 value_uincl res (get_typed_reg_values xm' xres).
  + elim: (lfd_res fd) (xres) ok_xres (res) res_res' => [ | [x ?] xs hrec] //=; t_xrbindP.
    + by move=> ? <- res' h; inversion_clear h => /=.
    move=> ? r h ? /hrec{}hrec <- res' /List_Forall2_inv; case: res' => // v res' [hr /hrec] /=.
    apply/List.Forall2_cons/(value_uincl_trans hr).
    rewrite (asm_typed_reg_of_varI h) /=.
    case: LM' => /= _ _ _ _ R RX X F.
    case: (r) => //=.
  exists xm'; split => //.
  - by case: LM' => /= _ <-.
  - by case: LM' => <-.
  move=> hszs pr hnvalid.
  case: LM' => /= _ <- _ _ _ _ _ _.
  by apply (hzero hszs pr hnvalid).
Qed.

(* Agreement relation between source and target memories.
   Expressed in a way that streamlines the composition of compiler-correctness theorems (front-end and back-end).
  TODO: There might be an equivalent definition that is clearer.
*)

Record mem_agreement_with_ghost (m m': mem) (gd: pointer) (data: seq u8) (ma_ghost: mem) : Prop :=
  { ma_extend_mem : extend_mem m ma_ghost gd data
  ; ma_match_mem : match_mem ma_ghost m'
  ; ma_stack_stable : stack_stable m ma_ghost
  ; ma_stack_range : (wunsigned (stack_limit ma_ghost) <= wunsigned (top_stack m'))%Z
  }.

Definition mem_agreement (m m': mem) (gd: pointer) (data: seq u8) : Prop :=
  ∃ ma_ghost, mem_agreement_with_ghost m m' gd data ma_ghost.

Definition wf_args_asm (glob_data : seq u8) (rip : word Uptr) (m1 m2 : mem) (p : uprog) (xp : asm_prog) 
  (fn : funname) (va va' : seq value) :=
  ∀ (glob_size := Z.of_nat (size glob_data)) (fd : _fundef extra_fun_t),
    get_fundef (p_funcs p) fn = Some fd
    → ∀ xd,
        get_fundef (asm_funcs xp) fn = Some xd
        → let l1 := [seq reg_ptr_writable_status i | i <- f_params fd] in
          let l2 := asm_fd_align_args xd in
          Forall4 (wf_arg' glob_size rip m1 m2) l1 l2 va va'.

Lemma inlining_get_fundef to_keep p p' fn fd :
  inlining cparams to_keep p = ok p' ->
  fn \in to_keep ->
  get_fundef p.(p_funcs) fn = Some fd ->
  exists fd', get_fundef p'.(p_funcs) fn = Some fd'.
Proof.
  rewrite /inlining.
  t_xrbindP=> pi ok_pi pd.
  rewrite !print_uprogP => ok_pd <- {p'} ok_fn get_fd.

  have [fdi [get_fdi _]] := [elaborate inline_prog_err_get_fundef ok_pi get_fd].
  have get_fdp := [elaborate dead_calls_err_seq_get_fundef' ok_pd ok_fn get_fdi].
  by exists fdi.
Qed.

Lemma unroll_loop_get_fundef p p' fn fd :
  unroll_loop aparams.(ap_is_move_op) p = ok p' ->
  get_fundef p.(p_funcs) fn = Some fd ->
  exists fd', get_fundef p'.(p_funcs) fn = Some fd'.
Proof.
  rewrite /unroll_loop; t_xrbindP.
  elim: Loop.nb p fd => //= n Hn p fd p1 ok_p1.
  case e: unroll_prog => [ p2 [] ]; last first.
  { move/ok_inj => <- {p' n Hn} get_fd.
    have [fd' _ get_fd'] := [elaborate
      dead_code_prog_tokeep_get_fundef (pT:=progUnit) ok_p1 (const_prop_prog_get_fundef get_fd)].
    by exists fd'. }
  t_xrbindP => p3 ok_p3 ok_p' get_fd.
  have [fd' _ get_fd'] := [elaborate
      dead_code_prog_tokeep_get_fundef (pT:=progUnit) ok_p1 (const_prop_prog_get_fundef get_fd)].
  have := p'_get_fundef get_fd'.
  rewrite e [get_fundef _ _]/= => get_fd''.
  exact: (Hn _ _ _ ok_p3 ok_p' get_fd'').
Qed.

Lemma live_range_splitting_get_fundef p p' fn fd :
  live_range_splitting aparams cparams p = ok p' ->
  get_fundef p.(p_funcs) fn = Some fd ->
  exists fd', get_fundef p'.(p_funcs) fn = Some fd'.
Proof.
  rewrite /live_range_splitting; t_xrbindP.
  rewrite !print_uprogP => ok_p' pa ok_pa.
  rewrite print_uprogP => ? get_fd; subst pa.
  have [fd' [get_fd' _]] := [elaborate allocation_proof.all_checked ok_p' get_fd].
  have [fd'' _ get_fd''] := [elaborate
    dead_code_prog_tokeep_get_fundef (pT:=progUnit) ok_pa get_fd'].
  by exists fd''.
Qed.

(* unused *)
Lemma compiler_first_part_get_fundef entries p p' fn fd :
  compiler_first_part aparams cparams entries p = ok p' ->
  fn \in entries ->
  get_fundef p.(p_funcs) fn = Some fd ->
  exists fd', get_fundef p'.(p_funcs) fn = Some fd'.
Proof.
  rewrite /compiler_first_part; t_xrbindP => pa0.
  rewrite print_uprogP => ok_pa0 pb.
  rewrite print_uprogP => ok_pb pa.
  rewrite print_uprogP => ok_pa pc ok_pc.
  rewrite !print_uprogP => pd ok_pd.
  rewrite !print_uprogP => pe ok_pe.
  rewrite !print_uprogP => pf ok_pf.
  rewrite !print_uprogP => pg ok_pg.
  rewrite !print_uprogP => ph ok_ph pi ok_pi.
  rewrite !print_uprogP => ok_fvars pj ok_pj pp.
  rewrite !print_uprogP => ok_pp <- {p'} ok_fn get_fd.

  have [fda0 _ get_fda0] := [elaborate array_copy_proof.all_checked ok_pa0 get_fd].
  have [fdb [get_fdb _]] := [elaborate spill_get_fundef ok_pb (add_init_prog_get_fundef get_fda0)].
  have [fda get_fda] := inlining_get_fundef ok_pa ok_fn get_fdb.
  have [fdc get_fdc] := unroll_loop_get_fundef ok_pc get_fda.
  have get_fdd := [elaborate dead_calls_err_seq_get_fundef' ok_pd ok_fn get_fdc].
  have [fde get_fde] := live_range_splitting_get_fundef ok_pe get_fdd.
  have [fdf [get_fdf _]] := [elaborate
    makereference_prog_get_fundef ok_pf (remove_init_get_fundef get_fde)].
  have [fdg get_fdg] := [elaborate expand_prog_get_fundef ok_pg get_fdf].
  have [fdh get_fdh] := live_range_splitting_get_fundef ok_ph get_fdg.
  have [fdi get_fdi] := [elaborate RGP.remove_glob_prog_get_fundef ok_pi get_fdh].
  have := [elaborate lower_slh_prog_get_fundef ok_pj (fn:=fn)].
  rewrite get_map_prog. rewrite get_fdi /=.
  move=> /(_ _ erefl) [fdj [get_fdj _]].
  have [fdp _ get_fdp] := [elaborate propagate_inline_proof.all_checked ok_pp get_fdj].
  by exists fdp.
Qed.

Lemma compiler_back_end_to_asm_get_fundef entries sp xp fn :
  compiler_back_end_to_asm aparams cparams entries sp = ok xp ->
  fn \in entries ->
  exists sfd xd, [/\
    get_fundef sp.(p_funcs) fn = Some sfd,
    get_fundef xp.(asm_funcs) fn = Some xd,
    xd.(asm_fd_export) &
    sfd.(f_extra).(sf_align_args) = xd.(asm_fd_align_args)].
Proof.
  move=> ok_xp ok_fn.
  move: ok_xp; rewrite /compiler_back_end_to_asm.
  t_xrbindP=> lp ok_lp ok_xp.
  move: ok_lp; rewrite /compiler_back_end.
  t_xrbindP=> hcheck _ lp1 ok_lp1 lp2.
  rewrite print_linearP => ok_lp2 lp3.
  rewrite print_linearP => ok_lp3.
  rewrite print_linearP => ?; subst lp.

  have [sfd [get_sfd ranone]]:
    exists sfd,
      get_fundef sp.(p_funcs) fn = Some sfd
      /\ is_RAnone sfd.(f_extra).(sf_return_address).
  + move: hcheck; rewrite /check_export.
    have /InP ok_fn' := ok_fn.
    move=> /allMP -/(_ fn ok_fn').
    case: get_fundef => //.
    t_xrbindP=> sfd ranone.
    by exists sfd.

  have get_lfd1 := [elaborate get_fundef_p' ok_lp1 get_sfd].
  have [lfd2 ok_lfd2 get_lfd2] := [elaborate
    stack_zeroization_lprog_get_fundef ok_lp2 get_lfd1].
  have get_lfd3 := [elaborate get_fundef_tunnel_program ok_lp3 get_lfd2].
  have [xd get_xd ok_xd] := [elaborate ok_get_fundef ok_xp get_lfd3].

  exists sfd, xd.
  move/assemble_fdI: ok_xd => [_ _ [_ [_ [_ [_ _ _ {-2}-> _]]]]] /=.
  move/stack_zeroization_lfd_invariants: ok_lfd2 => [_ _ _ _ _ _ <- _ _ [_ <-]] /=.
  by split.
Qed.

Lemma read_error m p ws e :
  validw m p ws ->
  read m p ws = Error e ->
  e = ErrAddrInvalid.
Proof.
Local Opaque wsize_size.
  rewrite /validw /read.
  move=> /andP [-> _] /=.
  apply ziota_ind => //= i l _ ih.
  case h1: get => [w|e'] /=.
  + by move: ih; case: mapM.
  move=> [<-].
  exact: (Memory.get_error h1).
Local Transparent wsize_size.
Qed.

Lemma test m1 m2 :
  (forall p, validw m1 p U8 -> read m1 p U8 = read m2 p U8) ->
  forall p w, read m1 p U8 = ok w -> read m2 p U8 = ok w.
Proof. by move=> h p w /dup[] /(@readV _ _ _ _ _) /h <-. Qed.

Lemma test' m1 m2 :
  (forall p w, read m1 p U8 = ok w -> read m2 p U8 = ok w) ->
  (forall p, validw m1 p U8 -> read m1 p U8 = read m2 p U8).
Proof.
  (* semble faux en toute généralité *)
  (* si une valeur est initialisée dans m2 mais pas dans m1 *)
Abort.

Lemma compile_prog_to_asmP
  entries
  (p : prog)
  (xp : asm_prog)
  scs (m : mem) scs' (m' : mem)
  (fn: funname)
  va
  vr
  xm :
  compile_prog_to_asm aparams cparams entries p = ok xp
  -> fn \in entries
  -> psem.sem_call (dc:= indirect_c) (wsw:=nosubword) p tt scs m fn va scs' m' vr
  -> forall mi,
     mem_agreement_with_ghost m (asm_mem xm) (asm_rip xm) (asm_globs xp) mi
  -> enough_stack_space xp fn (top_stack m) (asm_mem xm)
  -> exists xd : asm_fundef,
      [/\
         get_fundef (asm_funcs xp) fn = Some xd
        , asm_fd_export xd
        &   asm_scs xm = scs
            -> asm_reg xm ad_rsp = top_stack m
(*             -> List.Forall2 value_uincl va (get_typed_reg_values xm (asm_fd_arg xd)) *)
            -> wf_args_asm (asm_globs xp) (asm_rip xm) m mi p xp fn va (get_typed_reg_values xm (asm_fd_arg xd))
            -> disjoint_values'' p fn va (get_typed_reg_values xm (asm_fd_arg xd))
            -> exists xm',
                [/\ asmsem_exportcall xp fn xm xm'
                  , mem_agreement m' (asm_mem xm') (asm_rip xm') (asm_globs xp), asm_scs xm' = scs'
                  , (cparams.(stack_zero_info) fn <> None ->
                      forall pr, ~ validw m pr U8 ->
                        disjoint_from_writable_params' p fn pr va (get_typed_reg_values xm (asm_fd_arg xd)) ->
                        read xm'.(asm_mem) pr U8 = read xm.(asm_mem) pr U8
                        \/ read xm'.(asm_mem) pr U8 = ok 0%R)
                  & List.Forall2 value_uincl vr (get_typed_reg_values xm' (asm_fd_res xd))
                ]
      ].
Proof.
  rewrite /compile_prog_to_asm; t_xrbindP => sp ok_sp ok_xp ok_fn p_call mi.
  have -> := compiler_back_end_to_asm_meta ok_xp.
  case=> /= mi1 mi2 mi3 mi4.
  rewrite (ss_top_stack mi3).
  move=> /dup[] henough /(enough_stack_space_alloc_ok ok_xp ok_fn mi4) ok_mi.
  have [sfd [xd [get_sfd get_xd xd_export align_args_eq]]] :=
    compiler_back_end_to_asm_get_fundef ok_xp ok_fn.
  exists xd; split=> //.
  move=> ok_scs ok_rsp va_wf va_disjoint.
  have h: wf_args' (sp_globs (p_extra sp)) (asm_rip xm) m mi p sp fn va (get_typed_reg_values xm (asm_fd_arg xd)).
  + move=> fd get_fd. rewrite get_sfd. move=> _ [<-].
    move: va_wf; rewrite /wf_args_asm.
    move=> /(_ fd get_fd xd get_xd).
    by rewrite align_args_eq.
  have := compiler_front_endP ok_sp ok_fn p_call mi1 h va_disjoint
    (enough_stack_space_alloc_ok ok_xp ok_fn mi4 henough).
  case => vr' [] mi' [] vr_vr' sp_call m1 U.
  have := compiler_back_end_to_asmP ok_xp ok_fn sp_call.
  rewrite get_xd.
  case => _ [] [<-] _ /(_ _ _ erefl _ mi2) xp_call.
  have hallocatable: allocatable_stack mi (asm_fd_total_stack xd).
  + rewrite /allocatable_stack.
    by have /= := henough _ get_xd; Lia.lia.
  have := xp_call ok_scs ok_rsp (List_Forall2_refl _ value_uincl_refl) hallocatable.
  case => xm' [] {} xp_call m2 ok_scs' hzero vr'_res'.
  exists xm'; split => //.
  + case: xp_call => _ _ _ /= _ /asmsem_invariantP /= xm_xm' _.
    exists mi'; split.
    - rewrite -(asmsem_invariant_rip xm_xm').
      exact: m1.
    - exact: m2.
    - transitivity mi;
        last exact: (sem_call_stack_stable_sprog sp_call).
      transitivity m; last exact: mi3.
      symmetry. exact: (sem_call_stack_stable_uprog p_call).
    rewrite
      -(ss_limit (sem_call_stack_stable_sprog sp_call))
      -(ss_top_stack (asmsem_invariant_stack_stable xm_xm')).
    exact: mi4.
  + move=> hszs pr hnvalid hdisj.
    change reg_size with Uptr in pr.
    case: (@idP (validw mi pr U8)).
    + move=> hvalid.
      have := U _ hvalid hnvalid hdisj.
      case:
        (boolP
          ((wunsigned (stack_limit mi) <=? wunsigned pr)
          && (wunsigned pr <? wunsigned (stack_root mi)))%Z);
        rewrite !zify => hb.
      + have := m2.(read_incl_stk).
        have [<- <- _] := sem_call_stack_stable_sprog sp_call.
        move=> /(_ _ _ hb).
        read (asm_mem xm') pr U8 = read (asm_mem xm) pr U8 \/
          read () pr U8 = match_mem memory
      have := mi2.(read_incl_mem) hb hvalid.
      have := m2.(read_incl_mem).
      have [<- <- _] := sem_call_stack_stable_sprog sp_call.
      move=> /(_ _ hb).
      have <- := sem_call_validw_stable_sprog sp_call.
      move=> /(_ hvalid).
      move=> -> -> ?.
      by left.
    move=> hnvalid'.
    by apply hzero.
      hzero
        rewrite mi3.( hb hvalid.
        admit.
      hzero
        
      have: disjoint_from_writable_params' p fn pr va (get_typed_reg_values xm (asm_fd_arg xd))
       \/ ~ disjoint_from_writable_params' p fn pr va (get_typed_reg_values xm (asm_fd_arg xd)).
      + admit.
      move=> [hdisj|hndisj].
      + have := U _ hvalid hnvalid hdisj.
        case hread: (read mi pr U8) => [w|e].
        + move=> /esym hread'.
          rewrite (mi2.(read_incl) hread).
          rewrite (m2.(read_incl) hread').
          by left.
        admit. (* ? *)
      va
        match_mem
        match_mem
      Search read validw. Search get. Print Instances coreMem. Search Memory.CM read inside low_memory. memory_model.addE
      read ErrOob
      rewrite {1}/read /=. rewrite is_align8 /=. rewrite /get /=.
      read
    have := mi2.(read_incl). -> := mi1.(em_read_new) hi.
      by have /m2.(read_incl) -> := m1.(em_read_new) hi.
    case h: (validw mi pr U8).
    have := mi1.(em_valid). move=> /(_ pr).
    case: (@idP (between _ _ _ _)) => [hb|_].
    + move=> _; left.
      have [i [hi ->]]:
        exists i,
          (0 <= i < (Z.of_nat (size (sp_globs (p_extra sp)))))%Z
          /\ (pr = asm_rip xm + wrepr _ i)%R.
      + exists (wunsigned pr - wunsigned (asm_rip xm))%Z; split; last first.
        + rewrite wrepr_sub !wrepr_unsigned.
          by rewrite GRing.addrC GRing.subrK.
        move: hb; rewrite /between /zbetween wsize8 !zify /=.
        by Lia.lia.
      have /mi2.(read_incl) -> := mi1.(em_read_new) hi.
      by have /m2.(read_incl) -> := m1.(em_read_new) hi.
    rewrite orbF => hvalideq.
    apply (hzero hszs pr).
    admit.
  
Qed.

End PROOF.
