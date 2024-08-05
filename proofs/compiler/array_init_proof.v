(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem compiler_util.
Require Export array_init.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

Section Section.

Context {pT: progT} {sCP: semCallParams}.

Section REMOVE_INIT.
  
  Context (is_reg_array: var -> bool) (p : prog) (ev: extra_val_t).
  Notation gd := (p_globs p).

  Notation p' := (remove_init_prog is_reg_array p).

  Let Pi s1 (i:instr) s2 :=
    forall vm1,
      evm s1 <=1 vm1 ->
      exists2 vm2,
        sem p' ev (with_vm s1 vm1) (remove_init_i is_reg_array i) (with_vm s2 vm2) &
        evm s2 <=1 vm2.

  Let Pi_r s1 (i:instr_r) s2 := forall ii, Pi s1 (MkI ii i) s2.

  Let Pc s1 (c:cmd) s2 :=
    forall vm1,
      evm s1 <=1 vm1 ->
      exists2 vm2,
        sem p' ev (with_vm s1 vm1) (remove_init_c is_reg_array c) (with_vm s2 vm2) &
        evm s2 <=1 vm2.

  Let Pfor (i:var_i) vs s1 c s2 :=
    forall vm1,
      evm s1 <=1 vm1 ->
      exists2 vm2,
        sem_for p' ev i vs (with_vm s1 vm1) (remove_init_c is_reg_array c) (with_vm s2 vm2) &
        evm s2 <=1 vm2.

  Let Pfun scs m fn vargs scs' m' vres :=
    forall vargs',
    List.Forall2 value_uincl vargs vargs' ->
    exists vres', sem_call p' ev scs m fn vargs' scs' m' vres' /\
      List.Forall2 value_uincl vres vres'.

  Local Lemma Rnil : sem_Ind_nil Pc.
  Proof. by move=> s vm1 Hvm1;exists vm1 => //;constructor. Qed.

  Local Lemma Rcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ Hi _ Hc vm1 /(Hi _) [vm2 Hsi] /(Hc _) [vm3] Hsc ?.
    by exists vm3 =>//=; apply: sem_app Hsc.
  Qed.

  Local Lemma RmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by move=> ii i s1 s2 _ Hi vm1 /(Hi ii) [vm2] ??;exists vm2. Qed.

  Lemma assgn_uincl s1 s2 e v ty v' vm1 x ii tag:  
    sem_pexpr true gd s1 e = ok v ->
    truncate_val ty v = ok v' -> 
    write_lval true gd x v' s1 = ok s2 ->
    evm s1 <=1 vm1 ->
    exists2 vm2 : Vm.t,
      sem p' ev (with_vm s1 vm1) [:: MkI ii (Cassgn x tag ty e)] (with_vm s2 vm2) &
      evm s2 <=1 vm2.
  Proof.
    move=> Hse hsub hwr Hvm1. 
    have [z' Hz' Hz] := sem_pexpr_uincl Hvm1 Hse.
    have [z1 htr Uz1]:= value_uincl_truncate Hz hsub.
    have [vm2 Hw ?]:= write_uincl Hvm1 Uz1 hwr.
    exists vm2 => //; apply sem_seq1;constructor;econstructor;eauto.
  Qed.

  Local Lemma Rasgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' Hse hsub hwr ii vm1 /=; case: ifP; last first.
    + by move=> _; apply: assgn_uincl Hse hsub hwr.
    case: ifP; last first.
    + by move=> _ _; apply: assgn_uincl Hse hsub hwr.
    move=> _ /is_array_initP [n e1];subst e.
    case: Hse => ?; subst v.
    move: hsub;rewrite /truncate_val;case: ty => //= nty.
    t_xrbindP => empty /WArray.cast_empty_ok ??; subst v' empty.
    case: x hwr => [vi t | [x xi] | al ws x e | al aa ws x e | aa ws len [x xi] e] /=.
    + by move=> /write_noneP [->];exists vm1 => //;constructor.
    + move=> /write_varP_arr [/=hty _ _ ->] /= hsub.
      exists vm1; first by constructor.
      apply vm_uincl_set_l => //=.
      have /compat_valEl := Vm.getP vm1 x; rewrite -hty eqxx => -[t' ->].
      by apply: WArray.uincl_empty.
    + by t_xrbindP.
    + by apply: on_arr_varP => ???; t_xrbindP.
    apply: on_arr_varP => /= tlen t ?; t_xrbindP => hg i vi hvi hi _ /WArray.cast_empty_ok ->.
    move => t1 ht1 /write_varP_arr [/= hty _ _ ->] hsub.
    exists vm1; first by constructor.
    apply vm_uincl_set_l => //=.
    move: hg; rewrite /get_var; t_xrbindP => _ hx.
    have := hsub x; rewrite hx -hty eqxx => /value_uinclE [t2 -> hu].
    split => //.
    move=> k w; rewrite (WArray.set_sub_get8 ht1) /=; case: ifP => ?.
    + by rewrite WArray.get_empty; case: ifP.
    by apply hu.
  Qed.

  Local Lemma Ropn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es H ii vm1 Hvm1; move: H;rewrite /sem_sopn; t_xrbindP => rs vs.
    move=> /(sem_pexprs_uincl Hvm1) [] vs' H1 H2.
    move=> /(vuincl_exec_opn H2) [] rs' H3 H4.
    move=> /(writes_uincl Hvm1 H4) [] vm2 Hw ?; exists vm2 => //.
    by apply sem_seq1;constructor;constructor;rewrite /sem_sopn H1 /= H3.
  Qed.

  Local Lemma Rsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> s1 scs m s2 o xs es ves vs he hsys hw ii vm1 uvm.
    have [ves' he' uves] := sem_pexprs_uincl uvm he.
    have [vs' hsys' uvs]:= exec_syscallP hsys uves.
    have [vm2 hw'] := writes_uincl (s1 := with_scs (with_mem s1 m) scs) uvm uvs hw.
    exists vm2 => //=; apply sem_seq1; constructor; econstructor; eauto.
  Qed.

  Local Lemma Rif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H _ Hc ii vm1 Hvm1.
    have [v' H1 /value_uinclE ?] := sem_pexpr_uincl Hvm1 H; subst.
    have [vm2 ??]:= Hc _ Hvm1; exists vm2 => //.
    by apply sem_seq1; constructor; apply Eif_true; rewrite // H1.
  Qed.

  Local Lemma Rif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H _ Hc ii vm1 Hvm1.
    have [v' H1 /value_uinclE ?] := sem_pexpr_uincl Hvm1 H;subst.
    have [vm2 ??]:= Hc _ Hvm1; exists vm2 => //.
    by apply sem_seq1;constructor;apply Eif_false;rewrite // H1.
  Qed.

  Local Lemma Rwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' _ Hc + _ Hc' _ Hw ii vm1 Hvm1.
    have [vm2 Hs2 Hvm2] := Hc _ Hvm1.
    move=> /(sem_pexpr_uincl Hvm2) [] v' H1 /value_uinclE H2; subst.
    have [vm3 H4 Hvm3]:= Hc' _ Hvm2.
    have [vm4 Hsem ?] := Hw ii _ Hvm3; exists vm4 => //=.
    apply sem_seq1;constructor;eapply Ewhile_true;eauto.
    by case/semE: Hsem => si [] /sem_IE ? /semE ?; subst si.
  Qed.

  Local Lemma Rwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' _ Hc H ii vm1 Hvm1; move: H.
    have [vm2 Hs2 Hvm2] := Hc _ Hvm1.
    move=> /(sem_pexpr_uincl Hvm2) [] v' H1 /value_uinclE ?;subst.
    by exists vm2 => //=;apply sem_seq1;constructor;apply: Ewhile_false=> //;rewrite H1.
  Qed.

  Local Lemma Rfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi H H' _ Hfor ii vm1 Hvm1.
    have [? H1 /value_uinclE H2]:= sem_pexpr_uincl Hvm1 H; subst.
    have [? H3 /value_uinclE H4]:= sem_pexpr_uincl Hvm1 H'; subst.
    have [vm2 ??]:= Hfor _ Hvm1; exists vm2 => //=.
    by apply sem_seq1;constructor; econstructor; eauto; rewrite ?H1 ?H3.
  Qed.

  Local Lemma Rfor_nil : sem_Ind_for_nil Pfor.
  Proof. by move=> s i c vm1 Hvm1; exists vm1 => //; constructor. Qed.

  Local Lemma Rfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hi _ Hc _ Hf vm1 Hvm1.
    have [vm1' Hi' /Hc [vm2 Hsc /Hf [vm3 Hsf Hvm3]]] := write_var_uincl Hvm1 (value_uincl_refl _) Hi.
    exists vm3 => //; econstructor; eauto.
  Qed.

  Local Lemma Rcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 xs fn args vargs vs Hargs Hcall Hfd Hxs ii' vm1 Hvm1.
    have [vargs' Hsa /Hfd [vres' [Hc Hvres]]]:= sem_pexprs_uincl Hvm1 Hargs.
    have /(_ _ Hvm1) [vm2' Hw ?] := writes_uincl _ Hvres Hxs.
    exists vm2' => //=; apply: sem_seq1; constructor; econstructor; eauto.
  Qed.

  Local Lemma Rproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn fd vargs vargs' s0 s1 s2 vres vres' Hget Htin Hi Hargs Hsem Hrec Hmap Htout Hsys Hfi vargs1' Uargs.
    have [vargs1 Htin1 Uargs1]:= mapM2_dc_truncate_val Htin Uargs.
    have [vm1 /= ]:= write_vars_uincl (vm_uincl_refl _) Uargs1 Hargs.
    rewrite with_vm_same => Hargs' Hvm1.
    have [vm2' /= Hsem' Uvm2]:= Hrec _ Hvm1.
    have [vres1 Hvres Hsub] := get_var_is_uincl Uvm2 Hmap.
    have [vres1' Htout1 Ures1]:= mapM2_dc_truncate_val Htout Hsub.
    exists vres1'; split => //.
    apply: (EcallRun (f:=remove_init_fd is_reg_array fd)); eauto.
    by rewrite /p' /remove_init_prog get_map_prog Hget.
  Qed.

  Lemma remove_init_fdP f scs mem scs' mem' va va' vr:
    List.Forall2 value_uincl va va' ->
    sem_call p ev scs mem f va scs' mem' vr ->
    exists vr', sem_call p' ev scs mem f va' scs' mem' vr' /\ List.Forall2 value_uincl vr vr'.
  Proof.
    move=> hall hsem.
    exact:
      (sem_call_Ind
         Rnil
         Rcons
         RmkI
         Rasgn
         Ropn
         Rsyscall
         Rif_true
         Rif_false
         Rwhile_true
         Rwhile_false
         Rfor
         Rfor_nil
         Rfor_cons
         Rcall
         Rproc
         hsem
         _
         hall).
  Qed.

End REMOVE_INIT.

End Section.

Lemma remove_init_fdPu is_reg_array (p : uprog) ev f scs mem scs' mem' va va' vr:
   List.Forall2 value_uincl va va' ->
   sem_call p ev scs mem f va scs' mem' vr ->
   exists vr' : seq value,
     sem_call (remove_init_prog is_reg_array p) ev scs mem f va' scs' mem' vr' /\ List.Forall2 value_uincl vr vr'.
Proof. apply remove_init_fdP; apply wf_initu. Qed.

Lemma remove_init_fdPs is_reg_array (p : sprog) ev f scs mem scs' mem' va va' vr:
   List.Forall2 value_uincl va va' ->
   sem_call p ev scs mem f va scs' mem' vr ->
   exists vr' : seq value,
     sem_call (remove_init_prog is_reg_array p) ev scs mem f va' scs' mem' vr' /\ List.Forall2 value_uincl vr vr'.
Proof. apply remove_init_fdP; apply wf_inits. Qed.

Section ADD_INIT.

  Context (p : uprog) (ev:unit).

  Notation gd := (p_globs p).

  Notation p' := (add_init_prog p).

  Definition undef_except (X:Sv.t) vm :=
    forall x, ~Sv.In x X ->  vm.[x] = undef_addr (vtype x).

  Notation lift_vm sem s1 s2 :=
    (forall vm1,
       vm_eq (evm s1) vm1 ->
       exists2 vm2,
         vm_eq (evm s2) vm2
         & sem (with_vm s1 vm1) (with_vm s2 vm2))
    (only parsing).

  Definition lift_semI s1 i s2 :=
    lift_vm (fun s s' => sem_I p' ev s i s') s1 s2.

  Definition lift_sem s1 c s2 :=
    lift_vm (fun s s' => sem p' ev s c s') s1 s2.

  Let Pi s1 i s2 :=
    lift_semI s1 i s2
    /\ forall I,
         undef_except I (evm s1) ->
         let: iI := add_init_i I i in
         undef_except iI.2 (evm s2) /\ lift_sem s1 iI.1 s2.

  Let Pi_r s1 (i:instr_r) s2 := forall ii, Pi s1 (MkI ii i) s2.

   Let Pc s1 c s2 :=
     lift_sem s1 c s2
     /\ forall I,
          undef_except I (evm s1) ->
          let: cI := add_init_c add_init_i I c in
          undef_except cI.2 (evm s2) /\ lift_sem s1 cI.1 s2.

 Let Pfor i vs s1 c s2 :=
   lift_vm (fun s s' => sem_for p' ev i vs s c s') s1 s2.

  Let Pfun scs m fn vargs scs' m' vres :=
    sem_call p' ev scs m fn vargs scs' m' vres.

  Local Lemma RAnil : sem_Ind_nil Pc.
  Proof. 
    move=> s1; split.
    + by move=> vm1 he;exists vm1 => //;constructor.
    by move=> I hu /=;split => // vm1 he; exists vm1 => //; constructor.
  Qed.

  Local Lemma RAcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ [] hsi hi _ [] hsc hc; split.
    + by move=> vm1 /hsi [vm2] /hsc [vm3] ? hsc' hsi'; exists vm3 => //; apply: Eseq hsi' hsc'.
    move=> I /hi /=; case: add_init_i => c1 I2 [] /= /hc; case: add_init_c => c2 I3 [] /= hu3 hc2 hc1.
    by split => // vm1 /hc1 [] vm2 /hc2 [] vm3 ? hc2' hc1'; exists vm3 => //; apply: sem_app hc1' hc2'.
  Qed.

  Local Lemma RAmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by move=> ii i s1 s2 _ /(_ ii). Qed.

  Lemma add_initP ii0 ii1 i s1 s2 I X :
    undef_except I (evm s1) ->
    lift_semI s1 (MkI ii0 i) s2 ->
    lift_sem s1 (add_init ii1 I X (MkI ii0 i)) s2.
  Proof.
    move=> hu hs; rewrite /add_init Sv.fold_spec.
    have : forall x:var, x \in Sv.elements (Sv.diff X I) -> (evm s1).[x] = undef_addr (vtype x).
    + by move=> x /Sv_elemsP hx; rewrite hu //; SvD.fsetdec.
    have : lift_sem s1 [:: MkI ii0 i] s2.
    + by move=> vm1 /hs [vm2] ??; exists vm2 => //;apply sem_seq1.
    clear; elim: Sv.elements s1 [:: MkI ii0 i] => [ | x xs ih] //= s1 l hl hu.
    apply ih; last by move=> y hy; apply hu; rewrite in_cons hy orbT.
    move=> vm1 hu1; rewrite /add_init_aux.
    have hl1 := hl _ hu1.
    case heq: vtype => [||len|] //; case:ifP => _ //.
    set i' := MkI _ _.
    have [vm2 heq2 hi']: exists2 vm2, evm s1 =1 vm2 & sem_I p' ev (with_vm s1 vm1) i' (with_vm s1 vm2).
    + rewrite /i'; have := hu x; rewrite in_cons eq_refl /= => /(_ erefl) {hu i'} hx.
      exists (vm1.[x <- Varr (WArray.empty len)]).
      + move: hu1; rewrite !vm_eq_vm_rel => hu1; apply vm_rel_set_r.
        + by move=> _ /=; rewrite hx heq eqxx.
        by apply: vm_relI hu1.
      constructor; econstructor; first reflexivity.
      + by rewrite /truncate_val /= WArray.castK.
      by apply /write_varP; econstructor => //=; rewrite heq /truncatable eqxx.
    by have [vm3 ? hc']:= hl _ heq2; exists vm3 => //; apply: Eseq hc'.
  Qed.

  Local Lemma aux ii0 ii1 i s1 s2 :
    sem_I p ev s1 (MkI ii0 i) s2 →
    lift_semI s1 (MkI ii0 i) s2 →
    lift_semI s1 (MkI ii0 i) s2 /\
    forall I, undef_except I (evm s1) →
      undef_except (Sv.union I (write_i i)) (evm s2) /\
      let: i' := add_init ii1 I (Sv.union (write_i i) (read_i i)) (MkI ii0 i) in
      lift_sem s1 i' s2.
  Proof.
    move=> hs hs'; split => //.
    move=> I hu; split.
    + by move=> x hx; rewrite -(write_IP hs) ?hu //; SvD.fsetdec.
    by apply add_initP.
  Qed.

  Local Lemma RAasgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' hse htr hwr ii /=.
    apply aux => //.
    + by constructor; econstructor; eauto.
    move=> vm1 heq1.
    have [vm2 heq2 hwr2 ]:= write_lvar_ext_eq heq1 hwr.
    exists vm2 => //; constructor; econstructor; eauto.
    by rewrite -(sem_pexpr_ext_eq _ _ e heq1).
  Qed.

  Local Lemma RAopn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 xs tag ty es hso ii /=. 
    apply aux => //.
    + by constructor; econstructor.
    move: hso; rewrite /sem_sopn; t_xrbindP => vs vs' hse ho hwr vm1 heq1.
    have [vm2 heq2 hwr2 ]:= write_lvars_ext_eq heq1 hwr.
    exists vm2 => //; constructor; econstructor; eauto.
    by rewrite /sem_sopn -(sem_pexprs_ext_eq _ _ es heq1) hse /= ho.
  Qed.

  Local Lemma RAsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> s1 scs m s2 o xs es ves vs he hsys hw ii.
    apply aux => //.
    + by constructor; econstructor; eauto.
    move=> vm1 heq1.
    have [vm2 heq2 hw2 ]:= write_lvars_ext_eq (s1 := with_scs (with_mem s1 m) scs) heq1 hw.
    exists vm2 => //; constructor; econstructor; eauto.
    by rewrite -(sem_pexprs_ext_eq _ _ es heq1).
  Qed.

  Local Lemma RAif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H _ [] hs Hc ii /=; split.
    + move=> vm1 /dup[] heq1 /hs [vm2] ? hc; exists vm2 => //; constructor.
      by apply: Eif_true => //; rewrite -(sem_pexpr_ext_eq _ _ e heq1).
    move=> I /dup [] hu1 /Hc [] /=.
    case: (add_init_c _ _ c1)=> /= c1' O1; case: (add_init_c _ _ c2)=> /= c2' O2.
    move=> hu2 hsc'; split.
    + by move=> ??;rewrite hu2 //;SvD.fsetdec.
    apply add_initP => //.
    move=> vm1 /dup[] heq1 /hsc' [vm2 he hs']; exists vm2 => //.
    by constructor; apply: Eif_true => //; rewrite -(sem_pexpr_ext_eq _ _ e heq1).
  Qed.

  Local Lemma RAif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H _ [] hs Hc ii /=; split.
    + move=> vm1 /dup[] heq1 /hs [vm2] ? hc; exists vm2 => //; constructor.
      by apply: Eif_false => //; rewrite -(sem_pexpr_ext_eq _ _ e heq1).
    move=> I /dup [] hu1 /Hc [] /=.
    case: (add_init_c _ _ c1)=> /= c1' O1; case: (add_init_c _ _ c2)=> /= c2' O2.
    move=> hu2 hsc'; split.
    + by move=> ??;rewrite hu2 //;SvD.fsetdec.
    apply add_initP => //.
    move=> vm1 /dup[] heq1 /hsc' [vm2 he hs']; exists vm2 => //.
    by constructor; apply: Eif_false => //; rewrite -(sem_pexpr_ext_eq _ _ e heq1).
  Qed.

  Local Lemma RAwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' hsc [] Hc _ he hsc' [] Hc' _ hsi Hi ii.
    have [{Hi}Hi _]:= Hi ii.
    apply aux.
    + by constructor;apply: Ewhile_true;eauto.
    move=> vm1 /Hc [vm2] /dup[] heq /Hc' [vm3] /Hi [vm4] ? /sem_IE h *; exists vm4 => //.
    constructor;apply: Ewhile_true;eauto.
    by rewrite -(sem_pexpr_ext_eq _ _ e heq).
  Qed.

  Local Lemma RAwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' hsc [] Hc _ he ii.
    apply aux.
    + by constructor;apply: Ewhile_false;eauto.
    move=> vm1 /Hc [vm2] heq ?; exists vm2 => //.
    constructor;apply: Ewhile_false;eauto.
    by rewrite -(sem_pexpr_ext_eq _ _ e heq).
  Qed.

  Local Lemma RAfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi H H' hsf hf ii.
    apply aux.
    + by constructor; econstructor; eauto.
    move=> vm1 /dup [] heq /hf [vm2] ? hs'; exists vm2 => //.
    by constructor; econstructor; eauto; rewrite -(sem_pexpr_ext_eq _ _ _ heq).
  Qed.

  Local Lemma RAfor_nil : sem_Ind_for_nil Pfor.
  Proof. move=> s i c vm1 Hvm1;exists vm1 =>//;constructor. Qed.

  Local Lemma RAfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hi _ [] Hc _ _ Hf vm1 Hvm1.
    have [vm2 /Hc [vm3] /Hf [vm4] *]:= write_lvar_ext_eq Hvm1 (Hi : write_lval true gd i w s1 = ok s1').
    exists vm4 => //; by econstructor; eauto.
  Qed.

  Local Lemma RAcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 xs fn args vargs vs Hargs Hcall Hfd Hxs ii'.
    apply aux.
    + constructor; econstructor;eauto.
    move=> vm1 heq1.
    have heq1' : (evm (with_mem s1 m2) =1 vm1)%vm := heq1.
    have [vm2 heq2 hwr2 ]:= write_lvars_ext_eq (s1 := (with_scs (with_mem s1 m2) scs2)) heq1 Hxs.
    exists vm2 => //; constructor; econstructor; eauto.
    by rewrite -(sem_pexprs_ext_eq _ _ args).
  Qed.

  Local Lemma RAproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn fd vargs vargs' s0 s1 s2 vres vres' Hget Htin Hi Hargs Hsem [] hsi Hrec Hmap Htout Hsys Hfi.
    have hget : get_fundef (p_funcs p') fn = Some (add_init_fd fd).
    + by rewrite /p' get_map_prog Hget.
    set I := vrvs [seq (Lvar i) | i <- f_params fd].
    case: (Hrec I).
    + move=> x hx. 
      move: Hargs; rewrite (write_vars_lvals _ gd) => /disjoint_eq_ons -/(_ (Sv.singleton x)) <-.
      + by move: Hi => [<-] /=; rewrite Vm.initP.
      + by rewrite -/I /disjoint /is_true Sv.is_empty_spec; SvD.fsetdec.
      by SvD.fsetdec.     
    move=> ?  /(_ (evm s1) (fun _ => erefl)) [vm2] heq2 hsem {Hsem Hget}.    
    eapply (EcallRun (f := add_init_fd fd) (s1:= with_vm s1 (evm s1)) (s2:= (with_vm s2 vm2))); eauto.
    + by case: (s1) Hargs.
    by rewrite -Hmap; apply mapM_ext => // y; rewrite /get_var heq2.
  Qed.

  Lemma add_init_fdP f scs mem scs' mem' va vr:
    sem_call p ev scs mem f va scs' mem' vr ->
    sem_call p' ev scs mem f va scs' mem' vr.
  Proof.
    exact:
      (sem_call_Ind
         RAnil
         RAcons
         RAmkI
         RAasgn
         RAopn
         RAsyscall
         RAif_true
         RAif_false
         RAwhile_true
         RAwhile_false
         RAfor
         RAfor_nil
         RAfor_cons
         RAcall
         RAproc).
  Qed.

End ADD_INIT.

End WITH_PARAMS.
