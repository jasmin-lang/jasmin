(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem compiler_util.
Require Export array_init.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Section ASM_OP.

Context {pd:PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.
Context `{asmop:asmOp}.

Section Section.

Context {T:eqType} {pT:progT T} {sCP: semCallParams} (wf_init: wf_init sCP).

Section REMOVE_INIT.
  
  Context (is_reg_array: var -> bool) (p : prog) (ev: extra_val_t).
  Notation gd := (p_globs p).

  Notation p' := (remove_init_prog is_reg_array p).

  Let Pi s1 (i:instr) s2 :=
    forall vm1,
      vm_uincl (evm s1) vm1 -> wf_vm vm1 ->
      exists vm2,
       [/\ sem p' ev (with_vm s1 vm1) (remove_init_i is_reg_array i) (with_vm s2 vm2),
           vm_uincl (evm s2) vm2 &
           wf_vm vm2].

  Let Pi_r s1 (i:instr_r) s2 := forall ii, Pi s1 (MkI ii i) s2.

  Let Pc s1 (c:cmd) s2 :=
    forall vm1,
      vm_uincl (evm s1) vm1 -> wf_vm vm1 ->
      exists vm2,
        [/\ sem p' ev (with_vm s1 vm1) (remove_init_c is_reg_array c) (with_vm s2 vm2),
            vm_uincl (evm s2) vm2 &
            wf_vm vm2].

  Let Pfor (i:var_i) vs s1 c s2 :=
    forall vm1,
      vm_uincl (evm s1) vm1 -> wf_vm vm1 ->
      exists vm2,
        [/\ sem_for p' ev i vs (with_vm s1 vm1) (remove_init_c is_reg_array c) (with_vm s2 vm2),
            vm_uincl (evm s2) vm2 &
            wf_vm vm2].

  Let Pfun scs m fn vargs scs' m' vres :=
    forall vargs',
    List.Forall2 value_uincl vargs vargs' ->
    exists vres', sem_call p' ev scs m fn vargs' scs' m' vres' /\
      List.Forall2 value_uincl vres vres'.

  Local Lemma Rnil : sem_Ind_nil Pc.
  Proof. by move=> s vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

  Local Lemma Rcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ Hi _ Hc vm1 Hvm1 /(Hi _ Hvm1)  [vm2 []] Hsi Hvm2 /(Hc _ Hvm2) [vm3 []] Hsc ??.
    by exists vm3;split=>//=; apply: sem_app Hsc.
  Qed.

  Local Lemma RmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by move=> ii i s1 s2 _ Hi vm1 Hvm1 /(Hi ii _ Hvm1) [vm2 []] Hsi ??;exists vm2. Qed.

  Lemma is_array_initP e : is_array_init e -> exists n, e = Parr_init n.
  Proof. by case: e => // n _; eauto. Qed.

  Lemma assgn_uincl s1 s2 e v ty v' vm1 x ii tag:  
    sem_pexpr gd s1 e = ok v ->
    truncate_val ty v = ok v' -> 
    write_lval gd x v' s1 = ok s2 ->
    vm_uincl (evm s1) vm1 ->
    wf_vm vm1 ->
    ∃ vm2 : vmap, 
      [/\ sem p' ev (with_vm s1 vm1) [:: MkI ii (Cassgn x tag ty e)] (with_vm s2 vm2), 
          vm_uincl (evm s2) vm2 & 
          wf_vm vm2].
  Proof.
    move=> Hse hsub hwr Hvm1. 
    have [z' Hz' Hz] := sem_pexpr_uincl Hvm1 Hse.
    have [z1 htr Uz1]:= value_uincl_truncate Hz hsub.
    move=> hwf ; have [vm2 Hw ?]:= write_uincl Hvm1 Uz1 hwr.
    exists vm2;split=> //.
    + apply sem_seq1;constructor;econstructor;eauto.
    by apply: wf_write_lval Hw.
  Qed.

  Local Lemma Rasgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' Hse hsub hwr ii vm1 Hvm1 /=; case: ifP; last first.
    + by move=> _; apply: assgn_uincl Hse hsub hwr Hvm1.
    case: ifP; last first.
    + by move=> _ _; apply: assgn_uincl Hse hsub hwr Hvm1.
    move=> _ /is_array_initP [n e1];subst e.
    case: Hse => ?; subst v.
    move: hsub;rewrite /truncate_val;case: ty => //= nty.
    t_xrbindP => empty /WArray.cast_empty_ok ??; subst v' empty.
    case: x hwr => [vi t | [[xt xn] xi] | ws x e | aa ws x e | aa ws len [[xt xn] xi] e] /=.
    + by move=> /write_noneP [->];exists vm1;split=> //;constructor.
    + apply: rbindP => vm1';apply: on_vuP => //=.
      + case: xt => //= p0 _ /WArray.cast_empty_ok -> ? [?]; subst => Wf1.
        exists vm1;split => //=; first by constructor.
        move=> z;have := Hvm1 z.
        case: ({| vtype := sarr p0; vname := xn |} =P z) => [<- _ | /eqP neq].
        + rewrite Fv.setP_eq; have := Wf1 {| vtype := sarr p0; vname := xn |}.
          case: (vm1.[_]) => //= [ | [] //].
          move=> a _;split;first by apply Z.le_refl.
          move=> ??; rewrite (WArray.get_empty); case: ifP => //.
        by rewrite Fv.setP_neq.
      by rewrite /of_val;case:xt => //= ? ?; case: wsize_eq_dec => // ?; case: CEDecStype.pos_dec.
    + by t_xrbindP.
    + by apply: on_arr_varP => ???; t_xrbindP.
    apply: on_arr_varP => /= tlen t ?; t_xrbindP => hg i vi hvi hi _ /WArray.cast_empty_ok ->.
    move => t1 ht1; apply: rbindP => vm1' hset [<-] Wf1; subst xt.
    exists vm1;split => //=; first by constructor.
    move=> z;have := Hvm1 z.  
    move: hset; apply: set_varP => //= ? <- <-.
    case: ({| vtype := sarr tlen; vname := xn |} =P z) => [<- _ | /eqP neq]; last by rewrite Fv.setP_neq.
    rewrite Fv.setP_eq; have := Wf1 {| vtype := sarr tlen; vname := xn |}.
    move: hg; rewrite /get_var /on_vu /=. set x := {| vtype := _|}.
    have := Hvm1 x; rewrite /eval_uincl.
    case: (evm s1).[x] => [ a1 | [] //].
    case: vm1.[x] => [a2 | //] [ _ hu] heq _.
    have ?:= Varr_inj1 (ok_inj heq); subst a1 => {heq}.
    rewrite WArray.castK.
    split; first by apply Z.le_refl.
    move=> k w; rewrite (WArray.set_sub_get8 ht1) /=; case: ifP => ?.
    + by rewrite WArray.get_empty; case: ifP.
    by apply hu.
  Qed.

  Local Lemma Ropn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es H ii vm1 Hvm1; move: H;rewrite /sem_sopn; t_xrbindP => rs vs.
    move=> /(sem_pexprs_uincl Hvm1) [] vs' H1 H2.
    move=> /(vuincl_exec_opn H2) [] rs' H3 H4.
    move=> /(writes_uincl Hvm1 H4) [] vm2 Hw ?.
    exists vm2;split => //=;last by apply: wf_write_lvals Hw.
    by apply sem_seq1;constructor;constructor;rewrite /sem_sopn H1 /= H3.
  Qed.

  Local Lemma Rsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> s1 scs m s2 o xs es ves vs he hsys hw ii vm1 uvm hwf.
    have [ves' he' uves] := sem_pexprs_uincl uvm he.
    have [vs' hsys' uvs]:= exec_syscallP hsys uves.
    have [vm2 hw'] := writes_uincl (s1 := with_scs (with_mem s1 m) scs) uvm uvs hw.
    exists vm2;split => //=;last by apply: wf_write_lvals hw'.
    apply sem_seq1; constructor; econstructor; eauto.
  Qed.

  Local Lemma Rif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H _ Hc ii vm1 Hvm1.
    have [v' H1 /value_uincl_bool1 ?] := sem_pexpr_uincl Hvm1 H;subst => Hwf.
    have [vm2 [??]]:= Hc _ Hvm1 Hwf;exists vm2;split=>//.
    by apply sem_seq1;constructor;apply Eif_true;rewrite // H1.
  Qed.

  Local Lemma Rif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H _ Hc ii vm1 Hvm1.
    have [v' H1 /value_uincl_bool1 ?] := sem_pexpr_uincl Hvm1 H;subst => Hwf.
    have [vm2 [??]]:= Hc _ Hvm1 Hwf;exists vm2;split=>//.
    by apply sem_seq1;constructor;apply Eif_false;rewrite // H1.
  Qed.

  Local Lemma Rwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' _ Hc H _ Hc' _ Hw ii vm1 Hvm1 Hwf;move: H.
    have [vm2 [Hs2 Hvm2 Hwf2]] := Hc _ Hvm1 Hwf.
    move=> /(sem_pexpr_uincl Hvm2) [] v' H1 /value_uincl_bool1 H2;subst.
    have [vm3 [H4 Hvm3 ]]:= Hc' _ Hvm2 Hwf2.
    move=> /(Hw ii _ Hvm3)  [vm4 [Hsem ??]]; exists vm4;split => //=.
    apply sem_seq1;constructor;eapply Ewhile_true;eauto.
    by case/semE: Hsem => si [] /sem_IE ? /semE ?; subst si.
  Qed.

  Local Lemma Rwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' _ Hc H ii vm1 Hvm1 Hwf; move: H.
    have [vm2 [Hs2 Hvm2 Hwf2]] := Hc _ Hvm1 Hwf.
    move=> /(sem_pexpr_uincl Hvm2) [] v' H1 /value_uincl_bool1 ?;subst.
    by exists vm2;split=> //=;apply sem_seq1;constructor;apply: Ewhile_false=> //;rewrite H1.
  Qed.

  Local Lemma Rfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi H H' _ Hfor ii vm1 Hvm1 Hwf.
    have [? H1 /value_uincl_int1 H2]:= sem_pexpr_uincl Hvm1 H;subst.
    have [? H3 /value_uincl_int1 H4]:= sem_pexpr_uincl Hvm1 H';subst.
    have [vm2 []???]:= Hfor _ Hvm1 Hwf; exists vm2;split=>//=.
    by apply sem_seq1;constructor; econstructor;eauto;rewrite ?H1 ?H3.
  Qed.

  Local Lemma Rfor_nil : sem_Ind_for_nil Pfor.
  Proof. by move=> s i c vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

  Local Lemma Rfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hi _ Hc _ Hf vm1 Hvm1 Hwf.
    have [vm1' Hi' /Hc] := write_var_uincl Hvm1 (value_uincl_refl _) Hi.
    have /(_ Hwf) /= Hwf' := wf_write_var _ Hi'.
    move=> /(_ Hwf') [vm2 [Hsc /Hf H /H]] [vm3 [Hsf Hvm3]];exists vm3;split => //.
    by econstructor;eauto.
  Qed.

  Local Lemma Rcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 ii xs fn args vargs vs Hargs Hcall Hfd Hxs ii' vm1 Hvm1 Hwf.
    have [vargs' Hsa /Hfd [vres' [Hc Hvres]]]:= sem_pexprs_uincl Hvm1 Hargs.
    have /(_ _ Hvm1) [vm2' Hw ?] := writes_uincl _ Hvres Hxs.
    exists vm2';split=>//=.
    + by apply: sem_seq1;constructor; econstructor;eauto.
    by apply: wf_write_lvals Hw.
  Qed.

  Local Lemma Rproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn fd vargs vargs' s0 s1 s2 vres vres' Hget Htin Hi Hargs Hsem Hrec Hmap Htout Hsys Hfi vargs1' Uargs.
    have [vargs1 Htin1 Uargs1]:= mapM2_truncate_val Htin Uargs.
    have [vm1 /= ]:= write_vars_uincl (vm_uincl_refl _) Uargs1 Hargs.
    rewrite with_vm_same => Hargs' Hvm1.
    have Hwf1 := wf_write_vars (wf_init Hi wf_vmap0) Hargs'.
    have [vm2' /= [] Hsem' Uvm2 Hwf2]:= Hrec _ Hvm1 Hwf1.
    have [vres1 Hvres Hsub] := get_vars_uincl Uvm2 Hmap.
    have [vres1' Htout1 Ures1]:= mapM2_truncate_val Htout Hsub.
    exists vres1';split => //.
    apply: (EcallRun (f:=remove_init_fd is_reg_array fd)); eauto.
    by rewrite /p' /remove_init_prog get_map_prog Hget.
  Qed.

  Lemma remove_init_fdP f scs mem scs' mem' va va' vr:
    List.Forall2 value_uincl va va' ->
    sem_call p ev scs mem f va scs' mem' vr ->
    exists vr', sem_call p' ev scs mem f va' scs' mem' vr' /\ List.Forall2 value_uincl vr vr'.
  Proof.
    move=> /(@sem_call_Ind _ _ _ _ _ _ _ _ p ev Pc Pi_r Pi Pfor Pfun Rnil Rcons RmkI Rasgn Ropn Rsyscall
             Rif_true Rif_false Rwhile_true Rwhile_false Rfor Rfor_nil Rfor_cons Rcall Rproc) H.
    by move=> /H.
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

  Context (is_ptr : var -> bool) (p : uprog) (ev:unit).

  Notation gd := (p_globs p).

  Notation p' := (add_init_prog is_ptr p).

  Definition undef_except (X:Sv.t) (vm:vmap) := 
   forall x, ~Sv.In x X ->  vm.[x] = pundef_addr (vtype x).

  Let Pi s1 (i:instr) s2 :=
    (forall vm1, evm s1 =v vm1 -> 
       exists2 vm2, evm s2 =v vm2 & sem_I p' ev (with_vm s1 vm1) i (with_vm s2 vm2)) /\
    forall I, undef_except I (evm s1) ->
      undef_except (add_init_i is_ptr I i).2 (evm s2) /\
      forall vm1, evm s1 =v vm1 -> 
        exists2 vm2, evm s2 =v vm2 &
          sem p' ev (with_vm s1 vm1) (add_init_i is_ptr I i).1 (with_vm s2 vm2).

  Let Pi_r s1 (i:instr_r) s2 := forall ii, Pi s1 (MkI ii i) s2.

  Let Pc s1 (c:cmd) s2 :=
    (forall vm1, evm s1 =v vm1 -> 
         exists2 vm2, evm s2 =v vm2 & sem p' ev (with_vm s1 vm1) c (with_vm s2 vm2)) /\
    forall I, undef_except I (evm s1) ->
      undef_except (add_init_c (add_init_i is_ptr) I c).2 (evm s2) /\
      forall vm1, evm s1 =v vm1 -> 
        exists2 vm2, evm s2 =v vm2 &
         sem p' ev (with_vm s1 vm1) (add_init_c (add_init_i is_ptr) I c).1 (with_vm s2 vm2).

  Let Pfor (i:var_i) vs s1 c s2 :=
    forall vm1, evm s1 =v vm1 -> 
       exists2 vm2, evm s2 =v vm2 & sem_for p' ev i vs (with_vm s1 vm1) c (with_vm s2 vm2).

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

  Lemma add_initP ii i s1 s2 I X: 
    undef_except I (evm s1) → 
    (∀ vm1 : vmap, evm s1 =v vm1 → exists2 vm2 : vmap, evm s2 =v vm2 & sem_I p' ev (with_vm s1 vm1) (MkI ii i) (with_vm s2 vm2)) →
    ∀ vm1 : vmap, evm s1 =v vm1 → 
    exists2 vm2 : vmap,
        evm s2 =v vm2 & sem p' ev (with_vm s1 vm1) (add_init is_ptr ii I X (MkI ii i)) (with_vm s2 vm2).
  Proof.
    move=> hu hs; rewrite /add_init Sv.fold_spec.
    have : forall x:var, x \in Sv.elements (Sv.diff X I) -> (evm s1).[x] = pundef_addr (vtype x).
    + by move=> x /Sv_elemsP hx; rewrite hu //; SvD.fsetdec.
    have : ∀ vm1 : vmap, evm s1 =v vm1 → 
      exists2 vm2 : vmap, evm s2 =v vm2 & sem p' ev (with_vm s1 vm1) [:: MkI ii i] (with_vm s2 vm2).
    + by move=> vm1 /hs [vm2] ??; exists vm2 => //;apply sem_seq1.
    clear; elim: Sv.elements s1 [:: MkI ii i] => [ | x xs ih] //= s1 l hl hu.
    apply ih; last by move=> y hy; apply hu; rewrite in_cons hy orbT.
    move=> vm1 hu1; rewrite /add_init_aux.
    have hl1 := hl _ hu1.
    case heq: vtype => [||len|] //; case:ifP => _ //.
    set i' := MkI _ _.
    have [vm2 heq2 hi']: exists2 vm2, evm s1 =v vm2 & sem_I p' ev (with_vm s1 vm1) i' (with_vm s1 vm2).
    + rewrite /i'; have := hu x; rewrite in_cons eq_refl /= => /(_ erefl) {hu i'}.
      case: x heq => ty xn /= -> /= hx.
      set x := {|vtype := _|}.
      exists (vm1.[x <- ok (WArray.empty len)])%vmap.
      + move=> y; case: (x =P y) => [<- | /eqP hne].
        + by rewrite Fv.setP_eq hx. 
        by rewrite Fv.setP_neq // hu1.
      constructor; econstructor; first reflexivity.
      + by rewrite /truncate_val /= WArray.castK.
      by rewrite /= /write_var /= /set_var /= WArray.castK.
    by have [vm3 ? hc']:= hl _ heq2; exists vm3 => //; apply: Eseq hc'.
  Qed.

  Local Lemma aux ii i s1 s2 :
    sem_I p ev s1 (MkI ii i) s2 →
    (∀ vm1 : vmap, evm s1 =v vm1 →
       exists2 vm2 : vmap, evm s2 =v vm2 & sem_I p' ev (with_vm s1 vm1) (MkI ii i) (with_vm s2 vm2)) →
    (∀ vm1 : vmap,  evm s1 =v vm1 → 
          exists2 vm2 : vmap, evm s2 =v vm2 & sem_I p' ev (with_vm s1 vm1) (MkI ii i) (with_vm s2 vm2)) /\
    forall I, undef_except I (evm s1) →
      undef_except (Sv.union I (write_i i)) (evm s2) /\
      ∀ vm1 : vmap, evm s1 =v vm1 → 
        exists2 vm2 : vmap,
          evm s2 =v vm2 &
          sem p' ev (with_vm s1 vm1)
            (add_init is_ptr ii I (Sv.union (write_i i) (read_i i)) (MkI ii i)) (with_vm s2 vm2).
  Proof.
    move=> hs hs'; split => //.
    move=> I hu; split.
    + by move=> x hx; rewrite -(write_IP hs) ?hu //; SvD.fsetdec.
    by apply add_initP.
  Qed.

  Lemma sem_pexpr_ext_eq s e vm : 
    evm s =v vm ->
    sem_pexpr gd s e = sem_pexpr gd (with_vm s vm) e.
  Proof. by move=> heq; apply (@read_e_eq_on _ _ _ _ Sv.empty). Qed.

  Lemma sem_pexprs_ext_eq s es vm : 
    evm s =v vm ->
    sem_pexprs gd s es = sem_pexprs gd (with_vm s vm) es.
  Proof. by move=> heq; apply (@read_es_eq_on _ _ _ _ _ Sv.empty). Qed.

  Lemma write_lvar_ext_eq x v s1 s2 vm1 :
    evm s1 =v vm1 ->
    write_lval gd x v s1 = ok s2 ->
    exists2 vm2, evm s2 =v vm2 & write_lval gd x v (with_vm s1 vm1) = ok (with_vm s2 vm2).
  Proof.
    move=> he hw.
    have hsub : Sv.Subset (read_rv x) (read_rv x) by SvD.fsetdec.
    have heq : evm s1 =[read_rv x]  vm1 by move=> ??;rewrite he.
    have [vm2 [heq2 hw2]]:= write_lval_eq_on hsub hw heq.
    exists vm2 => //.
    move=> y; case: (Sv_memP y (vrv x)) => hin.
    + by apply heq2; SvD.fsetdec.
    have hd : disjoint (Sv.singleton y) (vrv x). 
    + by rewrite /disjoint /is_true Sv.is_empty_spec; SvD.fsetdec.
    rewrite -(disjoint_eq_on hd hw); last SvD.fsetdec.
    have := disjoint_eq_on hd hw2.
    rewrite /with_vm /= => <- //; SvD.fsetdec.
  Qed.

  Lemma write_lvars_ext_eq xs vs s1 s2 vm1 :
    evm s1 =v vm1 ->
    write_lvals gd s1 xs vs = ok s2 ->
    exists2 vm2, evm s2 =v vm2 & write_lvals gd (with_vm s1 vm1) xs vs = ok (with_vm s2 vm2).
  Proof.
    move=> he hw.
    have hsub : Sv.Subset (read_rvs xs) (read_rvs xs) by SvD.fsetdec.
    have heq : evm s1 =[read_rvs xs]  vm1 by move=> ??;rewrite he.
    have [vm2 [heq2 hw2]]:= write_lvals_eq_on hsub hw heq.
    exists vm2 => //.
    move=> y; case: (Sv_memP y (vrvs xs)) => hin.
    + by apply heq2; SvD.fsetdec.
    have hd : disjoint (Sv.singleton y) (vrvs xs). 
    + by rewrite /disjoint /is_true Sv.is_empty_spec; SvD.fsetdec.
    rewrite -(disjoint_eq_ons hd hw); last SvD.fsetdec.
    have := disjoint_eq_ons hd hw2.
    rewrite /with_vm /= => <- //; SvD.fsetdec.
  Qed.

  Local Lemma RAasgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' hse htr hwr ii /=.
    apply aux => //.
    + by constructor; econstructor; eauto.
    move=> vm1 heq1.
    have [vm2 heq2 hwr2 ]:= write_lvar_ext_eq heq1 hwr.
    exists vm2 => //; constructor; econstructor; eauto.
    by rewrite -(sem_pexpr_ext_eq e heq1).
  Qed.

  Local Lemma RAopn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 xs tag ty es hso ii /=. 
    apply aux => //.
    + by constructor; econstructor.
    move: hso; rewrite /sem_sopn; t_xrbindP => vs vs' hse ho hwr vm1 heq1.
    have [vm2 heq2 hwr2 ]:= write_lvars_ext_eq heq1 hwr.
    exists vm2 => //; constructor; econstructor; eauto.
    by rewrite /sem_sopn -(sem_pexprs_ext_eq es heq1) hse /= ho.
  Qed.

  Local Lemma RAsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> s1 scs m s2 o xs es ves vs he hsys hw ii.
    apply aux => //.
    + by constructor; econstructor; eauto.
    move=> vm1 heq1.
    have [vm2 heq2 hw2 ]:= write_lvars_ext_eq (s1 := with_scs (with_mem s1 m) scs) heq1 hw.
    exists vm2 => //; constructor; econstructor; eauto.
    by rewrite -(sem_pexprs_ext_eq es heq1).
  Qed.

  Local Lemma RAif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H _ [] hs Hc ii /=; split.
    + move=> vm1 /dup[] heq1 /hs [vm2] ? hc; exists vm2 => //; constructor.
      by apply: Eif_true => //; rewrite -(sem_pexpr_ext_eq e heq1).
    move=> I /dup [] hu1 /Hc [] /=.
    case: (add_init_c _ _ c1)=> /= c1' O1; case: (add_init_c _ _ c2)=> /= c2' O2.
    move=> hu2 hsc'; split.
    + by move=> ??;rewrite hu2 //;SvD.fsetdec.
    apply add_initP => //.
    move=> vm1 /dup[] heq1 /hsc' [vm2 he hs']; exists vm2 => //.
    by constructor; apply: Eif_true => //; rewrite -(sem_pexpr_ext_eq e heq1).
  Qed.

  Local Lemma RAif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H _ [] hs Hc ii /=; split.
    + move=> vm1 /dup[] heq1 /hs [vm2] ? hc; exists vm2 => //; constructor.
      by apply: Eif_false => //; rewrite -(sem_pexpr_ext_eq e heq1).
    move=> I /dup [] hu1 /Hc [] /=.
    case: (add_init_c _ _ c1)=> /= c1' O1; case: (add_init_c _ _ c2)=> /= c2' O2.
    move=> hu2 hsc'; split.
    + by move=> ??;rewrite hu2 //;SvD.fsetdec.
    apply add_initP => //.
    move=> vm1 /dup[] heq1 /hsc' [vm2 he hs']; exists vm2 => //.
    by constructor; apply: Eif_false => //; rewrite -(sem_pexpr_ext_eq e heq1).
  Qed.

  Local Lemma RAwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' hsc [] Hc _ he hsc' [] Hc' _ hsi Hi ii.
    have [{Hi}Hi _]:= Hi ii.
    apply aux.
    + by constructor;apply: Ewhile_true;eauto.
    move=> vm1 /Hc [vm2] /dup[] heq /Hc' [vm3] /Hi [vm4] ? /sem_IE h *; exists vm4 => //.
    constructor;apply: Ewhile_true;eauto.
    by rewrite -(sem_pexpr_ext_eq e heq).
  Qed.

  Local Lemma RAwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' hsc [] Hc _ he ii.
    apply aux.
    + by constructor;apply: Ewhile_false;eauto.
    move=> vm1 /Hc [vm2] heq ?; exists vm2 => //.
    constructor;apply: Ewhile_false;eauto.
    by rewrite -(sem_pexpr_ext_eq e heq).
  Qed.

  Local Lemma RAfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi H H' hsf hf ii.
    apply aux.
    + by constructor; econstructor; eauto.
    move=> vm1 /dup [] heq /hf [vm2] ? hs'; exists vm2 => //.
    by constructor; econstructor; eauto; rewrite -(sem_pexpr_ext_eq _ heq).
  Qed.

  Local Lemma RAfor_nil : sem_Ind_for_nil Pfor.
  Proof. move=> s i c vm1 Hvm1;exists vm1 =>//;constructor. Qed.

  Local Lemma RAfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c Hi _ [] Hc _ _ Hf vm1 Hvm1.
    have [vm2 /Hc [vm3] /Hf [vm4] *]:= write_lvar_ext_eq Hvm1 (Hi : write_lval gd i w s1 = ok s1').
    exists vm4 => //; by econstructor; eauto.
  Qed.

  Local Lemma RAcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 ii xs fn args vargs vs Hargs Hcall Hfd Hxs ii'.
    apply aux.
    + constructor; econstructor;eauto.
    move=> vm1 heq1.
    have heq1' : evm (with_mem s1 m2) =v vm1 := heq1.
    have [vm2 heq2 hwr2 ]:= write_lvars_ext_eq (s1 := (with_scs (with_mem s1 m2) scs2)) heq1 Hxs.
    exists vm2 => //; constructor; econstructor; eauto.
    by rewrite -(sem_pexprs_ext_eq args).
  Qed.

  Local Lemma RAproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn fd vargs vargs' s0 s1 s2 vres vres' Hget Htin Hi Hargs Hsem [] hsi Hrec Hmap Htout Hsys Hfi.
    have hget : get_fundef (p_funcs p') fn = Some (add_init_fd is_ptr fd).
    + by rewrite /p' get_map_prog Hget.
    set I := vrvs [seq (Lvar i) | i <- f_params fd].
    case: (Hrec I).
    + move=> x hx. 
      move: Hargs; rewrite (write_vars_lvals gd) => /disjoint_eq_ons -/(_ (Sv.singleton x)) <-.
      + by move: Hi => [<-] /=; rewrite Fv.get0.
      + by rewrite -/I /disjoint /is_true Sv.is_empty_spec; SvD.fsetdec.
      by SvD.fsetdec.     
    move=> ?  /(_ (evm s1) (fun _ => erefl)) [vm2] heq2 hsem {Hsem Hget}.    
    eapply (EcallRun (f := add_init_fd is_ptr fd) (s1:= with_vm s1 (evm s1)) (s2:= (with_vm s2 vm2))); eauto.
    + by case: (s1) Hargs.
    by rewrite -Hmap; apply mapM_ext => // y; rewrite /get_var heq2.
  Qed.

  Lemma add_init_fdP f scs mem scs' mem' va vr:
    sem_call p ev scs mem f va scs' mem' vr ->
    sem_call p' ev scs mem f va scs' mem' vr.
  Proof.
    by apply (@sem_call_Ind _ _ _ _ _ _ _ _ p ev Pc Pi_r Pi Pfor Pfun RAnil RAcons RAmkI RAasgn RAopn RAsyscall
               RAif_true RAif_false RAwhile_true RAwhile_false RAfor RAfor_nil RAfor_cons RAcall RAproc).
  Qed.

End ADD_INIT.

End ASM_OP.
