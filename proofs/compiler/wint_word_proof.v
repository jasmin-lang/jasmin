Require Import compiler_util psem psem_facts.
Require Import wint_word allocation_proof.
Import Utf8.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.

Section PROOF.

#[local] Existing Instance progUnit.
#[local] Existing Instance indirect_c.
#[local] Existing Instance withsubword.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

Context
  (remove_wint_annot: funname -> fundef -> fundef)
  (dead_vars_fd : fun_decl → instr_info → Sv.t).

Variable (p:prog) (ev:extra_val_t).

Notation gd := (p_globs p).

#[local]Open Scope vm_scope.

Section E.

  Context (s:estate) (vm:Vm.t) (hincl : evm s <=1 vm) (wdb : bool).

  Let s' := with_vm s vm.

  Let P e : Prop :=
    ∀ v,
      sem_pexpr wdb gd s e = ok v →
      exists2 v', sem_pexpr wdb gd s' (wi2w_e e) = ok v' & value_uincl v v'.

  Let Q es : Prop :=
    ∀ vs,
      sem_pexprs wdb gd s es = ok vs →
      exists2 vs', sem_pexprs wdb gd s' (map wi2w_e es) = ok vs' & List.Forall2 value_uincl vs vs'.

  Lemma wi2w_e_esP : (∀ e, P e) ∧ (∀ es, Q es).
  Proof.
    apply: pexprs_ind_pair; subst P Q; split => //=; t_xrbindP.
    + by move=> _ <-; exists [::].
    + move=> e he es hes ? v /he [v' -> /= hu] vs /hes [vs' -> /= hus] <-.
      by eexists; [reflexivity | eauto].
    1-3: move=> > ->; by eexists; [reflexivity | eauto].
    + by move=> x v; apply: get_gvar_uincl.
    + move=> al aa sz x e he v.
      apply: on_arr_gvarP => n t1 wt /(get_gvar_uincl hincl) [_] -> /value_uinclE [t2] -> htu.
      t_xrbindP => i ve /he [v' -> +] /to_intI ?; subst ve.
      move=> /value_uinclE ?; subst v' => ? /= /(WArray.uincl_get htu) -> <- /=.
      by (eexists; first reflexivity) => /=.
    + move=> aa sz len x e he v.
      apply: on_arr_gvarP => n t1 wt /(get_gvar_uincl hincl) [_] -> /value_uinclE [t2] -> htu.
      t_xrbindP => i ve /he [v' -> +] /to_intI ?; subst ve.
      move=> /value_uinclE -> /= ? /(WArray.uincl_get_sub htu) [t'] -> ht'u <- /=.
      by (eexists; first reflexivity) => /=.
    + move=> al sz x e he v a ve /(get_var_uincl hincl) [?] -> + /to_wordI [? [? [? htr1]]]; subst ve.
      move=> /value_uinclE [? [? [-> hu1]]] ?? /he [v' -> +] /to_wordI [sz' [w' [? htr]]]; subst.
      move=> /value_uinclE [?] [w''] [->] hu ? /=.
      rewrite (word_uincl_truncate hu1 htr1) (word_uincl_truncate hu htr) /= => -> <- /=.
      by (eexists; first reflexivity) => /=.
    + move=> o e he v v1 /he{he} [v' he hu].
      rewrite /sem_sop1 /=; t_xrbindP => + /(of_value_uincl_te hu).
      case: o => [sz | si sz | si sz | si sz | | sz | [ | sz] | sg o] /=;
        rewrite /= ?he /sem_sop1 /=; t_xrbindP;
        try by move=> > -> /= > [->] <-; (eexists; first reflexivity) => /=.
      case: o => /=; rewrite he /sem_sop1 /=.
      + move=> > /to_intI -> > /wint_of_intP [-> h] <- /=.
        by (eexists; first reflexivity) => /=.
      + move=> > /to_wordI [? [? [-> htr]]] > [<-] <- /=.
        by rewrite htr /=; eexists; first reflexivity.
      + move=> > /to_wordI [sz' [w' [?]]] htr ? [<-] <-; subst v'.
        eexists; first reflexivity.
        by apply: truncate_word_uincl htr.
      + move=> > /to_wordI [sz' [w' [?]]] htr ? [<-] <-; subst v'.
        eexists; first reflexivity.
        by apply: truncate_word_uincl htr.
      + move=> > /to_wordI [sz' [w' [?]]] htr ? [] + <-; subst v'.
        by case: sg => /=; rewrite htr /= => ->; (eexists; first reflexivity) => /=.
      move=> > /to_wordI [sz' [w' [?]]] htr ? + <-; subst v'.
      move=> /wint_of_intP [-> ?] /=; rewrite htr /=.
      (eexists; first reflexivity) => /=.
      by rewrite wrepr_opp wrepr_int_of_word.

    + move=> o e he1 e2 he2 v v1 /he1{he1} [v1' -> hu1] v2 /he2{he2} [v2' -> hu2] /=.
      rewrite /sem_sop2 /=; t_xrbindP.
      move=> w1 /(of_value_uincl_te hu1) h1 w2 /(of_value_uincl_te hu2) h2 {hu1 hu2}.
      case: o w1 h1 w2 h2 =>
       [ | | | k | k | k | si k | si k | ws | ws | ws | ws | k | k | ws | ws | k | k | k | k | k | k
                              | ve ws | ve ws | ve ws | ve ws | ve ws | ve ws | si ws o];
        try by move => /= > -> > -> > /= [<-] <-; eexists; first reflexivity.
      1-3: by rewrite /=; case: k => /= > -> > -> > [<-] <- /=; (eexists; first reflexivity) => /=.
      1-2: by rewrite /=; (case: k => /= > -> > -> >; first case) => /= -> <-;
             (eexists; first reflexivity).
      1-8: by case: k => /= > -> /= > -> /= > [->] <-; (eexists; first reflexivity).
      case: o; rewrite /= /mk_sem_wiop2 /=.
      1-3: by move=> > -> > -> /= > /wint_of_intP [-> _] <-; (eexists; first reflexivity);
           rewrite (wrepr_add, wrepr_mul, wrepr_sub) !wrepr_int_of_word.
      1-2: by move=> > -> > -> /= > -> <- /=; (eexists; first reflexivity) => /=.
      + move=> > -> w2 -> /= > /wint_of_intP /= [-> _] <-; (eexists; first reflexivity).
        rewrite /zlsl /sem_shl /sem_shift; case: ifPn => /ZleP ?.
        + by rewrite wrepr_mul wrepr_int_of_word GRing.mulrC wshl_sem.
        by have := wunsigned_range w2; Lia.lia.
      + rewrite /mk_sem_wishift; case: si => /= w1 -> w2 -> > /=;
        move=> /wint_of_intP [-> ?] <-;  (eexists; first reflexivity) => /=;
        rewrite /sem_sar /sem_shr /sem_shift /wsar /wshr /zasr /zlsl;
        have [h _ ] := wunsigned_range w2;
        (case: ZleP;
        [ case/Zle_lt_or_eq: h; first Lia.lia;
          by move=> <- _ /=; rewrite Z.mul_1_r Z.shiftr_0_r
        | by move=> _; rewrite Z.opp_involutive Z.shiftr_div_pow2]).

      1-2: by move=> > -> > -> > /= [<-] <-; (eexists; first reflexivity) => /=;
          rewrite int_of_word_eqb.

      1-4: move=> > -> > -> > /= [<-] <-; (eexists; first reflexivity) => /=;
           case: si => //=; rewrite ?(Z.gtb_ltb, Z.geb_leb) //.
    + move=> op es hes v vs /hes [vs']; rewrite /sem_pexprs => -> /= hus hs.
      by rewrite (vuincl_sem_opN hus hs); eexists; first reflexivity.

    move=> t e he e1 he1 e2 he2 v b v0 /he [v0' -> hu0].
    move=> /to_boolI => ?; subst v0.
    have ? := value_uinclE hu0; subst v0'.
    move=> v1_ v1 /he1 [v1' -> hu1] htr1 v2_ v2 /he2 [v2'-> hu2] htr2 /= <-.
    have [? -> ?]:= value_uincl_truncate hu1 htr1.
    have [? -> ?] /= := value_uincl_truncate hu2 htr2.
    by eexists; first reflexivity; case b.
  Qed.

  Lemma wi2w_eP : ∀ e, P e.
  Proof. by case wi2w_e_esP. Qed.

  Lemma wi2w_esP : ∀ e, Q e.
  Proof. by case wi2w_e_esP. Qed.

End E.

Lemma wi2w_lvalP wdb lv s s' vm v1 v2 :
  evm s <=1 vm ->
  value_uincl v1 v2 ->
  write_lval wdb gd lv v1 s = ok s' ->
  exists2 vm', write_lval wdb gd (wi2w_lv lv) v2 (with_vm s vm) = ok (with_vm s' vm') &
               evm s' <=1 vm'.
Proof.
  case: lv => [ vi ty | x | al w x e | al aa sz x e | aa sz len x e] /=.
  + move=> hu hvu hw; rewrite (uincl_write_none _ hvu hw).
    by have [-> _ _] := write_noneP hw; eauto.
  + by apply write_var_uincl.
  + move=> hu hvu; t_xrbindP => ?? /(get_var_uincl hu) [? -> hu1] /to_wordI [?[?[? htr1]]] /=; subst.
    have [? [? [? hw1 {hu1}]]]:= value_uinclE hu1; subst => /=.
    have -> := word_uincl_truncate hw1 htr1.
    move=> ?? /(wi2w_eP hu) [? -> hu2] /to_wordI [?[?[? htr2]]] /=; subst.
    have [? [? [? hw2 {hu2}]]]:= value_uinclE hu2; subst => /=.
    have -> := word_uincl_truncate hw2 htr2.
    move=> ? /to_wordI [?[?[? htr3]]] /=; subst.
    have [? [? [? hw3 {hvu}]]]:= value_uinclE hvu; subst => /=.
    have -> /= := word_uincl_truncate hw3 htr3.
    by move=> m' -> <- /=; exists vm.
  + move=> hu hvu; apply on_arr_varP; t_xrbindP; rewrite /on_arr_var.
    move=> ?? hty /(get_var_uincl hu) [? -> hu1] ?? /(wi2w_eP hu) [? -> hu2] /to_intI ?; subst.
    have [? ? htu]:= value_uinclE hu1; subst => /=.
    have ? := value_uinclE hu2; subst => /=.
    move=> ? /to_wordI [?[?[? htr3]]] /=; subst.
    have [? [? [? hw3 {hvu}]]]:= value_uinclE hvu; subst => /=.
    have -> /= := word_uincl_truncate hw3 htr3.
    move=> ? /(WArray.uincl_set htu) [? [-> htu']] /=.
    by apply write_var_uincl.
  move=> hu hvu; apply on_arr_varP; t_xrbindP; rewrite /on_arr_var.
  move=> ?? hty /(get_var_uincl hu) [? -> hu1] ?? /(wi2w_eP hu) [? -> hu2] /to_intI ?; subst.
  have [? ? htu {hu1} ]:= value_uinclE hu1; subst => /=.
  have ? := value_uinclE hu2; subst => /=.
  move=> ? /to_arrI ?; subst.
  have [? ? htu']:= value_uinclE hvu; subst => /=.
  rewrite WArray.castK /=.
  move=> ? /(WArray.uincl_set_sub htu htu') [? -> ?] /=.
  by apply write_var_uincl.
Qed.

Lemma wi2w_lvalsP wdb lvs s s' vm vs1 vs2 :
  evm s <=1 vm ->
  List.Forall2 value_uincl vs1 vs2 ->
  write_lvals wdb gd s lvs vs1 = ok s' ->
  exists2 vm', write_lvals wdb gd (with_vm s vm) (map wi2w_lv lvs) vs2 = ok (with_vm s' vm') &
               evm s' <=1 vm'.
Proof.
  elim: lvs s vm vs1 vs2 => /= [ | x xs Hrec] s1 vm1 vs1 vs2 Hvm [] //=.
  + by move=> [] <-;eauto.
  move=> {vs1 vs2} v1 v2 vs1 vs2 Hv Hvs;apply: rbindP => s1'.
  by move=> /(wi2w_lvalP Hvm Hv) []vm2 -> Hvm2 /(Hrec _ _ _ _ Hvm2 Hvs).
Qed.

Section Internal.

Let p' := wi2w_prog_internal p.

Lemma eq_globs : gd = p_globs p'.
Proof. done. Qed.

Lemma eq_p_extra : p_extra p = p_extra p'.
Proof. done. Qed.

Let Pi_r s (i:instr_r) s' :=
  forall vm, evm s <=1 vm ->
    exists2 vm', sem_i p' ev (with_vm s vm) (wi2w_ir i) (with_vm s' vm') &
                 evm s' <=1 vm'.

Let Pi s (i:instr) s' :=
  forall vm, evm s <=1 vm ->
    exists2 vm', sem_I p' ev (with_vm s vm) (wi2w_i i) (with_vm s' vm') &
                 evm s' <=1 vm'.

Let Pc s (c:cmd) s' :=
  forall vm, evm s <=1 vm ->
    exists2 vm', sem p' ev (with_vm s vm) (map wi2w_i c) (with_vm s' vm') &
                 evm s' <=1 vm'.

Let Pfor (i:var_i) vs s c s' :=
 forall vm, evm s <=1 vm ->
    exists2 vm', sem_for p' ev i vs (with_vm s vm) (map wi2w_i c) (with_vm s' vm') &
                 evm s' <=1 vm'.

Let Pfun scs1 m1 fn vargs scs2 m2 vres :=
  forall vargs', List.Forall2 value_uincl vargs vargs' ->
  exists2 vres',
     List.Forall2 value_uincl vres vres' &
     sem_call p' ev scs1 m1 fn vargs' scs2 m2 vres'.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof. move=> s vm; exists vm => //; constructor. Qed.

Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ hi _ hc vm hu1.
  have [? h1 hu2] := hi _ hu1.
  have [vm' h2 hu3] := hc _ hu2.
  exists vm' => //; apply: Eseq h1 h2.
Qed.

Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Proof. move=> ii i s1 s2 _ hi vm hu; have [vm' ??] := hi _ hu; exists vm' => //; constructor. Qed.

Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s1 s2 x t ty e v v' he htr hw vm hu.
  have [v1 he1 hu1] := wi2w_eP hu he.
  have [v1' htr1 hu2] := value_uincl_truncate hu1 htr.
  have [vm' hw' hu'] := wi2w_lvalP hu hu2 hw.
  exists vm' => //; econstructor; eauto.
Qed.

Local Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move => s1 s2 t o xs es; rewrite /sem_sopn; t_xrbindP => vr ve hes hex hws vm hu.
  have [vs' hes' hu1] := wi2w_esP hu hes.
  have [vr' hex' hu2] := vuincl_exec_opn hu1 hex.
  have [vm' hw' hu'] := wi2w_lvalsP hu hu2 hws.
  exists vm' => //; econstructor; eauto.
  by rewrite /sem_sopn hes' /= hex' /=.
Qed.

Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
Proof.
  move=> s1 scs m s2 o xs es ves vs hes ho hws vm hu.
  have [vs' hes' hu1] := wi2w_esP hu hes.
  have [vr' hex' hu2] := exec_syscallP ho hu1.
  have /(_ _ hu) [vm' hw' hu'] := wi2w_lvalsP _ hu2 hws.
  exists vm' => //; econstructor; eauto.
Qed.

Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 he _ hc vm hu.
  have [v1 he1 /value_uinclE ?] := wi2w_eP hu he; subst v1.
  have [vm' h1 h2] := hc _ hu.
  by exists vm' => //; apply: Eif_true h1.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 he _ hc vm hu.
  have [v1 he1 /value_uinclE ?] := wi2w_eP hu he; subst v1.
  have [vm' h1 h2] := hc _ hu.
  by exists vm' => //; apply: Eif_false h1.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 s3 s4 a c e ei c' _ hc he _ hc' _ hwh vm hu.
  have [vm1 hc1 hu1]:= hc _ hu.
  have [v1 he1 /value_uinclE ?] := wi2w_eP hu1 he; subst v1.
  have [vm2 hc2 hu2] := hc' _ hu1.
  have [vm' hwh' hu'] := hwh _ hu2.
  by exists vm' => //; apply: Ewhile_true hc2 hwh'.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 a c e ei c' _ hc he vm hu.
  have [vm' hc1 hu1]:= hc _ hu.
  have [v1 he1 /value_uinclE ?] := wi2w_eP hu1 he; subst v1.
  by exists vm' => //; apply: Ewhile_false.
Qed.

Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Proof.
  move=> s1 s2 i d lo hi c vlo vhi hlo hhi _ hfor vm hu.
  have [? hlo' /value_uinclE ?] := wi2w_eP hu hlo.
  have [? hhi' /value_uinclE ?] := wi2w_eP hu hhi; subst.
  have [vm' h hu'] := hfor _ hu.
  exists vm' => //; econstructor; eauto.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof. move=> s i c vm hu; exists vm => //; apply EForDone. Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  move=> s1 s1' s2 s3 i w ws c hw _ hc _ hfor vm hu.
  have [vm1 hw' hu1] := [elaborate write_var_uincl hu (value_uincl_refl w) hw].
  have [vm2 hs1 hu2] := hc _ hu1.
  have [vm' hs2 hu'] := hfor _ hu2.
  exists vm' => //; econstructor; eauto.
Qed.

Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
Proof.
  move=> s1 scs2 m2 s2 xs fn args vargs vs hes _ hf hws vm hu.
  have [vs' hes' hu1] := wi2w_esP hu hes.
  have [vr hu2 h] := hf _ hu1.
  rewrite /= in hws.
  have /(_ _ hu) [vm' hw' hu'] := wi2w_lvalsP _ hu2 hws.
  exists vm' => //; econstructor; eauto.
Qed.

Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
Proof.
  move=> scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hfun htra Hi Hw _ Hc Hres Hfull Hscs Hfi vargs1 hu.
  have hfun' : get_fundef (p_funcs p') fn = Some (wi2w_fun f).
  + by rewrite get_map_prog Hfun.
  move=> {Hfun}.
  case: f htra Hi Hw Hc Hres Hfull Hfi hfun' => /=.
  move=> info tyin params body tyout res extra htra hi hw hc hres hfull hfi hfun'.
  have [vargs2 {}htra hu1] := mapM2_dc_truncate_val htra hu.
  have [vm1 {}hw hu2] := [elaborate write_vars_uincl (vm_uincl_refl _) hu1 hw].
  have [vm' {}hc hu3] := hc _ hu2.
  have [vres1 {}hres hu4]:= get_var_is_uincl hu3 hres.
  have [vres2 {}hfull hu5] := mapM2_dc_truncate_val hfull hu4.
  rewrite with_vm_same in hw.
  exists vres2 => //; econstructor; first (by apply hfun'); eauto.
Qed.

Lemma wi2w_call_internalP fn scs mem scs' mem' va va' vr:
  List.Forall2 value_uincl va va' ->
  sem_call p ev scs mem fn va scs' mem' vr ->
  exists2 vr',
    List.Forall2 value_uincl vr vr' &
    sem_call p' ev scs mem fn va' scs' mem' vr'.
Proof.
  move=> Hall Hsem.
  exact:
    (sem_call_Ind
       Hskip
       Hcons
       HmkI
       Hassgn
       Hopn
       Hsyscall
       Hif_true
       Hif_false
       Hwhile_true
       Hwhile_false
       Hfor
       Hfor_nil
       Hfor_cons
       Hcall
       Hproc
       Hsem
       _
       Hall).
Qed.

End Internal.

Lemma wi2w_progP (p' : uprog) scs m fn va scs' m' vr :
  wi2w_prog remove_wint_annot dead_vars_fd p = ok p' →
  sem_call p ev scs m fn va scs' m' vr →
  exists2 vr' : seq value,
    List.Forall2 value_uincl vr vr' &
    sem_call p' ev scs m fn va scs' m' vr'.
Proof.
  rewrite /wi2w_prog; t_xrbindP => ok_pv <- h.
  have [vr1 hu1 {}h]:= wi2w_call_internalP (List_Forall2_refl _ value_uincl_refl) h.
  have [vr2 [{}h hu2]] := alloc_call_uprogP ok_pv h.
  exists vr2 => //.
  apply (Forall2_trans value_uincl_trans hu1 hu2).
Qed.

End PROOF.
