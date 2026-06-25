(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem_core psem compiler_util.
Require Export array_init.
Import Utf8.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

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

Section IT_REMOVE_INIT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Context (is_reg_array: var -> bool) (p : prog) (ev: extra_val_t).
Notation gd := (p_globs p).

Notation p' := (remove_init_prog is_reg_array p).

Let Pi i :=
  let im := remove_init_i is_reg_array i in
  wequiv_rec p p' ev ev uincl_spec (st_uincl tt) [::i] im (st_uincl tt).

Let Pi_r i := forall ii, Pi (MkI ii i).

Let Pc c :=
  let cm := remove_init_c is_reg_array c in
  wequiv_rec p p' ev ev uincl_spec (st_uincl tt) c cm (st_uincl tt).

#[local] Lemma checker_st_uinclP : Checker_uincl p p' checker_st_uincl.
Proof. by apply checker_st_uinclP. Qed.

#[local] Hint Resolve checker_st_uinclP : core.

Lemma it_remove_init_fdP fn : wiequiv_f p p' ev ev (rpreF (eS:= uincl_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof.
 apply wequiv_fun_ind => {}fn _ fs ft [<- hfsu] fd hget.
 exists (remove_init_fd is_reg_array fd).
 + by rewrite get_map_prog hget.
 move=> s hinit.
 have [t -> hu] :=
   [elaborate fs_uincl_initialize (p:=p) (p':=p') (fd:=fd) (fd':=remove_init_fd is_reg_array fd)
           erefl erefl erefl erefl hfsu hinit].
 exists t=> //; exists (st_uincl tt), (st_uincl tt); split => //; last by apply fs_uincl_finalize.
 clear fn fs ft hfsu hget s hinit t hu.
 rewrite /remove_init_fd /=.
 apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => // {fd}; rewrite /Pi_r /Pi /Pc /=.
 + by apply wequiv_nil.
 + by move=> > hi hc /=; rewrite -cat1s; apply wequiv_cat with (st_uincl tt).
 + move=> x tg ty e ii.
   have h : wequiv_rec p p' ev ev uincl_spec
             (st_uincl tt) [:: MkI ii (Cassgn x tg ty e)] [:: MkI ii (Cassgn x tg ty e)] (st_uincl tt).
   + apply wequiv_assgn_rel_uincl with checker_st_uincl tt => //.
   case: is_array_initP => // -[wse [len ?]]; subst e.
   case: ifP => // hx.
   apply wequiv_assign_left => s1 s1' s2 hu.
   rewrite /sem_assgn /=; t_xrbindP => v /truncate_valE [_ ?]; subst v => {h hx}.
   case: hu => hscs hmem hsub.
   case: x => [vi t | [x xi] | al ws x e | al aa ws x e | aa ws len' [x xi] e] /=.
    + by move=> /write_noneP [->].
    + move=> /write_varP_arr [/=hty _ _ ->]; split => //.
      apply vm_uincl_set_l => //=.
      have /compat_valEl := Vm.getP (evm s2) x; rewrite -hty eqxx => -[t' ->].
      by apply: WArray.uincl_empty.
    + by t_xrbindP.
    + by apply: on_arr_varP => ???; t_xrbindP.
    apply: on_arr_varP => /= tlen t ?; t_xrbindP => hg i vi hvi hi _ /WArray.cast_empty_ok ->.
    move => t1 ht1 /write_varP_arr [/= hty _ _ ->]; split => //.
    apply vm_uincl_set_l => //=.
    move: hg; rewrite /get_var; t_xrbindP => _ hx.
    have := hsub x; rewrite hx -hty eqxx => /value_uinclE [t2 -> hu].
    split => //.
    move=> k w; rewrite (WArray.set_sub_get8 ht1) /=; case: ifP => ?.
    + by rewrite WArray.get_empty; case: ifP.
    by apply hu.
  + by move=> xs tg o es ii; apply wequiv_opn_rel_uincl with checker_st_uincl tt.
  + by move=> xs sc es ii; apply wequiv_syscall_rel_uincl with checker_st_uincl tt.
  + by move=> a ii; apply wequiv_noassert.
  + by move=> e c1 c2 hc1 hc2 ii; apply wequiv_if_rel_uincl with checker_st_uincl tt tt tt.
  + by move=> > hc ii; apply wequiv_for_rel_uincl with checker_st_uincl tt tt.
  + by move=> > ?? ii; apply wequiv_while_rel_uincl with checker_st_uincl tt.
  move=> xs fn es ii; apply wequiv_call_rel_uincl with checker_st_uincl tt => //.
 move=> ???; exact/wequiv_fun_rec.
Qed.

End IT_REMOVE_INIT.

End Section.

Section IT.
Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

(* TODO : do we really need the instances ? *)
Lemma it_remove_init_fdPu is_reg_array (p : uprog) ev fn :
  wiequiv_f p (remove_init_prog is_reg_array p) ev ev (rpreF (eS:= uincl_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof. apply it_remove_init_fdP. Qed.

Lemma it_remove_init_fdPs is_reg_array (p : sprog) ev fn :
  wiequiv_f p (remove_init_prog is_reg_array p) ev ev (rpreF (eS:= uincl_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof. apply it_remove_init_fdP. Qed.

End IT.

Definition undef_except (X:Sv.t) vm :=
  forall x, ~Sv.In x X ->  vm.[x] = undef_addr (eval_atype (vtype x)).

Section IT_ADD_INIT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Context (p : uprog) (ev:unit).

Notation gd := (p_globs p).

Notation p' := (add_init_prog p).

(* two states are related wrt varset I iff they are extensionally
equal and undefined except for I *)
Definition undef_vm_eq (I : Sv.t) (vm1 vm2 : Vm.t) :=
  undef_except I vm1 /\  (vm1 =1 vm2)%vm.

Definition cmpl_inv (I : Sv.t) := st_rel undef_vm_eq I.

Lemma cmpl_inv_incl I1 I2 s1 s2 : Sv.Subset I1 I2 -> cmpl_inv I1 s1 s2 → cmpl_inv I2 s1 s2.
Proof.
  move=> hincl [h1 h2 [h3 h4]]; split => //; split => //.
  move=> z hz; apply h3; SvD.fsetdec.
Qed.

Let Pi i :=
  forall I,
    let im := add_init_i I i in
    wequiv_rec p p' ev ev eq_spec (cmpl_inv I) [::i] im.1 (cmpl_inv im.2).

Let Pi_r i := forall ii, Pi (MkI ii i).

Let Pc c :=
  forall I,
    let cm :=  add_init_c add_init_i I c in
    wequiv_rec p p' ev ev eq_spec (cmpl_inv I) c cm.1 (cmpl_inv cm.2).

Lemma add_init_auxP ii c c' I I' X :
 disjoint I X ->
 wequiv_rec p p' ev ev eq_spec (cmpl_inv I) c c' (cmpl_inv I') ->
 wequiv_rec p p' ev ev eq_spec (cmpl_inv I) c (Sv.fold (add_init_aux ii) X c') (cmpl_inv I').
Proof.
  move=> hdisj hs; rewrite Sv.fold_spec.
  have h : forall x, x \in Sv.elements X -> ~Sv.In x I.
  + by move: hdisj; rewrite /disjoint => /Sv.is_empty_spec hdisj x /Sv_elemsP; SvD.fsetdec.
  elim: Sv.elements c c' h hs => [ | x xs ih] c c' {}hdisj hcc' //=.
  apply ih.
  + by move=> z hz; apply hdisj; rewrite in_cons hz orbT.
  rewrite /add_init_aux.
  case heq: vtype => [||len|] //; case:ifP => _ //.
  rewrite -(cat0s c) -cat1s.
  apply wequiv_cat with (cmpl_inv I) => //.
  apply wequiv_assign_right => s t h.
  rewrite /sem_assgn /=  /truncate_val /= WArray.castK /=.
  eexists.
  + by apply write_varP; split => //; rewrite heq /= eqxx.
  case h => h1 h2 [h3 h4]; split => //; split => //.
  move: h4; rewrite !vm_eq_vm_rel => hu1; apply vm_rel_set_r.
  + move=> _ /=; rewrite h3.
    + by rewrite heq /= eqxx.
    by apply/hdisj/mem_head.
  by apply: vm_relI hu1.
Qed.

Lemma it_aux I ii1 ii i :
  wequiv_rec p p' ev ev eq_spec (cmpl_inv I)
     [:: MkI ii i]
     (add_init ii1 I (Sv.union (write_i i) (read_i i)) (MkI ii i)) (cmpl_inv (Sv.union I (write_i i))).
Proof.
  apply add_init_auxP; first by apply/Sv.is_empty_spec; SvD.fsetdec.
  apply wkequivP' => s t.
  have h := [elaborate wequiv_rec_st_eq (p:=p) (p':=p') ev ev erefl [:: MkI ii i]].
  have /(_ s) {h} := wequiv_write1 h.
  apply wkequiv_weaken => //.
  + by move=> s1 s2 [ [-> ->] [?? []]].
  move=> ???? [[-> ->] [_ _ [hundef _]]] [h1] [?? heq2]; split => //; split => //.
  move=> z hz; rewrite -h1.
  + by apply hundef; SvD.fsetdec.
  rewrite write_c_cons write_c_nil write_Ii; SvD.fsetdec.
Qed.

Lemma it_add_init_callP fn : wiequiv_f p p' ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
 apply wequiv_fun_ind => {}fn _ fs _ [<- <-] fd hget.
 exists (add_init_fd fd).
 + by rewrite get_map_prog hget.
 move=> {hget}.
 rewrite /add_init_fd /=.
 set I := (I in add_init_c _ I _).
 set cm := add_init_c _ _ _.
 set fd' := with_body _ _.
 move=> s1 hinit.
 exists s1=> //; exists (cmpl_inv I), (cmpl_inv cm.2); split => //.
 + move: hinit; rewrite /initialize_funcall.
   t_xrbindP => vs hargs s0 hini hw.
   split => //; split => //.
   move=> x hx.
   move: hw; rewrite (write_vars_lvals _ gd) => /disjoint_eq_ons -/(_ (Sv.singleton x)) <-.
   + by move: hini => [<-] /=; rewrite Vm.initP.
   + by rewrite -/I /disjoint /is_true Sv.is_empty_spec; SvD.fsetdec.
   by SvD.fsetdec.
 2:{
   move=> s2 t2 fs2 h.
   rewrite /finalize_funcall; t_xrbindP => vs hget vs' hmap <-.
   eexists; last by eauto.
   case: h => [<- <- [_ h]].
   have -> /= : get_var_is (~~ direct_call) (evm t2) (f_res fd') = ok vs.
   + by rewrite -hget; apply mapM_ext => // y; rewrite /get_var -h.
   by rewrite hmap.
 }

 apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => // {fd fn fs hinit cm I fd' s1}.
 + by move=> I /=; apply wequiv_nil.
 + move=> i c hi hc I /=.
   case heqi: add_init_i => [i' I'].
   case heqc: add_init_c => [c' I''] /=.
   rewrite -cat1s.
   apply wequiv_cat with (cmpl_inv I').
   + by have /= := hi I; rewrite heqi.
   by have /= := hc I'; rewrite heqc.
 1-4, 6-8: by move=> * ii I; apply/it_aux.
 move=> e c1 c2 hc1 hc2 ii I /=.
 case heq1 : add_init_c => [c1' I1].
 case heq2 : add_init_c => [c2' I2] /=.
 apply add_init_auxP.
 + by apply/Sv.is_empty_spec; SvD.fsetdec.
 apply wequiv_if_eq.
 + apply wrequiv_weaken with (st_eq tt) eq => //.
   + by move=> ?? [?? []].
   by apply st_eq_sem_pexpr.
 move=> [].
 + have := hc1 I; rewrite heq1; apply: wequiv_weaken => //=.
   by move=> ??; apply cmpl_inv_incl; SvD.fsetdec.
 have := hc2 I; rewrite heq2; apply: wequiv_weaken => //=.
 by move=> ??; apply cmpl_inv_incl; SvD.fsetdec.
Qed.

End IT_ADD_INIT.

End WITH_PARAMS.
