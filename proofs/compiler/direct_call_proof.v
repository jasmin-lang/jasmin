(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
Require Import varmap psem.

Import Utf8.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** proofs
 * -------------------------------------------------------------------- *)

Section WITH_PARAMS.

Context
  {wsw:WithSubWord}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {sCP : semCallParams}.

Context (p:prog) (ev:extra_val_t).

#[local] Open Scope vm_scope.

Let Pi_r s1 (i:instr_r) s2:=
  forall (vm1:Vm.t), evm s1 <=1 vm1 ->
  exists2 vm2, evm s2 <=1 vm2 & sem_i (dc:= direct_c) p ev (with_vm s1 vm1) i (with_vm s2 vm2).

Let Pi s1 (i:instr) s2:=
  forall (vm1:Vm.t), evm s1 <=1 vm1 ->
  exists2 vm2, evm s2 <=1 vm2 & sem_I (dc:= direct_c) p ev (with_vm s1 vm1) i (with_vm s2 vm2).

Let Pc s1 (c:cmd) s2:=
  forall (vm1:Vm.t), evm s1 <=1 vm1 ->
  exists2 vm2, evm s2 <=1 vm2 & sem (dc:= direct_c) p ev (with_vm s1 vm1) c (with_vm s2 vm2).

Let Pfor (i:var_i) vs s1 c s2 :=
  forall (vm1:Vm.t), evm s1 <=1 vm1 ->
  exists2 vm2, evm s2 <=1 vm2 & sem_for (dc:= direct_c) p ev i vs (with_vm s1 vm1) c (with_vm s2 vm2).

Let Pfun scs m fn vargs scs' m' vres :=
  forall vargs', List.Forall2 value_uincl vargs vargs' ->
  exists2 vres',
    sem_call (dc:= direct_c) p ev scs m fn vargs' scs' m' vres' &
    List.Forall2 value_uincl vres vres'.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof. move=> s1 vm1 hle; eexists; eauto; constructor. Qed.

Local Lemma Hcons : sem_Ind_cons (dc:=indirect_c) p ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ hi _ hc vm1 /hi [] vm2 /hc [vm3] hle hc' hi'.
  exists vm3 => //; econstructor; eauto.
Qed.

Local Lemma HmkI : sem_Ind_mkI (dc:=indirect_c) p ev Pi_r Pi.
Proof. move=> ii i s1 s2 _ hi vm1 /hi [vm2 hle hi']; exists vm2 => //; constructor. Qed.

Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s1 s2 x t ty e v v' he htr hw vm1 hle.
  have [v1 he1 hu1]:= sem_pexpr_uincl hle he.
  have [v1' htr1 hu1' ] := value_uincl_truncate hu1 htr.
  have [vm2 hw2 hle2]:= write_uincl hle hu1' hw.
  exists vm2 => //; econstructor; eauto.
Qed.

Local Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move => s1 s2 t o xs es; rewrite /sem_sopn; t_xrbindP => vrs ves hes hex hws vm1 hle.
  have [ves1 hes1 hu1]:= sem_pexprs_uincl hle hes.
  have [vrs1 hex1 hu1'] := vuincl_exec_opn hu1 hex.
  have [vm2 hws2 hle2]:= writes_uincl hle hu1' hws.
  exists vm2 => //; econstructor; eauto.
  by rewrite /sem_sopn hes1 /= hex1 /= hws2.
Qed.

Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
Proof.
  move=> s1 scs m s2 o xs es ves vs hes hex hws vm1 hle.
  have [ves1 hes1 hu1]:= sem_pexprs_uincl hle hes.
  have [vrs1 hex1 hu1'] := exec_syscallP hex hu1.
  have  [vm2 Hw ?]:= writes_uincl (s1 := with_scs (with_mem s1 m) scs) hle hu1' hws.
  exists vm2 => //; econstructor; eauto.
Qed.

Local Lemma Hif_true : sem_Ind_if_true (dc:=indirect_c) p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 he _ hc vm1 hle.
  have [v' he1 /value_uinclE ?]:= sem_pexpr_uincl hle he; subst v'.
  by have [vm2 ??]:= hc _ hle;exists vm2 => //; apply Eif_true.
Qed.

Local Lemma Hif_false : sem_Ind_if_false (dc:=indirect_c) p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 he _ hc vm1 hle.
  have [v' he1 /value_uinclE ?]:= sem_pexpr_uincl hle he; subst v'.
  by have [vm2 ??]:= hc _ hle;exists vm2 => //; apply Eif_false.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true (dc:=indirect_c) p ev Pc Pi_r.
Proof.
  move=> s1 s2 s3 s4 a c e c' _ hc he _ hc' _ hw vm1 hle.
  have [vm2 hle2 hs2] := hc _ hle.
  have [v' he2 /value_uinclE ?]:= sem_pexpr_uincl hle2 he;subst.
  have [vm3 /hw [vm4 hle4 hs4] hs3]:= hc' _ hle2;exists vm4 => //; eapply Ewhile_true; eauto.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false (dc:=indirect_c) p ev Pc Pi_r.
Proof.
  move=> s1 s2 a c e c' _ hc he vm1 hle.
  have [vm2 hle2 hs2] := hc _ hle.
  have [v' he' /value_uinclE ?]:= sem_pexpr_uincl hle2 he;subst.
  by exists vm2 => //;apply: Ewhile_false.
Qed.

Local Lemma Hfor : sem_Ind_for (dc:=indirect_c) p ev Pi_r Pfor.
Proof.
  move=> s1 s2 i d lo hi c vlo vhi hlo hhi _ hfor vm1 hle.
  have [? ? /value_uinclE ?]:= sem_pexpr_uincl hle hlo;subst.
  have [? ? /value_uinclE ?]:= sem_pexpr_uincl hle hhi;subst.
  by have [vm2 ??]:= hfor _ hle; exists vm2 => //; econstructor; eauto.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof. by move=> s i c vm1 ?;exists vm1 => //;constructor. Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons (dc:=indirect_c) p ev Pc Pfor.
Proof.
  move=> s1 s1' s2 s3 i w ws c hw _ hc _ hf vm1 hle.
  have [vm1' Hi' /hc] := write_var_uincl hle (value_uincl_refl _) hw.
  move=> [vm2 /hf [vm3 hle3 ?] ?]; exists vm3 => //; econstructor; eauto.
Qed.

Section EXPR.

  Context (wdb : bool) (gd : glob_decls) (s : estate).

  Let P e : Prop := forall v, sem_pexpr true gd s e = ok v -> sem_pexpr wdb gd s e = ok v.

  Let Q es : Prop := forall vs, sem_pexprs true gd s es = ok vs -> sem_pexprs wdb gd s es = ok vs.

  Lemma get_var_weak vm x v : get_var true vm x = ok v → get_var wdb vm x = ok v.
  Proof. by move => /get_varP []; rewrite /get_var /= => -> -> _; rewrite orbT. Qed.

  Lemma get_gvar_weak vm (x : gvar) v : get_gvar true gd vm x = ok v → get_gvar wdb gd vm x = ok v.
  Proof. rewrite /get_gvar; case: ifP => // _; apply get_var_weak. Qed.

  Lemma sem_pexpr_weak_and : (∀ e, P e) ∧ (∀ es, Q es).
  Proof.
    apply: pexprs_ind_pair; subst P Q; split => //=; t_xrbindP.
    + by move=> e he es hes vs v /he -> /= ? /hes -> <-.
    + by apply get_gvar_weak.
    + move=> > he >; apply on_arr_gvarP => ?? hty /get_gvar_weak -> /=.
      by t_xrbindP => > /he -> /= -> /= > -> <-.
    + move=> > he >; apply on_arr_gvarP => ?? hty /get_gvar_weak -> /=.
      by t_xrbindP => > /he -> /= -> /= > -> <-.
    + by move=> > he > /get_var_weak -> /= -> > /he -> /= -> > /= -> <-.
    + by move=> > he > /he -> /= ->.
    + by move=> > he1 > he2 > /he1 -> /= > /he2 -> /= ->.
    + by move=> > hes > /hes; rewrite /sem_pexprs => -> /= ->.
    by move=> > he > he1 > he2 > /he -> /= > -> /= > /he1 -> /= -> /= > /he2 -> /= -> <-.
  Qed.

  Lemma sem_pexpr_weak e v : sem_pexpr true gd s e = ok v -> sem_pexpr wdb gd s e = ok v.
  Proof. case: sem_pexpr_weak_and => h _; apply:h. Qed.

  Lemma sem_pexprs_weak es vs : sem_pexprs true gd s es = ok vs -> sem_pexprs wdb gd s es = ok vs.
  Proof. case: sem_pexpr_weak_and => _ h; apply:h. Qed.

  Lemma truncatable_weak t v : truncatable true t v -> truncatable wdb t v.
  Proof.
    move=> /vm_truncate_valE; case: v.
    1-3: by move=> > [] ->.
    + by move=> > [] > [-> /= ->]; rewrite orbT.
    by move=> > [].
  Qed.

  Lemma DB_weak v : DB true v -> DB wdb v.
  Proof. by rewrite /DB /= => ->; rewrite orbT. Qed.

  Lemma set_var_weak vm x v vm' : set_var true vm x v = ok vm' -> set_var wdb vm x v = ok vm'.
  Proof. by rewrite /set_var; t_xrbindP => /DB_weak -> /truncatable_weak -> <-. Qed.

  Lemma write_var_weak x v s' : write_var true x v s = ok s' → write_var wdb x v s = ok s'.
  Proof. by rewrite /write_var; t_xrbindP => > /set_var_weak -> <-. Qed.

  Lemma write_lval_weak s' x v : write_lval true gd x v s = ok s' -> write_lval wdb gd x v s = ok s'.
  Proof.
    case: x => [vi t | x | ws x e | al aa ws x e | aa ws len x e] /=; t_xrbindP.
    + by rewrite /write_none; t_xrbindP => /truncatable_weak -> /DB_weak -> ->.
    + by apply write_var_weak.
    + by move=> ? > /get_var_weak -> /= -> > /sem_pexpr_weak -> /= -> > -> > /= -> <-.
    + apply on_arr_varP => > ? /get_var_weak -> /=.
      by t_xrbindP => > /sem_pexpr_weak -> /= -> > -> > /= -> /write_var_weak /= ->.
    apply on_arr_varP => > ? /get_var_weak -> /=.
    by t_xrbindP => > /sem_pexpr_weak -> /= -> > -> > /= -> /write_var_weak /= ->.
  Qed.

End EXPR.

Lemma write_vars_weak wdb s xs vs s' : write_vars true xs vs s = ok s' → write_vars wdb xs vs s = ok s'.
Proof.
  elim: xs vs s => [ | x xs hrec] [ | v vs] //= s.
  by t_xrbindP => > /(write_var_weak wdb) -> /= /hrec.
Qed.

Lemma write_lvals_weak wdb gd s s' xs vs :
  write_lvals true gd s xs vs = ok s' → write_lvals wdb gd s xs vs = ok s'.
Proof.
  elim: xs vs s => [ | x xs hrec] [ | v vs] //= s.
  by t_xrbindP => > /(write_lval_weak wdb) -> /= /hrec.
Qed.

Local Lemma Hcall : sem_Ind_call (dc:=indirect_c) p ev Pi_r Pfun.
Proof.
  move=> s1 scs2 m2 s2 xs fn args vargs vs hargs _ hrec hws vm1 hle.
  have [vargs' /(sem_pexprs_weak false) hargs1 /hrec[vres' hc hu]]:= sem_pexprs_uincl hle hargs.
  have [vm2 /(write_lvals_weak false)hws2 hle2]:= writes_uincl (s1 := with_scs (with_mem s1 m2) scs2) hle hu hws.
  exists vm2 => //; econstructor; eauto.
Qed.

Lemma mapM2_dc_truncate_weak ty vs1 vs2 vs' :
  List.Forall2 value_uincl vs1 vs2 ->
  mapM2 ErrType (dc_truncate_val (dc:=indirect_c)) ty vs1 = ok vs' ->
  mapM2 ErrType (dc_truncate_val (dc:=direct_c)) ty vs2 = ok vs2.
Proof.
  by elim: ty vs1 vs2 vs' => [| t ty hrec] > [] // > _ hu /=; t_xrbindP => > _ > /(hrec _ _ _ hu) ->.
Qed.

Local Lemma Hproc : sem_Ind_proc (dc:=indirect_c) p ev Pc Pfun.
Proof.
  move=> scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' hget htra hinit hw _ hc hgetr htrr -> -> vargs1 hu.
  have htra1 := mapM2_dc_truncate_weak hu htra.
  have {hu} hu:= Forall2_trans value_uincl_trans (mapM2_dc_truncate_value_uincl htra) hu.
  assert (h := write_vars_uincl (vm_uincl_refl (evm s0)) hu hw).
  case: h=> vm1; rewrite with_vm_same => /(write_vars_weak false) hw1 /hc [vm2 hle2 hc2].
  have [vres2 hgetr2 hu2] := get_var_is_uincl hle2 hgetr.
  have htrr2 := mapM2_dc_truncate_weak hu2 htrr.
  exists vres2; last first.
  + by apply: (Forall2_trans value_uincl_trans) hu2; apply: mapM2_dc_truncate_value_uincl htrr.
  econstructor; eauto => /=.
  elim: (f_res f) (vres2) hgetr2 => [ | t ty hrec] /=; t_xrbindP.
  + by move=> _ <-.
  by move=> > /get_varP [-> _ _] > /hrec -> <-.
Qed.

Lemma indirect_to_direct scs m fn va scs' m' vr :
  sem_call (dc := indirect_c) p ev scs m fn va scs' m' vr →
  exists2 vr',
    List.Forall2 value_uincl vr vr' &
    sem_call (dc := direct_c) p ev scs m fn va scs' m' vr'.
Proof.
  move=> Hsem.
  have [ ] :=
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
         va
         (List_Forall2_refl va value_uincl_refl)). eauto.
Qed.

End WITH_PARAMS.
