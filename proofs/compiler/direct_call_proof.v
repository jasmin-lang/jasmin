(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
From lang Require Import varmap psem.

Import Utf8.


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
    + by move=> > he > /he -> /= -> > /= -> <-.
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
    case: x => [vi t | x | ws x e | al aa ws vi e | aa ws len x e] /=; t_xrbindP.
    + by rewrite /write_none; t_xrbindP => /truncatable_weak -> /DB_weak -> ->.
    + by apply write_var_weak.
    + by move=> ? > /sem_pexpr_weak -> /= -> > -> > /= -> <-.
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

Section SEM.

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
  move=> s1 s2 s3 s4 a c e ei c' _ hc he _ hc' _ hw vm1 hle.
  have [vm2 hle2 hs2] := hc _ hle.
  have [v' he2 /value_uinclE ?]:= sem_pexpr_uincl hle2 he;subst.
  have [vm3 /hw [vm4 hle4 hs4] hs3]:= hc' _ hle2;exists vm4 => //; eapply Ewhile_true; eauto.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false (dc:=indirect_c) p ev Pc Pi_r.
Proof.
  move=> s1 s2 a c e ei c' _ hc he vm1 hle.
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
  have {}hu := Forall2_trans value_uincl_trans (mapM2_dc_truncate_value_uincl htra) hu.
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

End SEM.

Section IT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE0 : EventRels E0}.

Let Pi i :=
  wequiv_rec (dc1:=indirect_c) (dc2:=direct_c) p p ev ev uincl_spec (st_uincl tt) [::i] [::i] (st_uincl tt).

Let Pi_r i := forall ii, Pi (MkI ii i).

Let Pc c :=
  wequiv_rec (dc1:=indirect_c) (dc2:=direct_c) p p ev ev uincl_spec (st_uincl tt) c c (st_uincl tt).

Lemma checker_st_uinclP_ : Checker_uincl (dc1:=indirect_c) (dc2:=direct_c) p p checker_st_uincl.
Proof.
  constructor.
  + move=> wdb1 wdb2 d es1 es2 d' + <-; case => -[-> ->].
    + by apply read_es_st_uincl.
    by move=> ??? h /(sem_pexprs_weak false); apply: read_es_st_uincl h.
  move=> wdb1 wdb2 d xs1 xs2 d' + <-; case => -[-> ->].
  + by apply write_lvals_st_uincl.
  by move=> > hu > h /(write_lvals_weak false); apply: write_lvals_st_uincl h.
Qed.
#[local] Hint Resolve checker_st_uinclP_ : core.

Lemma it_indirect_to_direct fn :
  wequiv_f (sem_F1 := sem_fun_full (dc:=indirect_c)) (sem_F2 := sem_fun_full (dc:=direct_c))
    p p ev ev (rpreF (eS:=uincl_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof.
  apply wequiv_fun_ind => hrec {fn}.
  move=> fn _ fs1 fs2 [<-] [hscs hmem hu] fd hget; exists fd => // s.
  rewrite /initialize_funcall; t_xrbindP => vs htra s0 hinit hw.
  have -> /= := mapM2_dc_truncate_weak hu htra.
  rewrite /estate0 -hscs -hmem hinit /=.
  have {}hu := Forall2_trans value_uincl_trans (mapM2_dc_truncate_value_uincl htra) hu.
  assert (h := write_vars_uincl (vm_uincl_refl (evm s0)) hu hw).
  case: h=> vm1; rewrite with_vm_same => /(write_vars_weak false) -> {}hu.
  eexists; first reflexivity.
  exists (st_uincl tt), (st_uincl tt); split => // {s hw hu vm1 hinit vs htra s0 hscs hmem fs1 fs2}; last first.
  + move=> s t fr1 [hscs hmem hle2]; rewrite /finalize_funcall; t_xrbindP.
    move=> vres hgetr vres' htrr <-.
    have [vres2 /= hgetr2 hu2] := get_var_is_uincl hle2 hgetr.
    have -> /= : get_var_is false (evm t) (f_res fd) = ok vres2.
    + elim: (f_res fd) (vres2) hgetr2 => [ | ? ty hrec'] /=; t_xrbindP.
      + by move=> _ <-.
      by move=> > /get_varP [-> _ _] > /hrec' -> <-.
    rewrite (mapM2_dc_truncate_weak hu2 htrr) /=.
    eexists; first reflexivity.
    split => //=; first by rewrite hmem.
    by apply: (Forall2_trans value_uincl_trans) hu2; apply: mapM2_dc_truncate_value_uincl htrr.
  move: (f_body fd) => {fn fd hget}.
  apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => //; subst Pi_r Pi Pc => /=.
  + by apply wequiv_nil.
  + move=> i c hi hc.
    by apply wequiv_cons with (st_uincl tt).
  + by move=> x tg ty e ii; apply wequiv_assgn_rel_uincl with checker_st_uincl tt.
  + by move=> xs tg o es ii; apply wequiv_opn_rel_uincl with checker_st_uincl tt.
  + move=> xs sc es ii; apply wequiv_syscall_rel_uincl_core with checker_st_uincl tt => //.
    by apply fs_uincl_syscall.
  + by move=> e c1 c2 hc1 hc2 ii; apply wequiv_if_rel_uincl with checker_st_uincl tt tt tt.
  + by move=> > hc ii; apply wequiv_for_rel_uincl with checker_st_uincl tt tt.
  + by move=> > ?? ii; apply wequiv_while_rel_uincl with checker_st_uincl tt.
  move=> xs fn es ii; apply wequiv_call_rel_uincl with checker_st_uincl tt => //.
  by move=> ???; apply hrec.
Qed.

End IT.

End WITH_PARAMS.
