(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
Require Import varmap psem.

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

Lemma mapM2_dc_truncate_weak ty vs1 vs2 vs' :
  values_uincl vs1 vs2 ->
  mapM2 ErrType (dc_truncate_val (dc:=indirect_c)) ty vs1 = ok vs' ->
  mapM2 ErrType (dc_truncate_val (dc:=direct_c)) ty vs2 = ok vs2.
Proof.
  by elim: ty vs1 vs2 vs' => [| t ty hrec] > [] // > _ hu /=; t_xrbindP => > _ > /(hrec _ _ _ hu) ->.
Qed.

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
  wiequiv_f (dc1:=indirect_c) (dc2:=direct_c)
    p p ev ev (rpreF (eS:=uincl_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof.
  apply wequiv_fun_ind => {}fn _ fs1 fs2 [<-] [hscs hmem hu] fd hget.
  exists fd => // s.
  rewrite /initialize_funcall; t_xrbindP => vs htra s0 hinit hw.
  have -> /= := mapM2_dc_truncate_weak hu htra.
  rewrite /estate0 -hscs -hmem hinit /=.
  have {}hu := values_uincl_trans (mapM2_dc_truncate_value_uincl htra) hu.
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
    by apply: values_uincl_trans hu2; apply: mapM2_dc_truncate_value_uincl htrr.
  move: (f_body fd) => {fn fd hget}.
  apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => //; subst Pi_r Pi Pc => /=.
  + by apply wequiv_nil.
  + move=> i c hi hc.
    by apply wequiv_cons with (st_uincl tt).
  + by move=> x tg ty e ii; apply wequiv_assgn_rel_uincl with checker_st_uincl tt.
  + by move=> xs tg o es ii; apply wequiv_opn_rel_uincl with checker_st_uincl tt.
  + move=> xs sc es ii; apply wequiv_syscall_rel_uincl_core with checker_st_uincl tt => //.
    by apply fs_uincl_syscall.
  + by move=> >; apply wequiv_noassert.
  + by move=> e c1 c2 hc1 hc2 ii; apply wequiv_if_rel_uincl with checker_st_uincl tt tt tt.
  + by move=> > hc ii; apply wequiv_for_rel_uincl with checker_st_uincl tt tt.
  + by move=> > ?? ii; apply wequiv_while_rel_uincl with checker_st_uincl tt.
  move=> xs fn es ii; apply wequiv_call_rel_uincl with checker_st_uincl tt => //.
  by move=> ???; apply: wequiv_fun_rec.
Qed.

End IT.

End WITH_PARAMS.
