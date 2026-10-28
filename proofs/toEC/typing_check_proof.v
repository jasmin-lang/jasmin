(* * Properties of the type checker [check_prog]

   A well typed program does not fail in the total mode on the code that
   [dead_code] and [dead_args] remove ([total_ok]). In the total mode the
   memory and array accesses and the operators do not fail, and a variable
   reads a defined value of its type: a well typed expression evaluates to a
   defined value of its type, a well typed destination accepts the values of
   its type, a valid operator runs on well typed arguments. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq word_ssrZ.
Require Import compiler_util psem psem_facts values_facts sopn_facts sem_op_typed_facts.
Require Import typing_check dead_code_total_proof.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Section PROOF.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}.

Lemma check_typeP te ty :
  check_type te ty = ok tt -> subctype (eval_atype ty) (eval_atype te).
Proof. by rewrite /check_type; case: ifP => // h _; apply: subatype_subctype. Qed.

Lemma check_global_declP g d :
  check_global_decl (g, d) = ok tt -> type_of_val (gv2val d) = eval_atype (vtype g).
Proof.
rewrite /check_global_decl; case: d => [ws w | len a] /=; case: (vtype g) => //=.
+ by move=> ?; case: eqP => // ->.
by move=> ??; case: Z.eqb_spec => // ->.
Qed.

Lemma check_lvalsP gd xs tys :
  check_lvals gd xs tys = ok tt ->
  List.Forall2 (fun x ty => check_lval gd x ty = ok tt) xs tys.
Proof.
rewrite /check_lvals; elim: xs tys => [ | x xs ih] [ | ty tys] //=.
t_xrbindP => hx /ih hxs.
by constructor.
Qed.

Section GD.

Context (gd : glob_decls) (hgd : allM check_global_decl gd = ok tt).

(* A declared global reads a value of its type. *)
Lemma get_gvar_total_ok vm x ty :
  ty_gvar gd x = ok ty ->
  exists2 v, get_gvar (sm := total) true gd vm x = ok v &
    type_of_val v = eval_atype ty /\ is_defined v.
Proof using hgd.
rewrite /ty_gvar /get_gvar; case: ifP => _.
+ by move=> [<-]; apply get_var_total_ok.
rewrite /get_global; case h: get_global_value => [d | //] [<-].
have ht := check_global_declP (allMP (assoc_mem' h) hgd); rewrite ht eqxx.
by exists (gv2val d) => //; split => //; case: (d).
Qed.

(* A well typed expression evaluates in the total mode to a defined value of
   its type. *)
Lemma ty_expr_total_ok s e ty :
  ty_expr gd e = ok ty ->
  exists2 v, sem_pexpr (sm := total) true gd s e = ok v &
    type_of_val v = eval_atype ty /\ is_defined v.
Proof using hgd.
elim: e ty => [z | b | ws n | x | al aa ws x e ih | aa ws len x e ih | al ws e ih
              | o e ih | o e1 ih1 e2 ih2 | o es ih | t e ih e1 ih1 e2 ih2] ty /=.
1-3: by move=> [<-]; eexists.
+ by apply: get_gvar_total_ok.
+ rewrite /ty_get_set; t_xrbindP => tx hx te /ih [vi hvi [hti hdi]].
  rewrite /check_array /check_int.
  case: tx hx => // wsa n hx _ /check_typeP /= /eqP hte <-.
  have [vx hvx [htx hdx]] := get_gvar_total_ok (evm s) hx.
  move: htx; rewrite /= => /type_of_valI [a ?]; subst vx.
  rewrite /on_arr_var hvx /= hvi /=.
  move: hti hdi; rewrite -hte => /type_of_valI [-> // | [z ->]] _ /=.
  rewrite /WArray.get.
  have : is_ok (CoreMem.read (sm := total) a al (z * mk_scale aa ws)%Z ws).
  - by apply: CoreMem.read_total_ok.
  by case: CoreMem.read => // w _ /=; eexists.
+ rewrite /ty_get_set_sub; t_xrbindP => tx hx te /ih [vi hvi [hti hdi]].
  rewrite /check_array /check_int.
  case: tx hx => // wsa n hx _ /check_typeP /= /eqP hte <-.
  have [vx hvx [htx hdx]] := get_gvar_total_ok (evm s) hx.
  move: htx; rewrite /= => /type_of_valI [a ?]; subst vx.
  rewrite /on_arr_var hvx /= hvi /=.
  move: hti hdi; rewrite -hte => /type_of_valI [-> // | [z ->]] _ /=.
  by eexists.
+ rewrite /ty_load_store /check_ptr.
  t_xrbindP => te /ih [vi -> [hti hdi]] /check_typeP; rewrite -hti => hsub <- /=.
  have [p hp] := of_val_defined_ok hdi hsub.
  move: hp => /= -> /=.
  have : is_ok (CoreMem.read (sm := total) (emem s) al p ws).
  - by apply: CoreMem.read_total_ok.
  by case: CoreMem.read => // w _ /=; eexists.
+ move=> hc.
  have {hc} : check_expr (ty_expr gd) e (type_of_op1 o).1 >> ok (type_of_op1 o).2 = ok ty.
  - by move: hc; case: type_of_op1.
  rewrite /check_expr.
  t_xrbindP => te /ih [v1 -> [ht1 hd1]] /check_typeP; rewrite -ht1 => hsub <- /=.
  have [x1 hx1] := of_val_defined_ok hd1 hsub.
  rewrite /sem_sop1 hx1 /=.
  by eexists; first reflexivity; apply: to_val_typed.
+ move=> hc.
  have {hc} :
    check_expr (ty_expr gd) e1 (type_of_op2 o).1.1 >>
    (check_expr (ty_expr gd) e2 (type_of_op2 o).1.2 >> ok (type_of_op2 o).2) = ok ty.
  - by move: hc; case: type_of_op2 => [[]].
  rewrite /check_expr.
  t_xrbindP => te1 /ih1 [v1 -> [ht1 hd1]] /check_typeP; rewrite -ht1 => hsub1.
  move=> te2 /ih2 [v2 -> [ht2 hd2]] /check_typeP; rewrite -ht2 => hsub2 <- /=.
  have [x1 hx1] := of_val_defined_ok hd1 hsub1.
  have [x2 hx2] := of_val_defined_ok hd2 hsub2.
  rewrite /sem_sop2 hx1 hx2 /=.
  by eexists; first reflexivity; apply: to_val_typed.
+ move=> hc.
  have {hc} : check_exprs (ty_expr gd) es (type_of_opN o).1 >> ok (type_of_opN o).2 = ok ty.
  - by move: hc; case: type_of_opN.
  t_xrbindP => hes <-.
  have [vs -> hvs] :
    exists2 vs, mapM (sem_pexpr (sm := total) true gd s) es = ok vs &
      List.Forall2 (fun t v => is_defined v /\ subctype t (type_of_val v))
        (map eval_atype (type_of_opN o).1) vs.
  - elim: es (type_of_opN o).1 ih hes => [ | e es ihes] [ | t ts] //= ih.
    + by move=> _; exists [::].
    rewrite /check_exprs /= /check_expr.
    t_xrbindP => te /(ih e (or_introl erefl)) [v -> [ht hd]] /check_typeP.
    rewrite -ht => hsub /(ihes ts (fun e h => ih e (or_intror h))) [vs -> hvs] /=.
    by eexists; first reflexivity; constructor.
  have [r hr] := app_sopn_ok (sem_opN_typed_ok o) hvs.
  rewrite /sem_opN /= hr /=.
  by eexists; first reflexivity; apply: to_val_typed.
rewrite /check_expr.
t_xrbindP => te /ih [b -> [htb hdb]] /check_typeP; rewrite -htb => hsubb.
move=> te1 /ih1 [v1 -> [ht1 hd1]] /check_typeP; rewrite -ht1 => hsub1.
move=> te2 /ih2 [v2 -> [ht2 hd2]] /check_typeP; rewrite -ht2 => hsub2 <- /=.
have [xb hxb] := of_val_defined_ok hdb hsubb; move: hxb => /= -> /=.
have [w1 -> [htw1 hdw1]] := truncate_val_defined_ok hd1 hsub1.
have [w2 -> [htw2 hdw2]] := truncate_val_defined_ok hd2 hsub2.
by eexists; first reflexivity; case: (xb).
Qed.

Lemma check_exprs_total_ok s es tys :
  check_exprs (ty_expr gd) es tys = ok tt ->
  exists2 vs, sem_pexprs (sm := total) true gd s es = ok vs &
    List.Forall2 (fun t v => is_defined v /\ subctype t (type_of_val v)) (map eval_atype tys) vs.
Proof using hgd.
elim: es tys => [ | e es ih] [ | t ts] //=; first by move=> _; exists [::].
rewrite /check_exprs /= /check_expr.
t_xrbindP => te /(ty_expr_total_ok s) [v -> [ht hd]] /check_typeP; rewrite -ht => hsub.
move=> /ih [vs hvs hall]; rewrite /sem_pexprs /= -/(sem_pexprs _ _ _ es) hvs /=.
by eexists; first reflexivity; constructor.
Qed.

(* A well typed destination accepts the values of its type. *)
Lemma check_lval_total_ok x ty v s :
  check_lval gd x ty = ok tt ->
  type_of_val v = eval_atype ty -> DB true v ->
  is_ok (write_lval (sm := total) true gd x v s).
Proof using hgd.
rewrite /check_lval; t_xrbindP => tx htx /check_typeP + hty hdb.
rewrite -hty => hsub.
case: x htx => [ii t | x | al ws x e | al aa ws x e | aa ws len x e] /=.
+ by move=> [?]; subst t; rewrite /write_none (subctype_truncatable _ hsub) hdb.
+ by move=> [?]; subst tx; apply: write_var_total_ok.
+ rewrite /ty_load_store /check_ptr.
  t_xrbindP => te /(ty_expr_total_ok s) [vp -> [htp hdp]] /check_typeP.
  rewrite -htp => hsubp ?; subst tx.
  have [p hp] := of_val_defined_ok hdp hsubp; move: hp => /= -> /=.
  have hdv : is_defined v by move: hdb hsub; rewrite /DB /=; case/orP => // /eqP ->.
  have [w hw] := of_val_defined_ok hdv hsub; move: hw => /= -> /=.
  have : is_ok (CoreMem.write (sm := total) (emem s) al p w).
  - by apply: CoreMem.write_total_ok.
  by case: CoreMem.write.
+ rewrite /ty_get_set /ty_gvar /=.
  t_xrbindP => te /(ty_expr_total_ok s) [vi -> [hti hdi]].
  rewrite /check_array /check_int.
  case hx: (ty_var x) => [||wsa n|] // _ /check_typeP /= /eqP hte ?; subst tx.
  have [vx hvx [htx hdx]] := get_var_total_ok (evm s) x.
  move: htx; rewrite -/(ty_var x) hx /= => /type_of_valI [a ?]; subst vx.
  rewrite /on_arr_var hvx /=.
  move: hti hdi; rewrite -hte => /type_of_valI [-> // | [z ->]] _ /=.
  have hdv : is_defined v by move: hdb hsub; rewrite /DB /=; case/orP => // /eqP ->.
  have [w hw] := of_val_defined_ok hdv hsub; move: hw => /= -> /=.
  rewrite /WArray.set.
  have : is_ok (CoreMem.write (sm := total) a al (z * mk_scale aa ws)%Z w).
  - by apply: CoreMem.write_total_ok.
  case: CoreMem.write => // a' _ /=.
  by apply: write_var_total_ok => //; rewrite -/(ty_var x) hx.
rewrite /ty_get_set_sub /ty_gvar /=.
t_xrbindP => te /(ty_expr_total_ok s) [vi -> [hti hdi]].
rewrite /check_array /check_int.
case hx: (ty_var x) => [||wsa n|] // _ /check_typeP /= /eqP hte ?; subst tx.
have [vx hvx [htx hdx]] := get_var_total_ok (evm s) x.
move: htx; rewrite -/(ty_var x) hx /= => /type_of_valI [a ?]; subst vx.
rewrite /on_arr_var hvx /=.
move: hti hdi; rewrite -hte => /type_of_valI [-> // | [z ->]] _ /=.
have hdv : is_defined v by move: hdb hsub; rewrite /DB /=; case/orP => // /eqP ->.
have [w hw] := of_val_defined_ok hdv hsub; move: hw => /= -> /=.
by apply: write_var_total_ok => //; rewrite -/(ty_var x) hx.
Qed.

Lemma check_lvals_total_ok xs tys vs s :
  check_lvals gd xs tys = ok tt ->
  List.Forall2 (fun t v => type_of_val v = eval_atype t /\ DB true v) tys vs ->
  is_ok (write_lvals (sm := total) true gd s xs vs).
Proof using hgd.
move=> hc hall; elim: hall xs hc s => {tys vs} [ | t v ts vs [ht hdb] _ ih] [ | x xs] //= hc s.
rewrite /check_lvals /= in hc; move: hc; t_xrbindP => hx hxs.
have := check_lval_total_ok s hx ht hdb; case: write_lval => //= s' _.
by apply: ih.
Qed.

End GD.

Section PROG.

Context (p : uprog) (hgd : allM check_global_decl (p_globs p) = ok tt).

Let Pi i := check_instr (p_globs p) (p_funcs p) i = ok tt -> total_ok_i p i.
Let Pr ir := forall ii, Pi (MkI ii ir).
Let Pc c :=
  allM (check_instr (p_globs p) (p_funcs p)) c = ok tt ->
  (fix total_ok_c (c : cmd) : Prop :=
     if c is i :: c then total_ok_i p i /\ total_ok_c c else True) c.

Lemma check_cmd_total_ok c : Pc c.
Proof using hgd.
apply: (cmd_rect (Pr := Pr) (Pi := Pi) (Pc := Pc)) => //; subst Pr Pi Pc => /=.
+ move=> i c0 hi hc; rewrite /allM /=; t_xrbindP => /hi ? /hc.
  by split.
+ move=> x tg ty e ii /=; rewrite /check_expr.
  t_xrbindP => te /(ty_expr_total_ok hgd) he /check_typeP hsub hx s.
  have [v hv [ht hd]] := he s; rewrite -ht in hsub.
  have [v' hv' [ht' hd']] := truncate_val_defined_ok hd hsub.
  rewrite /sem_assgn hv /= hv' /=.
  by apply: (check_lval_total_ok hgd) hx ht' _; rewrite /DB hd' orbT.
+ move=> xs tg o es ii; t_xrbindP => hv hes hxs s.
  have [vs hvs hall] := check_exprs_total_ok hgd s hes.
  have [vs' hvs' hall'] := exec_sopn_total_ok hv hall.
  by rewrite /sem_sopn hvs /= hvs' /=; apply: (check_lvals_total_ok hgd) hxs hall'.
+ move=> e c1 c2 h1 h2 ii; t_xrbindP => _ /h1 ? /h2 ?.
  by split.
+ by move=> v d lo hi c0 h ii; t_xrbindP => _ _ _ /h.
+ move=> a c1 e info c2 h1 h2 ii; t_xrbindP => _ /h1 ? /h2 ?.
  by split.
move=> xs f es ii; rewrite /get_fun; case: get_fundef => [fd | //] /=.
t_xrbindP => hes /check_lvalsP hxs; split.
+ move=> s; have [vs -> hall] := check_exprs_total_ok hgd s hes.
  by apply: truncate_vals_defined_ok.
elim: hxs => {xs} [ | x ty xs tys hx _ ih] /=; constructor => // s v v'.
rewrite /dc_truncate_val /= => htr.
by apply: (check_lval_total_ok hgd) hx (truncate_val_has_type htr) (truncate_val_DB _ htr).
Qed.

Lemma check_fun_total_ok fd :
  check_fun (p_globs p) (p_funcs p) fd = ok tt ->
  total_ok_fd fd.2 /\ forall i, List.In i fd.2.(f_body) -> total_ok_i p i.
Proof using hgd.
rewrite /check_fun; t_xrbindP => hpar hres hbody _; split; first split.
+ move: hpar => /check_lvalsP; move: (f_params fd.2) (f_tyin fd.2).
  elim => [ | x xs ih] [ | ty tys] /=; try by move=> h; inversion h.
  move=> h; inversion_clear h as [ | ? ? ? ? hx hxs]; constructor; last by apply: ih.
  move=> s v v'; rewrite /dc_truncate_val /= => htr.
  move: hx; rewrite /check_lval /= => /check_typeP hsub.
  apply: write_var_total_ok; last by apply: truncate_val_DB htr.
  by rewrite (truncate_val_has_type htr).
+ move=> s.
  have -> : get_var_is (sm := total) true (evm s) (f_res fd.2) =
            sem_pexprs (sm := total) true (p_globs p) s (map Plvar (f_res fd.2)).
  - by rewrite /get_var_is /sem_pexprs; elim: (f_res fd.2) => //= x xs ->.
  have [vs -> hall] := check_exprs_total_ok hgd s hres.
  by apply: truncate_vals_defined_ok.
move=> i hi; have hci := allMP hi hbody.
have [] // := check_cmd_total_ok (c := [:: i]).
by rewrite /allM /= hci.
Qed.

End PROG.

End PROOF.

Lemma check_prog_total_ok :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    (p : uprog),
  check_prog p = ok tt -> total_ok p.
Proof.
move=> asm_op syscall_state ep spp sip p; rewrite /check_prog.
t_xrbindP => hgd hfuns fn fd hget.
have : List.In (fn, fd) (rev (p_funcs p)).
+ elim: (p_funcs p) (assoc_mem' hget) => //= a l ih h.
  rewrite rev_cons -cats1 List.in_app_iff /=; case: h => [-> | /ih]; auto.
by move=> /allMP /(_ hfuns) /(check_fun_total_ok hgd) [].
Qed.
