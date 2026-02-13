From HB Require Import structures.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg word_ssrZ.
Require Import compiler_util psem psem_facts safety safety_shared_proof safety_proof insert_cast.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

Section PROOF.
#[local] Existing Instance progUnit.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

#[local] Existing Instance sCP_unit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.
#[local] Existing Instance withassert.
Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Variable (p :uprog) (ev:extra_val_t).

Notation gd := (p_globs p).

Definition value_wuincl (v1 v2 : value) : Prop :=
  match v1, v2 with
  | Vword sz1 w1, Vword sz2 w2 => word_uincl w1 w2
  | _, _ => v1 = v2
  end.

Lemma value_wuincl_uincl (v1 v2 : value) :
  value_wuincl v1 v2 -> value_uincl v1 v2.
Proof.
  case: v1 => >; case: v2 => > //=.
  1, 2 : by move=> [->].
  + by move=> /Varr_inj [? <-]; subst.
  by move=> [->].
Qed.

Lemma value_wuincl_refl v : value_wuincl v v.
Proof. by case v => //=. Qed.
Hint Resolve value_wuincl_refl : core.

Lemma add_castP s e ty v :
  sem_pexpr true gd s (add_cast e ty) = ok v ->
  exists2 v', sem_pexpr true gd s e = ok v' & value_wuincl v v'.
Proof.
  rewrite /add_cast.
  case: ifP.
  + by move=> *; exists v.
  move=> _.
  case: ty; try by move => *; exists v.
  move=> ws; case heq: type_of_expr; try by move=> *;exists v.
  case: ifP; last by move=> *; exists v.
  move=> hle /=; t_xrbindP => v' hv'.
  rewrite /sem_sop1 /=; t_xrbindP => w /to_wordI' [ws' [w' [hle' ??]]] <-.
  exists v' => //; subst v' w => /=.
  rewrite zero_extend_idem //.
  by apply word_uincl_zero_ext; apply: cmp_le_trans hle hle'.
Qed.

Lemma add_castsP s es tys vs :
  size tys = size es ->
  sem_pexprs true gd s (map2 add_cast es tys) = ok vs ->
  exists2 vs', sem_pexprs true gd s es = ok vs' & List.Forall2 value_wuincl vs vs'.
Proof.
  elim: es tys vs => [ | e es ih] [|ty tys] //=.
  + by move=> ? _ [<-]; exists [::].
  move=> vs [] /ih{}ih; t_xrbindP => > /add_castP [v' -> ?] > /ih [vs' -> ?] <-.
  by exists (v' :: vs') => //; constructor.
Qed.

Lemma value_wuincl_truncate_val ty v1 v2 v :
  value_wuincl v1 v2 -> truncate_val ty v1 = ok v -> truncate_val ty v2 = ok v.
Proof.
  case: v1 => >; case: v2 => > //=.
  1-3,5: by move=> ->.
  move=> hu /truncate_valE [ws [w [-> htr ->]]].
  by rewrite /truncate_val /= (word_uincl_truncate hu htr).
Qed.

Lemma vwuincl_truncate_val vs1 vs2 vs tys :
  List.Forall2 value_wuincl vs1 vs2 ->
  mapM2 ErrType truncate_val tys vs1 = ok vs ->
  mapM2 ErrType truncate_val tys vs2 = ok vs.
Proof.
  move=> hwu; elim: hwu tys vs => //= {vs1 vs2}.
  move=> v1 v2 vs1 vs2 hwu hwus hrec [ | ty tys] vs //=; t_xrbindP.
  move=> > htr1 > /hrec -> <-.
  by rewrite (value_wuincl_truncate_val hwu htr1).
Qed.

Lemma vwuincl_sem_opN op vs vs' v :
  List.Forall2 value_wuincl vs vs' → sem_opN op vs = ok v → sem_opN op vs' = ok v.
Proof.
  move=> hwu /sem_opN_truncate_val [vs1] [hmap].
  rewrite /sem_opN; t_xrbindP => /= v1 hv1 <-.
  have -> //: app_sopn [seq eval_atype i | i <- (type_of_opN op).1] (sem_opN_typed op) vs' = ok v1.
  apply: truncate_val_app_sopn hv1.
  apply: vwuincl_truncate_val hwu hmap.
Qed.

Lemma vwuincl_exec_sopn o vs1 vs2 vs:
  List.Forall2 value_wuincl vs1 vs2 ->
  exec_sopn o vs1 = ok vs → exec_sopn o vs2 = ok vs.
Proof.
  move=> hu; rewrite /exec_sopn /=; t_xrbindP => /= f -> /= vs' h <-.
  have [vs'' [htr happ]] := app_sopn_truncate_val h.
  have -> // : app_sopn [seq eval_atype i | i <- tin (get_instr_desc o)] f vs2 = ok vs'.
  apply: truncate_val_app_sopn happ.
  apply: vwuincl_truncate_val hu htr.
Qed.

Lemma vwuincl_exec_syscall o s s' vs1 vs2 :
  List.Forall2 value_wuincl vs1 vs2 ->
  fexec_syscall o (mk_fstate vs1 s) = ok s' ->
  fexec_syscall o (mk_fstate vs2 s) = ok s'.
Proof.
  case: o => ws len; rewrite /fexec_syscall /=.
  set wlen := (_ * _)%positive.
  rewrite /exec_getrandom_u; case => // v1 v2 {}vs1 {}vs2 hu [] //.
  t_xrbindP => > /to_arrI ? ? hf <- <- [<-]; subst v1.
  by move: hu => /= <- /=; rewrite WArray.castK /= hf /=.
Qed.

Section EXPR.

Let Pe e :=
  forall s v,
  sem_pexpr true gd s (insert_cast_e e) = ok v ->
  sem_pexpr true gd s e = ok v.

Let Qe es :=
  forall s vs,
  sem_pexprs true gd s (map insert_cast_e es) = ok vs ->
  sem_pexprs true gd s es = ok vs.

Lemma insert_cast_eP_aux: (forall e, Pe e) /\ (forall es, Qe es).
Proof.
  apply: pexprs_ind_pair; subst Pe Qe; split => //=.
  + by move=> > he > hes >; t_xrbindP => > /he -> /= > /hes -> <-.
  1,2:
    by move=> > he >; apply on_arr_gvarP => > ? ->;
       rewrite /on_arr_var /=; t_xrbindP => > /he -> /= -> /= ? -> <-.
  + by move=> > he >; t_xrbindP => > /he -> /= -> /= ? -> <-.
  + move=> > he >; t_xrbindP => v /add_castP [v' /he] -> /= hwu.
    by apply/vuincl_sem_sop1/value_wuincl_uincl.
  + move=> > he1 > he2 > /=.
    case: type_of_op2 => -[ty1 ty2 _] /=.
    t_xrbindP => > /add_castP [? /he1] -> ? > /add_castP [? /he2] -> /= ?.
    by apply vuincl_sem_sop2; apply value_wuincl_uincl.
  + move=> > hes >; case: eqP => //= hsz; t_xrbindP => > /(add_castsP hsz) [vs' /hes].
    by rewrite /sem_pexprs => -> /=; apply vwuincl_sem_opN.
  + move=> > he > he1 > he2; t_xrbindP => > /he -> /= ->.
    move=> > /add_castP [v1' /he1 ->] /=.
    move=> hu1 htr1; rewrite (value_wuincl_truncate_val hu1 htr1) /=.
    move=> > /add_castP [v2' /he2 ->] /=.
    by move=> hu2 htr2 <-; rewrite (value_wuincl_truncate_val hu2 htr2) /=.
  by move=> > he1 he2 >; t_xrbindP => > /he1 -> /= -> > /he2 -> /= -> /= <-.
Qed.

Lemma insert_cast_eP : forall e, Pe e.
Proof. apply insert_cast_eP_aux. Qed.

Lemma insert_cast_esP : forall e, Qe e.
Proof. apply insert_cast_eP_aux. Qed.

End EXPR.

Lemma insert_cast_lvP lv v s s' :
  write_lval true gd (insert_cast_lv lv) v s = ok s' ->
  write_lval true gd lv v s = ok s'.
Proof.
  case: lv => //=.
  + by t_xrbindP => > _ > /insert_cast_eP -> /= -> > -> /= > -> /= ->.
  move=> >; apply on_arr_varP => >.
  by rewrite /on_arr_var /=; t_xrbindP => > ? -> /= > /insert_cast_eP -> /= -> > -> > /= -> /= ->.
Qed.

Lemma insert_cast_lvsP lvs vs s s' :
  write_lvals true gd s (insert_cast_lvs lvs) vs = ok s' ->
  write_lvals true gd s lvs vs = ok s'.
Proof.
  elim : lvs vs s => // lv lvs hrec [ | v vs] //= s.
  by t_xrbindP => > /insert_cast_lvP -> /= /hrec ->.
Qed.

Definition fs_wuincl := fs_rel (List.Forall2 value_wuincl).

Definition wuincl_spec : EquivSpec :=
  {| rpreF_ := fun (fn1 fn2 : funname) (fs1 fs2 : fstate) => fn1 = fn2 /\ fs_wuincl fs1 fs2
   ; rpostF_ := fun (fn1 fn2 : funname) (fs1 fs2 fr1 fr2: fstate) => fr1 = fr2 |}.

Let pi := map_prog (insert_cast_fd p) p.

Lemma value_wuincl_dc_truncate_vals ty v1 v2 v :
  List.Forall2 value_wuincl v1 v2 ->
  mapM2 ErrType dc_truncate_val ty v1 = ok v ->
  mapM2 ErrType dc_truncate_val ty v2 = ok v.
Proof.
  move=> h; elim: h ty v => //= > hu hus ih [ | ty tys] //= v.
  t_xrbindP => > htr > /ih -> <-.
  by rewrite /dc_truncate_val (value_wuincl_truncate_val hu htr).
Qed.

Lemma insert_cast_iparams fc: f_iparams (insert_cast_fc fc) = f_iparams fc.
Proof. by case: fc. Qed.

Lemma insert_cast_e_condP s e b:
  sem_cond gd (insert_cast_e e) s = ok b ->
  sem_cond gd e s = ok b.
Proof. by rewrite /sem_cond; t_xrbindP => > /insert_cast_eP -> /=. Qed.

Lemma insert_cast_assertionP s ass v:
  sem_assert gd s (insert_cast_assertion ass) = ok v ->
  sem_assert gd s ass = ok v.
Proof.
  rewrite /insert_cast_assertion /sem_assert /=.
  by t_xrbindP => > /insert_cast_e_condP -> /= -> <-.
Qed.

Lemma insert_cast_assertionsP s ass v:
  mapM (sem_assert gd s) (insert_cast_assertions ass) = ok v ->
  mapM (sem_assert gd s) ass = ok v.
Proof.
  elim: ass v => //= a ass ih v; t_xrbindP.
  by move=> /insert_cast_assertionP -> /= > /ih -> /= <-.
Qed.

Lemma fs_wuincl_sem_pre fn fs1 fs2:
  fs_wuincl fs1 fs2 ->
  sem_pre pi fn fs1 = ok tt -> sem_pre p fn fs2 = ok tt.
Proof.
  rewrite /sem_pre get_map_prog /= => -[<- <- hwu].
  case: get_fundef=> [fd | //] /=.
  case: fd => /= _ [] //= func funty _ _ _ _ _.
  t_xrbindP => v /(value_wuincl_dc_truncate_vals hwu) -> /= >.
  have [-> ->] :
     f_iparams (insert_cast_fc func) = f_iparams func /\
     f_pre (insert_cast_fc func) = insert_cast_assertions (f_pre func) by case: func.
  by move => -> /= > /insert_cast_assertionsP ->.
Qed.

Lemma wuincl_sem_post f vs1 vs2 fr :
  List.Forall2 value_wuincl vs1 vs2 ->
  sem_post pi f vs1 fr = ok tt → sem_post p f vs2 fr = ok tt.
Proof.
  rewrite /sem_post get_map_prog /= => hwu.
  case: get_fundef=> [fd | //] /=.
  case: fd => /= _ [] //= func funty _ _ _ _ _.
  t_xrbindP => v /(value_wuincl_dc_truncate_vals hwu) -> /= >.
  have [-> -> ->] :
     [/\ f_iparams (insert_cast_fc func) = f_iparams func
       , f_ires (insert_cast_fc func) = f_ires func
       & f_post (insert_cast_fc func) = insert_cast_assertions (f_post func)] by case: func.
  by move => -> /= > -> > /= /insert_cast_assertionsP ->.
Qed.

Lemma p_extraP : p_extra pi = p_extra p.
Proof. done. Qed.

Lemma insert_cast_initialize_funcall fd fs1 fs2 s :
  fs_wuincl fs1 fs2 ->
  initialize_funcall pi ev (insert_cast_fd p fd) fs1 = ok s ->
  initialize_funcall p ev fd fs2 = ok s.
Proof.
  rewrite /initialize_funcall /estate0; t_xrbindP.
  move=> [<- <- hwu] > /(value_wuincl_dc_truncate_vals hwu).
  have [-> -> ->] : [/\ f_tyin (insert_cast_fd p fd) = f_tyin fd
              , f_extra  (insert_cast_fd p fd) = f_extra fd
              & f_params (insert_cast_fd p fd) = f_params fd] by case: fd.
  by rewrite p_extraP => -> > /= [<-] ->.
Qed.

(* This comme from remove_globals_proof, share it *)
Notation st_equal := (st_rel (fun _ : unit => eq)).

Lemma st_equalP d s1 s2 : st_equal d s1 s2 <-> s1 = s2.
Proof.
  rewrite st_relP; split.
  + by move=> [-> <-]; rewrite with_vm_same.
  by move=> ->; rewrite with_vm_same.
Qed.

Definition check_es_equal (_:unit) (es1 es2 : pexprs) (_:unit) := es1 = es2.

Definition check_lvals_equal (_:unit) (xs1 xs2 : lvals) (_:unit) := xs1 = xs2.

Lemma check_esP_R_equal d es1 es2 d' :
  check_es_equal d es1 es2 d' →
  ∀ s1 s2, st_equal d s1 s2 → st_equal d' s1 s2.
Proof. done. Qed.

Definition checker_equal : Checker_e st_equal :=
  {| check_es := check_es_equal
   ; check_lvals := check_lvals_equal
   ; check_esP_rel := check_esP_R_equal
  |}.

(* End FIXME *)
Lemma checker_eqP : Checker_eq pi p checker_equal.
Proof.
  constructor.
  + by move=> > /wdb_ok_eq <- <- ??? /st_equalP ->; eauto.
  by move=> > /wdb_ok_eq <- <- ??? s /st_equalP ->; exists s.
Qed.
#[local] Hint Resolve checker_eqP : core.

Lemma insert_cast_callP_aux fn :
  wiequiv_f
    pi p ev ev (rpreF (eS:= wuincl_spec)) fn fn (rpostF (eS:= wuincl_spec)).
Proof.
  apply wequiv_fun_ind_wa => {} fn _ fs1 fs2 [<- hu] fd' hget.
  have [fd hget' ?]: exists2 fd, get_fundef (p_funcs p) fn = Some fd &
                     fd' = insert_cast_fd p fd.
  + move: hget; rewrite get_map_prog /=.
    by case heq: get_fundef => [fd|] //= [?]; subst fd'; eauto.
  exists fd => // hpre; split.
  + by apply: fs_wuincl_sem_pre hu hpre.
  move=> s11 hinit; exists s11; subst fd'.
  + by apply: insert_cast_initialize_funcall hu hinit.
  move=> {hget hget' hpre hinit}.
  exists (st_rel (fun _ => eq) tt), (st_rel (fun _ => eq) tt); split => // {s11}; first last.
  + by rewrite /rpostF /= => > <-; apply wuincl_sem_post; case: hu.
  + apply wrequiv_weaken with (st_eq tt) eq => //.
    + by move => > /st_equalP <-.
    by apply st_eq_finalize; case: fd.
  have -> : f_body (insert_cast_fd p fd) = map (insert_cast_i p) (f_body fd) by case: (fd).
  set Pi := (fun i =>
               wequiv_rec pi p ev ev wuincl_spec (st_rel (λ _ : unit, eq) tt)
                 [:: insert_cast_i p i] [::i] (st_rel (λ _ : unit, eq) tt)).
  set Pc := (fun c =>
               wequiv_rec pi p ev ev wuincl_spec (st_rel (λ _ : unit, eq) tt)
                 (map (insert_cast_i p) c) c (st_rel (λ _ : unit, eq) tt)).
  set Pi_r := (fun ir => forall ii, Pi (MkI ii ir)).
  apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => //;
    subst Pi_r Pi Pc => /= {fd fs1 fs2 hu}.
  + by move=> ?; apply wequiv_nil.
  + by move=> > hi hc /=; apply wequiv_cons with (st_rel (fun _ => eq) tt).
  + move=> >; apply wequiv_assgn with (Rv:= value_wuincl) (Rtr := eq).
    + by move=> s1 s2 v /st_equalP <- /add_castP [v'] /insert_cast_eP; exists v'.
    + move=> _ _ _ v1 v2 v hu htr; exists v => //.
      by apply: value_wuincl_truncate_val hu htr.
    by move=> > <- s1 s2 s1' /st_equalP <- /insert_cast_lvP ->; exists s1'.
  + move=> ?????; case: eqP => hsz;
     last by apply wequiv_opn_rel_eq with checker_equal tt => //.
    apply wequiv_opn with (Rve := List.Forall2 value_wuincl) (Rvo := eq).
    + by move=> ?? vs /st_equalP <- /(add_castsP hsz) [vs'] /insert_cast_esP; exists vs'.
    + by move=> _ _ _ vs1 vs2 vs hu /(vwuincl_exec_sopn hu); eauto.
    by move=> > <- s1 s2 s1' /st_equalP <- /insert_cast_lvsP ->; exists s1'.
  + move=> ????; case: eqP => hsz;
     last by apply wequiv_syscall_rel_eq with checker_equal tt => //.
    apply wequiv_syscall with (Rv := List.Forall2 value_wuincl) (Ro := eq).
    + by move=> ?? vs /st_equalP <- /(add_castsP hsz) [vs'] /insert_cast_esP; exists vs'.
    + by move=> s1 _ /st_equalP <- vs1 vs2 s1' hu /(vwuincl_exec_syscall hu) ->; eauto.
    by move=> > <- ?? s' /st_equalP <- /insert_cast_lvsP; exists s'.
  + by move=> ??; apply wequiv_assert => _; split => // > /st_equalP <- /insert_cast_e_condP.
  + move=> > hc1 hc2 ii; apply wequiv_if.
    + by move=> ??? /st_equalP <- /insert_cast_e_condP; eauto.
    by case.
  + move=> > hc ?; apply wequiv_for with (Pi := st_equal tt) => //.
    + move => ??? /st_equalP <-; rewrite /sem_bound.
      by t_xrbindP => > /insert_cast_eP -> /= -> > /insert_cast_eP -> /= -> <- /=; eauto.
    + by move => ??? s' /st_equalP <- ->; exists s'.
  + move=> > hc hc' ?; apply wequiv_while => //.
    by move=> ??? /st_equalP <- /insert_cast_e_condP; eauto.
  move=> xs f es ii.
  have h :
   wequiv_rec pi p ev ev wuincl_spec
     (st_equal tt) [:: MkI ii (Ccall xs f es)] [:: MkI ii (Ccall xs f es)] (st_equal tt).
  + apply wequiv_call_rel_eq_wa with checker_equal tt => //.
    + move=> s1 s2 vs /st_equalP <-; apply fs_wuincl_sem_pre; split => //.
      by apply List_Forall2_refl.
    + set hE := relEvent_recCall (rE0 := rE) wuincl_spec.
      apply wkequiv_io_weaken with (rpreF (eS:=wuincl_spec) f f) (rpostF (eS:=wuincl_spec) f f) => //.
      + by move=> > <-; split => //; split => //; apply List_Forall2_refl.
      by move=> >; apply wequiv_fun_rec.
    + by move=> vs fr; apply wuincl_sem_post; apply List_Forall2_refl.
  case: get_fundef => [fd | //].
  case: eqP => hsz //.
  apply wequiv_call_wa with (rpreF (eS:=wuincl_spec)) (rpostF (eS:=wuincl_spec)) (List.Forall2 value_wuincl).
  + by move=> ?? vs /st_equalP <- /(add_castsP hsz) [vs'] /insert_cast_esP; exists vs'.
  + by move=> > /st_equalP <- hu; apply fs_wuincl_sem_pre.
  + by move=> > /st_equalP <-.
  + by move=> > [_ [_ _ hu]] <-; apply wuincl_sem_post.
  + by move=> >; apply wequiv_fun_rec.
  move=> > _; rewrite /rpostF /= => <-.
  by move=> ?? s' /st_equalP <- /insert_cast_lvsP; exists s'.
Qed.

Lemma insert_cast_callP fn :
  wiequiv_f
    pi p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:= eq_spec)).
Proof.
  move: (insert_cast_callP_aux (fn := fn)).
  apply wkequiv_io_weaken => //.
  move=> ?? [_ <-]; split => //; split => //.
  by apply List_Forall2_refl.
Qed.

End PROOF.
