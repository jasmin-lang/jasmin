(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
Require Import psem compiler_util.
Require Export remove_length.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {dc:DirectCall}
  {eparams : EstateParams syscall_state}
  {spparams : SemPexprParams}
  {siparams : SemInstrParams asm_op syscall_state}.
(*   {pT : progT}
  {sCP : semCallParams}. *)

Context (p p' : sprog).
Hypothesis Hp : remove_length_prog p = ok p'.
Context (ev:extra_val_t (progT:=progStack)).

Notation gd  := (p_globs p).
Notation gd' := (p_globs p').

Lemma eq_globs : gd' = gd.
Proof using Hp. by move: (Hp); rewrite /remove_length_prog; t_xrbindP => ? _ <-. Qed.

Definition st_rel' :=
fun {syscall_state : Type} {ep : EstateParams syscall_state} {wsw1 wsw2 : WithSubWord} (D : Type)
  (R : forall env1 env2 : env_t, D -> Vm.t env1 -> Vm.t env2 -> Prop) (env1 env2 : env_t) (d : D) 
  (s : estate env1) (t : estate env2) =>
[/\ escs s = escs t, emem s = emem t & R env1 env2 d (evm s) (evm t)].
Definition vm_eq_novar := (fun env1 env2 (_:unit) (vm1:Vm.t (wsw:=wsw) env1) (vm2:Vm.t (wsw:=wsw) env2) => forall x, no_var_ty x.(vtype) -> vm1.[x] = vm2.[x]).

(* copied from constant_prop_proof *)
(* For the moment, there is no op1 manipulating arrays, so any [env] gives the same result. *)
(* FIXME: move *) 
Lemma sem_sop1_any_env env1 env2 : sem_sop1 env1 =1 sem_sop1 env2.
Proof.
  case => //.
  + by case. 
  by move=> sg [].
Qed.

(* For the moment, there is no op2 manipulating arrays, so any [env] gives the same result. *)
(* FIXME: move *)
Lemma sem_sop2_any_env env1 env2 : sem_sop2 env1 =1 sem_sop2 env2.
Proof.
  case => //; try (by case); try (by move=> ? []).
  by move=> ?? [].
Qed.

(* For the moment, this is true, but is this future proof? *)
(* FIXME: move *)
Lemma sem_opN_any_env env1 env2 : sem_opN env1 =1 sem_opN env2.
Proof.
  by case => // [ ws pe | len ]; rewrite /sem_opN /=; rewrite -> !map_nseq.
Qed.

Section EXPR.

Context env1 env2 (wdb : bool) (gd : glob_decls) (s1 : estate env1) (s2 : estate env2).
Hypothesis heq : st_rel' vm_eq_novar tt s1 s2.

Let P e := no_var_e e -> sem_pexpr wdb gd s1 e = sem_pexpr wdb gd s2 e.
Let Q es := no_var_es es -> sem_pexprs wdb gd s1 es = sem_pexprs wdb gd s2 es.

Lemma no_var_ty_get_var (vm1 : Vm.t env1) (vm2 : Vm.t env2) x :
  vm_eq_novar tt vm1 vm2 ->
  no_var_ty x.(vtype) ->
  get_var wdb vm1 x = get_var wdb vm2 x.
Proof.
  move=> h novar_x.
  by rewrite /get_var h.
Qed.

Lemma no_var_ty_get_gvar (vm1 : Vm.t env1) (vm2 : Vm.t env2) x :
  vm_eq_novar tt vm1 vm2 ->
  no_var_ty x.(gv).(vtype) ->
  get_gvar wdb gd vm1 x = get_gvar wdb gd vm2 x.
Proof.
  move=> h novar_x.
  rewrite /get_gvar.
  case: is_lvar.
  + by apply no_var_ty_get_var.
  rewrite /get_global.
  by rewrite (no_var_tyP novar_x _ env2).
Qed.

Lemma no_var_e_esP : (forall e, P e) /\ (forall es, Q es).
Proof using heq.
  have [h1 h2 h3] := heq.
  apply: pexprs_ind_pair; subst P Q; split => //=.
  + by move=> e he es hes /andP [/he -> /hes ->].
  + move=> ws n hnovar.
    by rewrite (no_var_alP hnovar _ env2).
  + move=> x novar_ty.
    by apply no_var_ty_get_gvar.
  + move=> al aa ws x e he /andP [novar_x /he{}he].
    rewrite /on_arr_var.
    by rewrite (no_var_ty_get_gvar h3 novar_x) he.
  + move=> aa ws len x e he /and3P [novar_len novar_x /he{}he].
    rewrite /on_arr_var.
    by rewrite (no_var_ty_get_gvar h3 novar_x) he (no_var_alP novar_len _ env2).
  + move=> al ws e he /he ->.
    by rewrite h2.
  + move=> o e he /he ->.
    by rewrite (sem_sop1_any_env _ env2).
  + move=> o e1 he1 e2 he2 /andP [/he1 -> /he2 ->].
    by rewrite (sem_sop2_any_env _ env2).
  + move=> o es hes /hes.
    rewrite -/(sem_pexprs _ _ _) => ->.
    by rewrite (sem_opN_any_env _ env2).
  move=> ty e he e1 he1 e2 he2 /and4P [novar_ty /he -> /he1 -> /he2 ->].
  by rewrite (no_var_tyP novar_ty _ env2).
Qed.

Lemma no_var_eP e :
  no_var_e e ->
  sem_pexpr wdb gd s1 e = sem_pexpr wdb gd s2 e.
Proof using heq.
  apply no_var_e_esP.
Qed.

Lemma no_var_esP es :
  no_var_es es ->
  sem_pexprs wdb gd s1 es = sem_pexprs wdb gd s2 es.
Proof using heq.
  apply no_var_e_esP.
Qed.

End EXPR.

Lemma no_var_ty_write_var env1 env2 (s1 s1' : estate env1) (s2 : estate env2) (x : var_i) wdb v :
  st_rel' vm_eq_novar tt s1 s2 ->
  no_var_ty x.(vtype) ->
  write_var wdb x v s1 = ok s1' ->
  exists2 s2', write_var wdb x v s2 = ok s2' & st_rel' vm_eq_novar tt s1' s2'.
Proof.
  move=> heq novar_x.
  rewrite /write_var /set_var.
  rewrite (no_var_tyP novar_x _ env2).
  t_xrbindP=> _ -> -> <- <- /=.
  eexists; first by reflexivity.
  have [h1 h2 h3] := heq.
  split=> //=.
  move=> y novar_y.
  rewrite !Vm.setP.
  case: eq_op; first by rewrite (no_var_tyP novar_x _ env2).
  by apply h3.
Qed.

Lemma no_var_lvalP env1 env2 r wdb gd v (s1 s1' : estate env1) (s2 : estate env2) :
  no_var_lval r ->
  st_rel' vm_eq_novar tt s1 s2 ->
  write_lval wdb gd r v s1 = ok s1' ->
  exists2 s2', write_lval wdb gd r v s2 = ok s2' & st_rel' vm_eq_novar tt s1' s2'.
Proof.
  move=> + heq.
  case: r => /=.
  + move=> _ ty novar_ty.
    rewrite /write_none (no_var_tyP novar_ty _ env2).
    t_xrbindP=> -> -> <- /=.
    by eexists; first by reflexivity.
  + move=> x novar_x.
    by apply no_var_ty_write_var.
  + move=> al ws _ e he.
    rewrite (no_var_eP _ _ heq he).
    have [h1 h2 h3] := heq.
    rewrite h2.
    t_xrbindP=> wp _ -> /= -> w -> /= mem1 -> <- /=.
    by eexists; first by reflexivity.
  + move=> al aa ws x e /andP [novar_x novar_e].
    have [h1 h2 h3] := heq.
    rewrite (no_var_ty_get_var _ h3 novar_x).
    rewrite (no_var_eP _ _ heq novar_e).
    apply: on_arr_varP => n a ? -> /=.
    t_xrbindP=> ?? -> /= -> ? -> /= ? -> /=.
    by apply no_var_ty_write_var.
  move=> aa ws len x e /and3P [novar_len novar_x novar_e].
  have [h1 h2 h3] := heq.
  rewrite (no_var_ty_get_var _ h3 novar_x).
  rewrite (no_var_eP _ _ heq novar_e).
  rewrite (no_var_alP novar_len _ env2).
  apply: on_arr_varP=> n a ? -> /=.
  t_xrbindP=> ?? -> /= -> ? -> ? /= -> /=.
  by apply no_var_ty_write_var.
Qed.

Lemma no_var_lvalsP env1 env2 rs wdb gd vs (s1 s1' : estate env1) (s2 : estate env2) :
  no_var_lvals rs ->
  st_rel' vm_eq_novar tt s1 s2 ->
  write_lvals wdb gd s1 rs vs = ok s1' ->
  exists2 s2', write_lvals wdb gd s2 rs vs = ok s2' & st_rel' vm_eq_novar tt s1' s2'.
Proof.
  elim: rs vs s1 s2 => [|r rs ih] [|v vs] s1 s2 //=.
  + move=> _ heq [<-].
    by eexists; first by reflexivity.
  move=> /andP [novar_r novar_rs] heq.
  t_xrbindP=> s1'' ok_s1'' ok_s1.
  have [s2'' ok_s2'' heq'] := no_var_lvalP novar_r heq ok_s1''.
  have [s2' ok_s2 heq''] := ih _ _ _ novar_rs heq' ok_s1.
  rewrite ok_s2'' /= ok_s2.
  by eexists; first by reflexivity.
Qed.

Section IT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Definition check_es_st_rel' (_:unit) (es1 es2 : pexprs) (_:unit) := [/\ no_var_es es1 & es1 = es2].
Definition check_lvals_st_rel' (_:unit) (xs1 xs2 : lvals) (_:unit) := [/\ no_var_lvals xs1 & xs1 = xs2].

Lemma check_esP_R_st_rel' env1 env2 (d : unit) (es1 es2 : pexprs) (d' : unit) :
  check_es_st_rel' d es1 es2 d' -> forall (s1 : estate env1) (s2 : estate env2), st_rel' vm_eq_novar d s1 s2 -> st_rel' vm_eq_novar d' s1 s2.
Proof. done. Qed.

Definition checker_st_rel' : Checker_e (st_rel' vm_eq_novar) :=
  {| check_es := check_es_st_rel';
     check_lvals := check_lvals_st_rel';
     check_esP_rel := check_esP_R_st_rel' |}.

  #[local] Lemma _checker_st_relP : Checker_eq p p' checker_st_rel'.
  Proof using Hp.
    split.
    + move=> env1 env2 wdb _ d es _ _ /wdb_ok_eq <- [novar_es <-].
      move=> s1 s2 vs heq ok_vs.
      rewrite -(no_var_esP _ _ heq novar_es) eq_globs ok_vs.
      by eexists; first by reflexivity.
    move=> env1 env2 wdb _ d xs _ d' /wdb_ok_eq <- [novar_xs <-] vs.
    move=> s1 s2 s1' heq ok_s1'.
    rewrite eq_globs.
    by apply (no_var_lvalsP novar_xs heq ok_s1').
  Qed.

  #[local] Hint Resolve _checker_st_relP : core.

Definition length_spec :=
{|
  rpreF_ := fun (fn1 fn2 : funname) (vals1 vals2 : seq Z) (fs1 fs2 : fstate) => fn1 = fn2 /\ (* vals2 = [::] /\ *) fs1 = fs2;
  rpostF_ := fun (fn1 _ : funname) (_ _ : seq Z) (_ _ fr1 fr2 : fstate) => fr1 = fr2
|}.

Section REC.

Context (env : env_t).

Let Pi i :=
  no_var_i i ->
  wequiv_rec (env1:=env) (env2:=empty_env) p p' ev ev length_spec (st_rel' vm_eq_novar tt) [::i] [::remove_length_i i] (st_rel' vm_eq_novar tt).

Let Pi_r i := forall ii, Pi (MkI ii i).

Let Pc c :=
  no_var_c c ->
  wequiv_rec (env1:=env) (env2:=empty_env) p p' ev ev length_spec (st_rel' vm_eq_novar tt) c (remove_length_c c) (st_rel' vm_eq_novar tt).

Lemma remove_length_progP_rec c : Pc c.
Proof using Hp.
  apply (cmd_rect (Pr:=Pi_r) (Pi:=Pi) (Pc:=Pc)) => // {c}; subst Pi_r Pi Pc => /=.
  + by move=> _; apply wequiv_nil.
  + move=> i c hi hc /andP [/hi{}hi /hc{}hc]. by apply wequiv_cons with (st_rel' vm_eq_novar tt).
  + move=> x tg ty e ii /and3P [novar_x novar_ty novar_e].
    apply wequiv_assgn_rel_eq with checker_st_rel' tt => //.
    + by rewrite /= /check_es_st_rel' /= novar_e.
    + by apply (no_var_tyP novar_ty).
    by rewrite /= /check_lvals_st_rel' /= novar_x.
  + move=> xs tg o als es ii /and3P [novar_xs novar_als novar_es].
    apply wequiv_opn_rel_eq with checker_st_rel' tt => //.
    elim: als novar_als => [|al als ih] //=.
    move=> /andP [novar_al novar_als].
    by rewrite (no_var_alP novar_al _ empty_env) (ih novar_als).
  + move=> xs o es ii /andP [novar_xs novar_es].
    apply wequiv_syscall_rel_eq_core_R with checker_st_rel' tt tt => //.
    + by move=> _ ?? [/= h1 h2 _].
    + by move=> ???? [/= h1 h2 h3]; split.
    by apply wrequiv_eq.
(*   + move=> a ii. apply wequiv_rec_st_eq. move: eq_globs. done. *)
  + move=> e c1 c2 hc1 hc2 ii /and3P [novar_e novar_c1 novar_c2].
    apply wequiv_if_rel_eq_R with checker_st_rel' tt tt tt => //.
    + by rewrite /= /check_es_st_rel' /= novar_e.
    + by apply hc1.
    by apply hc2.
  + move=> v dir lo hi c hc ii /and4P [novar_v novar_lo novar_hi novar_c].
    apply wequiv_for_rel_eq_R with checker_st_rel' tt tt => //.
    + by rewrite /= /check_es_st_rel' /= novar_lo novar_hi.
    + by rewrite /= /check_lvals_st_rel' /= novar_v.
    by apply hc.
  + move=> a c1 e info c2 hc1 hc2 ii /and3P [novar_c1 novar_e novar_c2].
    apply wequiv_while_rel_eq with checker_st_rel' tt => //.
    + by rewrite /= /check_es_st_rel' /= novar_e.
    + by apply hc1.
    by apply hc2.
  move=> xs fn als es ii /andP [novar_xs novar_es].
  apply wequiv_call with (rpreF (eS := length_spec)) (rpostF (eS := length_spec)) (fun _ vs => vs = [::]) eq.
  + move=> ??? heq. rewrite (no_var_esP _ _ heq novar_es) eq_globs => ->.
    by eexists; first by reflexivity.
  + done.
  + move=> ?????? heq -> <-.
    split. done. (* split=> //. *)
    rewrite /mk_fstate. have [h1 h2 _] := heq. rewrite h1 h2. done.
  + move=> ??. exact: wequiv_fun_rec.
  move=> ?????? /= h1 <-.
  move=> ??? heq.
  rewrite /upd_estate /=. rewrite eq_globs. apply no_var_lvalsP.
  done.
  split=> //=.
  apply heq.
Qed.

End REC.

Lemma toto fn :
  wiequiv_f p p' ev ev (rpreF (eS:= length_spec)) fn fn (rpostF (eS:=length_spec)).
Proof using Hp.
  rewrite /wiequiv_f.
  apply wequiv_fun_ind => {}fn _ vals1 vals2 fs _ [<- <-] fd hget1.
  move: Hp; rewrite /remove_length_prog; t_xrbindP=> fds' hfds' ok_p' /=.
  have [fd' ok_fd' hget2] := get_map_cfprog_gen hfds' hget1.
  rewrite -{1}ok_p' hget2.
  exists fd' => //.
  move=> s hinit.
  move: ok_fd'; rewrite /remove_length_fd.
  t_xrbindP=> novar_fd ?; subst fd' => /=.
  have: create_env [::] vals2 = empty_env.
  + by case: (vals2).
  move=> ->.
  move: hinit; rewrite /initialize_funcall. t_xrbindP=> vs ok_vs s_ ok_s_ ok_s.
  simpl.
  have: mapM2 ErrType dc_truncate_val [seq eval_atype empty_env i | i <- f_tyin fd] (fvals fs) = ok vs.
  + move: novar_fd; rewrite /no_var_fd => /and5P[] hty _ _ _ _.
    elim: fd.(f_tyin) fs.(fvals) (vs) hty ok_vs => [|ty tyin ih] [|v vs'] //=.
    move=> + /andP [hty htys].
    rewrite (no_var_tyP hty _ empty_env).
    t_xrbindP=> _ ? -> ? h <- /=.
    rewrite (ih _ _ htys h). done.
  move=> -> /=.
  (* quel invariant: forall x, x \in fd => vm[x] = vm'[x] ?
                  ou forall x, no_var x.(vtype) => vm[x] = vm'[x] ? *)
  have: exists2 vm_, init_stk_state (f_extra fd) (p_extra p') ev (estate0 empty_env fs) = ok (with_vm s_ vm_) &
    forall x, no_var_ty x.(vtype) -> s_.(evm).[x] = vm_.[x].
  + rewrite -ok_p'.
    move: ok_s_; rewrite /= /init_stk_state /=.
    t_xrbindP=> ? -> /=.
    move=> s__.
    rewrite {1 3}/write_var /= /set_var /=.
    t_xrbindP=> ? -> /= <- /= <-.
    move=> _ /[swap] [->].
    rewrite /write_var /= /set_var /=.
    t_xrbindP=> ? -> <- <- /=. rewrite /with_vm /=.
    eexists; first by reflexivity.
    move=> x hty. rewrite !Vm.setP.
    case: eqP => //=.
    case: eqP => //=.
    move=> _ _.
    rewrite !Vm.initP.
    rewrite (no_var_tyP hty _ empty_env). done.
  move=> [vm_ -> hvm_] /=.
  have: exists2 vm, write_vars (~~ direct_call) (f_params fd) vs (with_vm s_ vm_) = ok (with_vm s vm) &
        forall x, no_var_ty x.(vtype) -> s.(evm).[x] = vm.[x].
  + move: ok_s.
    move: novar_fd; rewrite /no_var_fd.
    move=> /and5P[] _ + _ _ _.
    move: hvm_.
    elim: fd.(f_params) (vs) (s_) (vm_) => [|x xs ih] [|v vs_] s__ vm__ //=.
    + move=> hvm_ _ [<-]. eexists; first by reflexivity. done.
    move=> hvm_ /andP [hty htys].
    t_xrbindP=> zz hw hws.
    move: hw. rewrite /write_var /set_var /=.
    rewrite (no_var_tyP hty _ empty_env). t_xrbindP=> ? -> -> <- /= ?.
    subst zz. rewrite /= !with_vm_idem.
    have [|] := ih _ _ (vm__.[x <- v]) _ htys hws.
    + rewrite /=. move=> y htyy. rewrite !Vm.setP.
      case: eqP. move=> ?; subst. rewrite (no_var_tyP hty _ empty_env). done.
      eauto.
    move=> ?. move=> -> h.
    eexists; first by reflexivity. eauto.
  move=> [vm -> hvm].
  eexists; first by reflexivity.
  exists (st_rel' vm_eq_novar tt), (st_rel' vm_eq_novar tt).
  split.
  + by split.
  + move: novar_fd => /and5P [_ _ _ _ ?].
    exact: remove_length_progP_rec.
  move=> s1 s2 fs1 [h1 h2 h3].
  rewrite /finalize_funcall /=.
  t_xrbindP=> vs_ ok_vs_.
  have: get_var_is (~~ direct_call) (evm s2) (f_res fd) = ok vs_.
  + move: ok_vs_.
    move: novar_fd. rewrite /no_var_fd => /and5P[] _ _ _ + _.
    elim: fd.(f_res) vs_ => [|x xs ih] vs_ //=.
    move=> /andP [hty htys].
    rewrite /get_var. rewrite h3 //.
    apply: rbindP=> ? -> /=.
    t_xrbindP=> ? h <-.
    have -> := ih _ htys h.
    done.
  move=> ->.
  move=> vs' ok_vs' <- /=.
  have: mapM2 ErrType dc_truncate_val [seq eval_atype empty_env i | i <- f_tyout fd] vs_ = ok vs'.
  + move: ok_vs'.
    move: novar_fd. rewrite /no_var_fd => /and5P[] _ _ + _ _.
    elim: fd.(f_tyout) (vs_) vs' => [|ty tys ih] [|v_ vs_'] //=.
    move=> ? /andP [hty htys].
    rewrite (no_var_tyP hty _ empty_env).
    apply: rbindP=> ? -> /=.
    t_xrbindP=> ? h <-.
    have -> := ih _ _ htys h.
    done.
  move=> -> /=.
  eexists; first by reflexivity.
  f_equal. done.
  by rewrite h2.
Qed.

Lemma remove_length_progP fn :
  wiequiv_f p p' ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=length_spec)).
Proof using Hp.
  apply wiequiv_f_weaken with (rpreF (eS:=length_spec)) (rpostF (eS:=length_spec)) => //=.
  tauto.
  apply toto.
Qed.

End IT.

End WITH_PARAMS.
