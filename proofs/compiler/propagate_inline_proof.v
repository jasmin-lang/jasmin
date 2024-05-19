(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem psem_facts constant_prop constant_prop_proof.
Require Export propagate_inline.

Import Utf8 ZArith Morphisms Classes.RelationClasses.

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
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {sCP : semCallParams}
.

Definition dfl_cel := 
  {| pi_def := Pconst 0; pi_fv := Sv.empty; pi_m := false; pi_fv_ok := erefl _; pi_m_ok := erefl _|}.

Lemma removeP (pi:pimap) x y :
  Mvar.get (remove pi x) y = 
    if (x == y) || Sv.mem x (odflt dfl_cel (Mvar.get pi y)).(pi_fv) then None 
    else Mvar.get pi y.
Proof. 
  rewrite /remove /= Mvar.filter_mapP.
  by case: eqP => //=; case heqy: Mvar.get. 
Qed.

Lemma remove_mP (pi:pimap) y :
  Mvar.get (remove_m pi) y = 
    if (odflt dfl_cel (Mvar.get pi y)).(pi_m) then None 
    else Mvar.get pi y.
Proof. 
  rewrite /remove_m /=; rewrite Mvar.filter_mapP.
  by case heqy: Mvar.get. 
Qed.

Lemma setP (pi:pimap) x e y :
  Mvar.get (set pi x e) y = 
    if (x == y) && ~~ Sv.mem x (read_e e) then 
      Some {| pi_def := e; pi_fv := read_e e; pi_m := use_mem e; pi_fv_ok := erefl _; pi_m_ok := erefl _|} 
    else Mvar.get pi y.
Proof. by rewrite /set /=; case: ifP => /= _; rewrite ?(andbF, andbT) // Mvar.setP. Qed.

Lemma mergeP (pi1 pi2:pimap) x : 
  Mvar.get (merge pi1 pi2) x = 
    match Mvar.get pi1 x, Mvar.get pi2 x with
    | Some c1, Some c2 => 
      if eq_expr c1.(pi_def) c2.(pi_def) then Mvar.get pi1 x
      else None
    | _, _ => None
    end.
Proof. by rewrite /merge /get Mvar.map2P. Qed.

Lemma incl_merge_l pi1 pi2 : incl (merge pi1 pi2) pi1.
Proof.
  rewrite /incl Mvar.inclP /= => x; rewrite mergeP.
  case: Mvar.get => // c1; case: Mvar.get => // c2.
  by case: ifP => //= _; apply eq_expr_refl.
Qed.

Lemma incl_merge_r pi1 pi2 : incl (merge pi1 pi2) pi2.
Proof.
  rewrite /incl Mvar.inclP /= => x; rewrite mergeP.
  case: Mvar.get => // c1; case: Mvar.get => // c2.
  by case: ifP => //= _; apply eq_expr_refl.
Qed.

Lemma inclP pi1 pi2 x c1 : 
  incl pi1 pi2 -> Mvar.get pi1 x = Some c1 -> 
  exists c2, Mvar.get pi2 x = Some c2 /\ eq_expr c1.(pi_def) c2.(pi_def).
Proof.
  move=> /Mvar.inclP -/(_ x) h hx; move: h; rewrite hx.
  by case: Mvar.get => // c2 ?;exists c2.
Qed.

Lemma incl_refl pi : incl pi pi.
Proof. rewrite /incl Mvar.inclP => x; case: Mvar.get => // ?; apply eq_expr_refl. Qed.

Lemma incl_trans pi2 pi1 pi3: 
  incl pi1 pi2 -> incl pi2 pi3 -> incl pi1 pi3.
Proof.
  rewrite /incl !Mvar.inclP => h1 h2 x.
  case: (Mvar.get pi1 x) (h1 x) (h2 x) => // c1.
  case: (Mvar.get pi2 x) => // c2.
  case: (Mvar.get pi3 x) => // c3.
  apply: eq_expr_trans.
Qed.

Section Global.
Context (gd : glob_decls).

Section SCFC.

Context (s : estate).

Lemma snotE wdb e b:
  sem_pexpr wdb gd s e = ok (Vbool b) ->
  sem_pexpr wdb gd s (snot e) = ok (Vbool (~~ b)).
Proof.
  move=> he; have /snotP : sem_pexpr wdb gd s (Papp1 Onot e) = ok (Vbool (~~b)).
  + by rewrite /= he.
  by move=> [v] [->] /value_uinclE ->.
Qed.

Lemma sbeqE wdb e0 e1 b0 b1 :
  sem_pexpr wdb gd s e0 = ok (Vbool b0) ->
  sem_pexpr wdb gd s e1 = ok (Vbool b1) ->
  sem_pexpr wdb gd s (sbeq e0 e1) = ok (Vbool (b0 == b1)).
Proof.
  move=> h0 h1.
  have : sem_pexpr wdb gd s (Papp2 Obeq e0 e1) = ok (Vbool (b0 == b1)).
  - by rewrite /= h0 h1.
  clear h0 h1.
  move=> /sbeqP [v [-> hincl]].
  by move: hincl => /value_uinclE ?; subst v.
Qed.

Lemma sorE wdb e1 e2 b1 b2 :
  sem_pexpr wdb gd s e1 = ok (Vbool b1) ->
  sem_pexpr wdb gd s e2 = ok (Vbool b2) ->
  sem_pexpr wdb gd s (sor e1 e2) = ok (Vbool (b1 || b2)).
Proof.
  move=> h1 h2; have : sem_pexpr wdb gd s (Papp2 Oor e1 e2) = ok (Vbool (b1 || b2)).
  + by rewrite /= h1 h2.
  by move=> /sorP [v] [-> /value_uinclE ->]. 
Qed.

Lemma sandE wdb e1 e2 b1 b2 :
  sem_pexpr wdb gd s e1 = ok (Vbool b1) ->
  sem_pexpr wdb gd s e2 = ok (Vbool b2) ->
  sem_pexpr wdb gd s (sand e1 e2) = ok (Vbool (b1 && b2)).
Proof.
  move=> h1 h2; have : sem_pexpr wdb gd s (Papp2 Oand e1 e2) = ok (Vbool (b1 && b2)).
  + by rewrite /= h1 h2.
  by move=> /sandP [v] [-> /value_uinclE ->]. 
Qed.

(* Interpreting the flag combination as an expression and evaluating it
   coincides with interpreting as a boolean. *)
Lemma sem_pexpr_fc_sem wsb b0 b1 b2 b3 e0 e1 e2 e3 fc :
  sem_pexpr wsb gd s e0 = ok (Vbool b0) ->
  sem_pexpr wsb gd s e1 = ok (Vbool b1) ->
  sem_pexpr wsb gd s e2 = ok (Vbool b2) ->
  sem_pexpr wsb gd s e3 = ok (Vbool b3) ->
  let: e := fc_sem snot sand sor sbeq e0 e1 e2 e3 fc in
  let: b := fc_sem negb andb orb (fun x y => x == y) b0 b1 b2 b3 fc in
  sem_pexpr wsb gd s e = ok (Vbool b).
Proof.
  move=> ????.
  elim: fc => * /=;
    t_simpl_rewrites;
    by [| exact: snotE | exact: sandE | exact: sorE | exact: sbeqE ].
Qed.

Lemma sem_pexpr_cf_xsem wdb e0 e1 e2 e3 cf v :
  let: e := PappN (Ocombine_flags cf) [:: e0; e1; e2; e3 ] in
  let: e' := cf_xsem snot sand sor sbeq e0 e1 e2 e3 cf in
  sem_pexpr wdb gd s e = ok v ->
  sem_pexpr wdb gd s e' = ok v.
Proof.
  rewrite /=.
  t_xrbindP=> vs0 v0 hv0 vs1 v1 hv1 vs2 v2 hv2 vs3 v3 hv3 ? ? ? ?;
    subst.

  rewrite /sem_opN /=.
  t_xrbindP=> b ? /to_boolI ?? /to_boolI ?? /to_boolI ?? /to_boolI ? hb ?;
    subst.

  rewrite /sem_combine_flags /cf_xsem.
  case: cf_tbl => -[] ?;
    by auto using snotE, sandE, sorE, sbeqE, sem_pexpr_fc_sem.
Qed.

Lemma scfcP wdb c es vs v :
  sem_pexprs wdb gd s es = ok vs
  -> sem_opN (Ocombine_flags c) vs = ok v
  -> sem_pexpr wdb gd s (scfc c es) = ok v.
Proof.
  move=> h.
  repeat (
    case: es h => /= [[<-] | ? es];
      first (by t_simpl_rewrites);
      t_xrbindP=> ?? {vs} vs h <-
  ).

  case: es h => /= [[<-] | ??]; first last.
  - t_xrbindP=> ???? <-. rewrite /sem_opN /=. by t_xrbindP.

  move=> h.
  apply: sem_pexpr_cf_xsem => /=.
  by t_simpl_rewrites.
Qed.

End SCFC.

Record valid_pi (s : estate) (pi : pimap) :=
  { vpi_ok :
     forall x c,
       Mvar.get pi x = Some c ->
       exists2 v', sem_pexpr true gd s c.(pi_def) = ok v' & value_uincl (evm s).[x] v' }.

Lemma valid_pi_empty s : valid_pi s piempty.
Proof. by constructor => ??; rewrite Mvar.get0. Qed.

Section Expr.

Context (s : estate) (pi : pimap) (hvalid : valid_pi s pi) (wdb : bool).

Let P e : Prop :=
  forall v, sem_pexpr wdb gd s e = ok v ->
  exists2 v', sem_pexpr wdb gd s (pi_e pi e) = ok v' & value_uincl v v'.

Let Q es : Prop :=
  forall vs, sem_pexprs wdb gd s es = ok vs ->
  exists2 vs', sem_pexprs wdb gd s (pi_es pi es) = ok vs' & List.Forall2 value_uincl vs vs'.

Lemma pi_eP_and : (forall e, P e) /\ (forall es, Q es).
Proof. 
  apply: pexprs_ind_pair; subst P Q; split => /=.
  + by move=> ? [<-]; exists [::]. 
  + move=> e hrec es hrecs vs; t_xrbindP => ? /hrec [v' -> hu] ? /hrecs [vs' -> hus] <- /=.
    by exists (v'::vs'); auto.
  1-3: by move=> ?? [<-]; eauto.
  + move=> x v; case: ifP => h /=; last by eauto.
    move=> hg; case heq : Mvar.get => [[e' fv m ??] | ]; last by eauto.
    move: hg; rewrite /get_gvar h => /get_varP [-> ??].
    have /= [v' /(sem_pexpr_wdb wdb)??]:= vpi_ok hvalid heq; eexists; eauto.
  + move=> ??? x e hrec v; apply:on_arr_gvarP; rewrite /on_arr_var => n t ? -> /=.
    t_xrbindP => i vi /= /hrec [v' -> /= /of_value_uincl_te h] /(h sint) /= -> w hget <-.
    by rewrite /= hget /=; (eexists; first reflexivity) => /=.
  + move=> ??? x e hrec v; apply:on_arr_gvarP; rewrite /on_arr_var => n t ? -> /=.
    t_xrbindP => i vi /= /hrec [v' -> /= /of_value_uincl_te h] /(h sint) /= -> st hget <-.
    by rewrite /= hget /=; (eexists; first reflexivity) => /=.
  + move=> ???? hrec ?; t_xrbindP => ?? -> /= -> ??
      /hrec [ve -> /of_value_uincl_te h] /(h (sword _)) /= -> ? /= -> /= ->.
    by (eexists; first reflexivity).
  + move=> op e hrec v; t_xrbindP => ve /hrec [ve' -> hu] /= hs.
    by rewrite (vuincl_sem_sop1 hu hs); eauto.
  + move=> op e1 hrec1 e2 hrec2 v; t_xrbindP => ve1 /hrec1 [ve1' -> hu1] ve2 /hrec2 [ve2' -> hu2] /= hs.
    by rewrite (vuincl_sem_sop2 hu1 hu2 hs); eauto.
  + move=> o es hrec ?; t_xrbindP => ? /hrec [vs' hs' hu].
    case: o => [wz pe | c] /=.
    + move=> ho; rewrite -/(sem_pexprs wdb gd _ (pi_es pi es)) hs' /=.
      by apply: vuincl_sem_opN ho hu.
    move=> ho; have [v' ho' hu']:= vuincl_sem_opN ho hu.
    by rewrite -/(pi_es pi es) (scfcP hs' ho'); eauto.
  move=> ?? hrec ? hrec1 ? hrec2 v; t_xrbindP.
  move=> ?? /hrec [? -> /of_value_uincl_te h] /(h sbool) /= ->.
  move=> ?? /hrec1 [? -> hu1] /= /(value_uincl_truncate hu1) [? -> hu1'].
  move=> ?? /hrec2 [? -> hu2] /= /(value_uincl_truncate hu2) [? -> hu2'] <- /=.
  by eexists; first reflexivity; case: ifP.
Qed.

Lemma pi_eP e v :
  sem_pexpr wdb gd s e = ok v ->
  exists2 v', sem_pexpr wdb gd s (pi_e pi e) = ok v' & value_uincl v v'.
Proof. case: pi_eP_and => h _; apply h. Qed.

Lemma pi_esP es vs :
  sem_pexprs wdb gd s es = ok vs ->
  exists2 vs', sem_pexprs wdb gd s (pi_es pi es) = ok vs' &
    List.Forall2 value_uincl vs vs'.
Proof. case: pi_eP_and => _ h; apply h. Qed.

Context (vm:Vm.t) (hu: evm s <=1 vm).

Lemma pi_eP_uincl e v :
  sem_pexpr wdb gd s e = ok v ->
  exists2 v', sem_pexpr wdb gd (with_vm s vm) (pi_e pi e) = ok v' & value_uincl v v'.
Proof.
  move=> /pi_eP [v'] /(sem_pexpr_uincl hu) [v'' ? h2] h1. 
  exists v'' => //; apply: value_uincl_trans h1 h2.
Qed.

Lemma pi_esP_uincl es vs :
  sem_pexprs wdb gd s es = ok vs ->
  exists2 vs', sem_pexprs wdb gd (with_vm s vm) (pi_es pi es) = ok vs' &
    List.Forall2 value_uincl vs vs'.
Proof. 
  move=> /pi_esP [vs'] /(sem_pexprs_uincl hu) [vs'' ? h2] h1.
  exists vs'' => //; apply: Forall2_trans h1 h2; apply value_uincl_trans.
Qed.

End Expr.


Lemma write_var_valid_pi wdb s s' pi x v :
  valid_pi s pi ->
  write_var wdb x v s = ok s' ->
  valid_pi s' (remove pi x) /\
  write_var wdb x v s = ok s'.
Proof.
  move=> hvalid hw; split => //.
  constructor => y c; rewrite removeP //; case: eqP => //=.
  case: Sv_memP => // hnin /eqP hne h.
  move: hw => /write_varP [-> ??] /=; rewrite Vm.setP_neq //.
  have [vy' hs huy] := vpi_ok hvalid h.
  exists vy' => //=; rewrite -hs.
  apply eq_on_sem_pexpr => //=.
  move=> z hz;  rewrite Vm.setP_neq //.
  by apply/eqP => ?; subst z; apply hnin; rewrite h /= pi_fv_ok.
Qed.

Lemma valid_pi_remove_m s pi m : 
  valid_pi s pi ->
  valid_pi (with_mem s m) (remove_m pi).
Proof.
  move=> hvalid; constructor; move=> y c /=; rewrite remove_mP //.
  case: ifP => //.
  move=> hm hy; rewrite hy /= in hm.
  rewrite pi_m_ok in hm.
  have /use_memP <- : evm s = evm (with_mem s m) by done.
  + by apply (vpi_ok hvalid hy).
  by rewrite hm.
Qed.

Lemma pi_lvP wdb pi s s' x v :
  valid_pi s pi ->
  write_lval wdb gd x v s = ok s' ->
  valid_pi s' (pi_lv pi x).1 /\
  write_lval wdb gd (pi_lv pi x).2 v s = ok s'.
Proof.
  move=> hvalid; case: x => /=.
  + by move=> vi ty /write_noneP; rewrite /write_none => -[-> -> ->].
  + by move=> x; apply write_var_valid_pi.
  + move=> al ws x e; t_xrbindP => px vx gx hpx pe ve he hpe w hw m hwr <-.
    split; first by apply valid_pi_remove_m.
    have /(_ _ _ _ he) [ve' -> /of_value_uincl_te hu] := pi_eP hvalid.
    have /= -> := hu (sword _) _ hpe.
    by rewrite gx /= hpx hw /= hwr.
  + move=> al aa ws x e; apply on_arr_varP => n t hty hx.
    t_xrbindP => i ve he hi w hw t' ht' hwr.
    rewrite /on_arr_var hx /=.
    have /(_ _ _ _ he) [ve' -> /of_value_uincl_te hu] /= := pi_eP hvalid.
    have /= -> := (hu sint _ hi).
    rewrite hw /= ht' /=.
    by apply write_var_valid_pi.
  move=> aa ws len x e; apply on_arr_varP => n t hty hx.
  t_xrbindP => i ve he hi w hw t' ht' hwr.
  rewrite /on_arr_var hx /=.
  have /(_ _ _ _ he) [ve' -> /of_value_uincl_te hu] /= := pi_eP hvalid.
  have /= -> := (hu sint _ hi).
  rewrite hw /= ht' /=.
  by apply write_var_valid_pi.
Qed.

Lemma pi_lvsP wdb pi s s' xs vs :
  valid_pi s pi ->
  write_lvals wdb gd s xs vs = ok s' ->
  valid_pi s' (pi_lvs pi xs).1 /\
  write_lvals wdb gd s (pi_lvs pi xs).2 vs = ok s'.
Proof.
  elim: xs vs pi s => [ | x xs hrec] [ | v vs] //= pi s hvalid.
  + by move=> [<-].
  t_xrbindP => s1 /(pi_lvP hvalid).
  case: pi_lv => pi1 x' [ hvalid1 hw1].
  move=> /(hrec _ _ _ hvalid1); case: pi_lvs => pi' xs' [hvalid' hw'].
  by rewrite /= hw1.
Qed.

Lemma pi_lvP_uincl wdb pi s vm s' x v v':
  evm s <=1 vm -> value_uincl v v' ->
  valid_pi s pi ->
  write_lval wdb gd x v s = ok s' ->
  exists vm', 
  [/\ evm s' <=1 vm',
      valid_pi s' (pi_lv pi x).1
    & write_lval wdb gd (pi_lv pi x).2 v' (with_vm s vm) = ok (with_vm s' vm') ].
Proof.
  move=> hu huv hvalid hw.
  have [hvalid' hw'] := pi_lvP hvalid hw.
  by have [vm' hw'' hu']:= write_uincl hu huv hw'; exists vm'.
Qed.

Lemma pi_lvsP_uincl wdb pi s vm s' xs vs vs':
  evm s <=1 vm -> List.Forall2 value_uincl vs vs' ->
  valid_pi s pi ->
  write_lvals wdb gd s xs vs = ok s' ->
  exists vm',
  [/\ evm s' <=1 vm',
      valid_pi s' (pi_lvs pi xs).1
    & write_lvals wdb gd (with_vm s vm) (pi_lvs pi xs).2 vs' = ok (with_vm s' vm') ].
Proof.
  move=> hu huv hvalid hw.
  have [hvalid' hw'] := pi_lvsP hvalid hw.
  by have [vm' hw'' hu']:= writes_uincl hu huv hw'; exists vm'.
Qed.

End Global.

Section PROOF.

  Context (p1 p2 : prog) (ev : extra_val_t).

  Notation gd := (p_globs p1).
  Notation ep1 := (p_extra p1).
  Notation ep2 := (p_extra p2). 

  Hypothesis hcomp : pi_prog p1 = ok p2.

  Lemma eq_globs : p_globs p1 = p_globs p2.
  Proof. by move: hcomp; rewrite /pi_prog; t_xrbindP => ?? <-. Qed.

  Lemma eq_p_extra : ep1 = ep2.
  Proof. by move: hcomp; rewrite /pi_prog; t_xrbindP => ? _ <-. Qed.

  Lemma all_checked fn f1 :
    get_fundef (p_funcs p1) fn = Some f1 ->
    exists2 f2, pi_fun f1 = ok f2 & get_fundef (p_funcs p2) fn = Some f2.
  Proof. 
    move: hcomp; rewrite /pi_prog; t_xrbindP => pf2 hf <- /=.
    by apply: compiler_util.get_map_cfprog_gen hf.
  Qed.

  Let Pi s1 (i1:instr) s2:=
    forall pi pi2 vm1, 
      pi_i pi i1 = ok pi2 ->
      evm s1 <=1 vm1 -> valid_pi gd s1 pi ->
      exists vm2, 
      [/\ evm s2 <=1 vm2, valid_pi gd s2 pi2.1
        & sem_I p2 ev (with_vm s1 vm1) pi2.2 (with_vm s2 vm2)].

  Let Pi_r s1 (i1:instr_r) s2 :=
    forall ii, Pi s1 (MkI ii i1) s2.

  Let Pc s1 (c1:cmd) s2:=
    forall pi pc2 vm1, 
      pi_c pi_i pi c1 = ok pc2 ->
      evm s1 <=1 vm1 -> valid_pi gd s1 pi ->
      exists vm2,
      [/\ evm s2 <=1 vm2, valid_pi gd s2 pc2.1
        & sem p2 ev (with_vm s1 vm1) pc2.2 (with_vm s2 vm2) ].

  Let Pfor (i1:var_i) vs s1 c1 s2 :=
    forall pi pc2 vm1, 
      pi_c pi_i (remove pi i1) c1 = ok pc2 -> incl pi pc2.1 ->
      evm s1 <=1 vm1 -> valid_pi gd s1 pi ->
      exists vm2,
      [/\ evm s2 <=1 vm2, valid_pi gd s2 pi
        & sem_for p2 ev i1 vs (with_vm s1 vm1) pc2.2 (with_vm s2 vm2) ].

  Let Pfun scs m fn vargs scs' m' vres :=
    forall vargs', List.Forall2 value_uincl vargs vargs' ->
    exists2 vres', List.Forall2 value_uincl vres vres' & sem_call p2 ev scs m fn vargs' scs' m' vres'.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof. move=> s pi pic2 vm1 [<-] ??; exists vm1; split => //; constructor. Qed.

  Local Lemma Hcons : sem_Ind_cons p1 ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ hi _ hc pi pc vm1 /=; t_xrbindP.
    move=> pi2 hpi2 pc2 hpc2 <- hu hv.
    have [vm2 [hu2 hv2 hsi]]:= hi _ _ _ hpi2 hu hv.
    have [vm3 [hu3 hv3 hsc]] := hc _ _ _ hpc2 hu2 hv2.
    exists vm3; split => //; econstructor; eauto.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p1 ev Pi_r Pi.
  Proof.
    move=> ii i s1 s2 _ hi pi pi2 vm1 hpi2 hu hv.
    have [vm' [???]] := hi _ _ _ _ hpi2 hu hv; exists vm'; split => //; constructor.
  Qed.

  Lemma set_lvE pi x tag e : 
       (exists x0, [/\ x = Lvar x0, tag = AT_inline & set_lv pi x tag e = set pi x0 e]) 
    \/ set_lv pi x tag e = pi.
  Proof. 
    case: x.
    1, 3-5: by move=> *; right.
    move=> x0 /=; case: eqP; last by move=> *; right.
    by move=> ->; left; exists x0.
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn p1 Pi_r.
  Proof.
    move => s1 s2 x tag ty e v v' he htr hwr ii pi pi2 vm1 /=.
    case heq: pi_lv => [pi' x'] [] <- hu hv.
    have [vpe hvpe hupe] := pi_eP hv he.
    have [ve hve huve] := sem_pexpr_uincl hu hvpe.
    have hue := value_uincl_trans hupe huve.
    have [ve' htr' hue']:= value_uincl_truncate hue htr.
    have [vm' ] := pi_lvP_uincl hu hue' hv hwr.
    rewrite heq /= => -[hu' hv' hwr'].
    exists vm' => /=.
    assert (h : valid_pi gd s2 (set_lv pi' x' tag (pi_e pi e))); last first.
    + by split => //; constructor; econstructor; eauto; rewrite -eq_globs. 
    case (set_lvE pi' x' tag (pi_e pi e)); last by move=> ->.
    move=> [x0 [?? ->]]; subst x' tag.
    have [??] : x = x0 /\ pi' = remove pi x0.    
    + by case: (x) heq => // ? [] <- ->.
    subst x pi'. 
    constructor => y c; rewrite setP; case: andP => [| _]; last by apply (vpi_ok hv').
    move=>  [/eqP <- /Sv_memP hnin] [<-] /=.
    move/write_varP: hwr => [? hdb htrv]; subst s2 => /=.
    rewrite Vm.setP_eq //.
    exists vpe.
    + rewrite -hvpe; apply eq_on_sem_pexpr => //=.
      move=> z hz; rewrite Vm.setP_neq //.
      by apply/eqP => ?; subst z;apply hnin.
    apply: value_uincl_trans hupe.
    apply: value_uincl_trans (truncate_value_uincl htr).
    apply: vm_truncate_value_uincl htrv.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p1 Pi_r.
  Proof.
    move => s1 s2 t o xs es.
    rewrite /sem_sopn; t_xrbindP => vs ves hes ho hws ii pi pi2 vm1 /=.
    case heq: pi_lvs => [pi0 xs0] [<-] hu hv /=.
    have [ves' hes' hues]:= pi_esP_uincl hv hu hes.
    have [ vs' ho' vs_vs' ] := vuincl_exec_opn hues ho.
    have [vm' []]:= pi_lvsP_uincl hu vs_vs' hv hws.
    rewrite heq /= => hu' hv' hws'; exists vm'; split => //.
    by do 2! constructor; rewrite /sem_sopn /= -eq_globs hes' /= ho' /= hws'.
  Qed.

  Lemma valid_pi_with_scs s pi scs : valid_pi gd s pi -> valid_pi gd (with_scs s scs) pi.
  Proof.
    move=> [] h; constructor => m c h1.
    by have := h _ _ h1; rewrite -sem_pexpr_with_scs.
  Qed.

  Local Lemma Hsyscall : sem_Ind_syscall p1 Pi_r.
  Proof.
    move => s1 scs m s2 o xs es ves vs hes ho hw ii pi pi2 vm1 /=.
    case heq: pi_lvs => [pi0 xs0] [<-] hu hv /=.
    have [ves' hes' hues]:= pi_esP_uincl hv hu hes.
    have [vs' ho' hus] := exec_syscallP ho hues.
    have hv' := valid_pi_with_scs scs (valid_pi_remove_m m hv).
    have /(_ _ hu) [vm2 []]:= pi_lvsP_uincl _ hus hv' hw.
    rewrite heq => ???; exists vm2; split => //.
    constructor; econstructor; rewrite -?eq_globs; eauto.
  Qed.

  Lemma valid_pi_incl s pi1 pi2 : incl pi1 pi2 -> valid_pi gd s pi2 -> valid_pi gd s pi1.
  Proof.
    move=> hincl hv; constructor => x c hg.
    have [c' [hg' heq]] := inclP hincl hg.
    have [v' hs hu]:= vpi_ok hv hg'.
    by exists v' => //; rewrite -hs; apply eq_exprP.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p1 ev Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 he _ hc ii pi pi2 vm /=.
    t_xrbindP=> pc1 hpc1 pc2 hpc2 ? hu hv; subst pi2.
    have [vm' [hu' hv' hs]]:= hc _ _ _ hpc1 hu hv.
    exists vm'; split => //=.
    + by apply: valid_pi_incl hv'; apply incl_merge_l.
    constructor; apply Eif_true => //; rewrite -eq_globs.
    by have [b' -> /value_uinclE ->]:= pi_eP_uincl hv hu he.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p1 ev Pc Pi_r.
  Proof.
    move => s1 s2 e c1 c2 he _ hc ii pi pi2 vm /=.
    t_xrbindP=> pc1 hpc1 pc2 hpc2 ? hu hv; subst pi2.
    have [vm' [hu' hv' hs]]:= hc _ _ _ hpc2 hu hv.
    exists vm'; split => //=.
    + by apply: valid_pi_incl hv'; apply incl_merge_r.
    constructor; apply Eif_false => //; rewrite -eq_globs.
    by have [b' -> /value_uinclE ->]:= pi_eP_uincl hv hu he.
  Qed.

  Local Lemma loop_whileP ii c1 e c2 c1' e' c2' n pi1 pi2:
    loop_while pi_i ii c1 e c2 n pi1 = ok (pi2, c1', e', c2') ->
      exists pi pi3, 
      [/\ pi_c pi_i pi c1 = ok (pi2, c1'), 
          pi_c pi_i pi2 c2 = ok (pi3, c2'),
          e' = pi_e pi2 e
        & incl pi pi3 /\ incl pi pi1 ].
  Proof.
    elim: n pi1 => //= n hrec pi1. 
    t_xrbindP => pic1 hc1 pic2 hc2; case: ifP => hincl.
    + move=> [*]; subst.
      exists pi1, pic2.1; split => //.
      + by rewrite hc1; case: (pic1).
      + by rewrite hc2; case: (pic2).
      split => //; apply incl_refl.
    move=> /hrec [pi [pi3 [???[? h]]]]; exists pi, pi3; split => //.
    by split => //; apply/(incl_trans h)/incl_merge_l.
  Qed.

  Local Lemma pi_i_whileP ii a c1 e c2 pi1 pi2:
    pi_i pi1 (MkI ii (Cwhile a c1 e c2)) = ok pi2 ->
    exists pi pi3 c1' c2', 
      [/\ pi_c pi_i pi c1 = ok (pi2.1, c1'), 
          pi_c pi_i pi2.1 c2 = ok (pi3, c2'),
          pi_i pi (MkI ii (Cwhile a c1 e c2)) = ok pi2,
          pi2 = (pi2.1, MkI ii (Cwhile a c1' (pi_e pi2.1 e) c2'))
        & incl pi pi3 /\ incl pi pi1 ].
  Proof.
    rewrite /=; t_xrbindP => -[[[pi2' c1'] e'] c2'] hl [<-] /=.
    have [pi [pi3 [hc1 hc2 he [hi1 hi2]]]]:= loop_whileP hl; subst e'.
    exists pi, pi3, c1', c2'; split => //.
    by rewrite compiler_util.Loop.nbP /= hc1 /= hc2 /= hi1 /=.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p1 ev Pc Pi_r.
  Proof.
    move => s1 s2 s3 s4 a c1 e c2 _ hc1 he _ hc2 _ hw ii pi pi2 vm1.
    move=> /pi_i_whileP [pi1 [pi3 [c1' [c2' [hc1_ hc2_ hw_ hpi2 [hi1 hi2]]]]]] hu hv.
    rewrite hpi2 in hw_ |- *.
    have hv1 := valid_pi_incl hi2 hv.
    have [vm2 [/= hu2 hv2 hs1]]:= hc1 _ _ _ hc1_ hu hv1.
    have [vm3 [/= hu3 hv3 hs2]]:= hc2 _ _ _ hc2_ hu2 hv2.
    have {hv3}hv3 := valid_pi_incl hi1 hv3.
    have [vm4 [/= hu4 hv4 /sem_IE hsw]]:= hw _ _ _ _ hw_ hu3 hv3.
    exists vm4; split => //.
    constructor; apply: Ewhile_true; eauto; rewrite -eq_globs.
    by have [v' -> /value_uinclE ->]:= pi_eP_uincl hv2 hu2 he.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p1 ev Pc Pi_r.
  Proof.
    move => s1 s2 a c1 e c2 _ hc1 he ii pi pi2 vm1.
    move=> /pi_i_whileP [pi1 [pi3 [c1' [c2' [hc1_ hc2_ hw_ hpi2 [hi1 hi2]]]]]] hu hv.
    rewrite hpi2 in hw_ |- *.
    have hv1 := valid_pi_incl hi2 hv.
    have [vm2 [/= hu2 hv2 hs1]]:= hc1 _ _ _ hc1_ hu hv1.
    exists vm2; split => //.
    constructor; apply: Ewhile_false; eauto; rewrite -eq_globs.
    by have [v' -> /value_uinclE ->]:= pi_eP_uincl hv2 hu2 he.
  Qed.

  Local Lemma loop_forP ii x c n pi1 pi c' : 
    loop_for pi_i ii x c n pi1 = ok (pi, c') ->
    exists pi3, 
     [/\ pi_c pi_i (remove pi x) c = ok (pi3, c'),
         incl pi pi3
       & incl pi pi1].
  Proof.
    elim: n pi1 => //= n hrec pi1.
    t_xrbindP => -[pi3 c''] /= hc; case: ifP => hincl.
    +  move=> [??]; subst pi1 c''; exists pi3; split => //; apply incl_refl.
    move=> /hrec [pi3' [h1 h2 h3]]; exists pi3'; split => //.
    by apply/(incl_trans h3)/incl_merge_l.
  Qed.

  Local Lemma Hfor : sem_Ind_for p1 ev Pi_r Pfor.
  Proof.
    move => s1 s2 i d lo hi c vlo vhi he1 he2 _ hfor ii pi pi2 vm1 /=.
    t_xrbindP => -[pi' c'] /= /loop_forP [pi3] [hpic hi1 hi2] ?; subst pi2 => /= hu hv.
    have hv' := valid_pi_incl hi2 hv.
    have [/= vm2 [hu2 hv2 hs]]:= hfor _ _ _ hpic hi1 hu hv'.
    exists vm2; split => //. 
    constructor; econstructor; eauto; rewrite -eq_globs.
    + by have [v' -> /value_uinclE ->] := pi_eP_uincl hv hu he1.
    by have [v' -> /value_uinclE ->] := pi_eP_uincl hv hu he2.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    move=> s i c pi pi2 vm1 _ hincl hu hv.
    by exists vm1; split => //; constructor.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p1 ev Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i w ws c hwi _ hc _ hfor pi pi2 vm1 hc_ hincl hu hv.
    have [{hv}hv {hwi}hwi]:= write_var_valid_pi hv hwi.
    have [vm1' hwi' hu']:= write_var_uincl hu (value_uincl_refl _) hwi.
    have [vm2 [hu2 hv2 hs2]] := hc _ _ _ hc_ hu' hv.
    have [vm3 [hu3 hv3 hsf]] := hfor _ _ _ hc_ hincl hu2 (valid_pi_incl hincl hv2).
    by exists vm3; split => //; econstructor; eauto.
  Qed.

  Local Lemma Hcall : sem_Ind_call p1 ev Pi_r Pfun.
  Proof.
    move=> s1 scs m2 s2 xs fn args vargs vs hargs _ hf hwr ii pi pi2 vm1 /=.
    case heq : pi_lvs => [pi' xs'] [<-] hu hv.
    have [vargs' hargs' hus]:= pi_esP_uincl hv hu hargs.
    have [vs' hvs' hc]:= hf _ hus.
    have [vm2 ]:= pi_lvsP_uincl (s := with_scs (with_mem s1 m2) scs) hu hvs'
          (valid_pi_with_scs scs (valid_pi_remove_m m2 hv)) hwr.
    rewrite heq /= => -[hu' hv' hwr'].
    exists vm2; split => //.
    by constructor; econstructor; eauto; rewrite -eq_globs.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p1 ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn [ii si p c so r ev0] /= vargs' vargs s0 s1 s2 vres vres'.
    move=> hget htr hinit hwr _ hc hres hrtr hscs hfin.
    have [fd2 /=]:= all_checked hget.
    t_xrbindP => -[pi2 c'] hc_ ? hget2 vargs1 hvargs1; subst fd2.
    have [vargs1' {htr} htr hua] := mapM2_dc_truncate_val htr hvargs1.
    have [{hua hwr} vm1 hwr hu] := write_vars_uincl (vm_uincl_refl _) hua hwr. 
    have [{hc hc_ hu}vm2 [hu' hv' hs]] := hc _ _ _ hc_ hu (valid_pi_empty _ _).
    have [{hres hu'} vs hvs huvs] := get_var_is_uincl hu' hres.
    have [{hrtr huvs} vs' hrtr huvs] := mapM2_dc_truncate_val hrtr huvs.
    exists vs' => //; econstructor; eauto => /=.
    by case: (s0) hinit => emem evm /=; rewrite eq_p_extra.
  Qed.

  Lemma pi_callP f scs mem scs' mem' va va' vr:
    List.Forall2 value_uincl va va' ->
    sem_call p1 ev scs mem f va scs' mem' vr ->
    exists vr', sem_call p2 ev scs mem f va' scs' mem' vr' /\ List.Forall2 value_uincl vr vr'.
  Proof.
    move=> hall hsem.
    have [vr' ??] :=
      sem_call_Ind
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
        hsem
        _
        hall.
    by exists vr'.
  Qed.

End PROOF.

End WITH_PARAMS.
