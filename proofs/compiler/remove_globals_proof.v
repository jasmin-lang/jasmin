(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import xseq.
Require Import compiler_util ZArith expr psem remove_globals low_memory.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition gd_incl (gd1 gd2: glob_decls) :=
  forall g v, get_global gd1 g = ok v -> get_global gd2 g = ok v.

Lemma gd_inclT gd3 gd1 gd2 :  gd_incl gd1 gd3 -> gd_incl gd3 gd2 -> gd_incl gd1 gd2.
Proof. by move=> h1 h2 g v /h1 /h2. Qed.

Module INCL. Section INCL.

  Section INCL_E.
    Context (gd1 gd2: glob_decls) (s: estate) (hincl: gd_incl gd1 gd2).
    Let P e : Prop :=
      ∀ v, sem_pexpr gd1 s e = ok v → sem_pexpr gd2 s e = ok v.
    Let Q es : Prop :=
      ∀ vs, sem_pexprs gd1 s es = ok vs → sem_pexprs gd2 s es = ok vs.

    Lemma gd_incl_gvar (x : gvar) (v : value) :
      get_gvar gd1 (evm s) x = ok v → get_gvar gd2 (evm s) x = ok v.
    Proof. by rewrite /get_gvar; case: x => x [] //=; apply: hincl. Qed.

    Lemma gd_incl_e_es : (∀ e, P e) ∧ (∀ es, Q es).
    Proof.
      apply: pexprs_ind_pair; split; subst P Q => //=.
      - move => e rec es ih q; t_xrbindP => v ok_v vs ok_vs <- {q}.
        by rewrite (rec _ ok_v) /= (ih _ ok_vs).
      - by apply gd_incl_gvar.
      - move => sz x e rec v; apply: on_arr_gvarP => n t h1 h2; t_xrbindP => z v1 /rec -> hz w.
        by rewrite /on_arr_var (gd_incl_gvar h2) /= hz /= => -> <-.
      - by move => sz x e hrec v; t_xrbindP => ?? -> /= -> ?? /hrec -> /= -> ? /= -> <-.
      - by move=> ? e hrec v; t_xrbindP => ? /hrec -> <-.
      - by move=> ? e1 hrec1 e2 hrec2 v; t_xrbindP => ? /hrec1 -> ? /= /hrec2 -> <-.
      - by move => op es rec v; rewrite -!/(sem_pexprs _ _); t_xrbindP => vs /rec ->.
      move=> t e1 hrec1 e2 hrec2 e3 hrec3 v.
      by t_xrbindP => ?? /hrec1 -> /= -> ?? /hrec2 -> /= -> ?? /hrec3 -> /= -> /= <-.
    Qed.

  End INCL_E.

  Definition gd_incl_e gd1 gd2 s e v h :=
    (@gd_incl_e_es gd1 gd2 s h).1 e v.

  Definition gd_incl_es gd1 gd2 s es vs h :=
    (@gd_incl_e_es gd1 gd2 s h).2 es vs.

  Lemma gd_incl_wl gd1 gd2 x v (s1 s2:estate) :
    gd_incl gd1 gd2 ->
    write_lval gd1 x v s1 = ok s2 ->
    write_lval gd2 x v s1 = ok s2.
  Proof.
    move=> hincl;case: x => //=.
    + by move=> ws x e;t_xrbindP => ?? -> /= -> ?? /(gd_incl_e hincl) -> /= -> ? -> /= ? -> <-.
    move=> sz x e; apply: on_arr_varP;rewrite /on_arr_var => ?? h1 ->.
    by t_xrbindP => ?? /(gd_incl_e hincl) -> /= -> ? -> /= ? -> /= ? -> <-.
  Qed.

  Lemma gd_incl_wls gd1 gd2 xs vs s1 s2 :
    gd_incl gd1 gd2 ->
    write_lvals gd1 s1 xs vs = ok s2 ->
    write_lvals gd2 s1 xs vs = ok s2.
  Proof.
    move=> hincl;elim: xs vs s1 s2 => //= x xs hrec [|v vs] s1 s2 //=.
    by t_xrbindP => ? /(gd_incl_wl hincl) -> /hrec /= ->.
  Qed.

  Context (P1:uprog) (ev:unit) (gd2:glob_decls).

  Notation gd := (P1.(p_globs)).

  Hypothesis hincl : gd_incl gd gd2.

  Let P2 := {| p_globs := gd2; p_funcs := P1.(p_funcs); p_extra := P1.(p_extra) |}.

  Let Pc s1 c s2 := sem P2 ev s1 c s2.

  Let Pi_r s1 i s2 := sem_i P2 ev s1 i s2.

  Let Pi s1 i s2 := sem_I P2 ev s1 i s2.

  Let Pfor x vs s1 c s2 := sem_for P2 ev x vs s1 c s2.

  Let Pfun m1 fn vs1 m2 vs2 := sem_call P2 ev m1 fn vs1 m2 vs2.

  Local Lemma Hnil : sem_Ind_nil Pc.
  Proof. move=> s; constructor. Qed.

  Local Lemma Hcons : sem_Ind_cons P1 ev Pc Pi.
  Proof. by move=> s1 s2 s3 i c ? h1 ?; apply: Eseq. Qed.

  Local Lemma HmkI : sem_Ind_mkI P1 ev Pi_r Pi.
  Proof. move=> ?????;apply: EmkI. Qed.

  Local Lemma Hasgn : forall s1 s2 (x : lval) (tag : assgn_tag) ty (e : pexpr) v v',
    sem_pexpr gd s1 e = ok v ->
    truncate_val ty v = ok v' ->
    write_lval gd x v' s1 = ok s2 ->
    Pi_r s1 (Cassgn x tag ty e) s2.
  Proof.
    move=> ???????? /(gd_incl_e hincl) h1 h2 /(gd_incl_wl hincl) h3.
    apply: Eassgn;eauto.
  Qed.

  Local Lemma Hopn : forall s1 s2 t (o : sopn) (xs : lvals) (es : pexprs),
    sem_sopn gd o s1 xs es = Ok error s2 ->
    Pi_r s1 (Copn xs t o es) s2.
  Proof.
    move=> ??????;rewrite /sem_sopn.
    t_xrbindP => ?? /(gd_incl_es hincl) h1 h2 /(gd_incl_wls hincl) h3.
    by econstructor;eauto;rewrite /sem_sopn h1 /= h2.
  Qed.

  Local Lemma Hif_true : forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    sem_pexpr gd s1 e = ok (Vbool true) ->
    sem P1 ev s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof. by move=> ????? /(gd_incl_e hincl) h1 ? h2; apply Eif_true. Qed.

  Local Lemma Hif_false : forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    sem_pexpr gd s1 e = ok (Vbool false) ->
    sem P1 ev s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof. by move=> ????? /(gd_incl_e hincl) h1 ? h2; apply Eif_false. Qed.

  Local Lemma Hwhile_true : forall (s1 s2 s3 s4 : estate) a (c : cmd) (e : pexpr) (c' : cmd),
    sem P1 ev s1 c s2 -> Pc s1 c s2 ->
    sem_pexpr gd s2 e = ok (Vbool true) ->
    sem P1 ev s2 c' s3 -> Pc s2 c' s3 ->
    sem_i P1 ev s3 (Cwhile a c e c') s4 -> Pi_r s3 (Cwhile a c e c') s4 -> Pi_r s1 (Cwhile a c e c') s4.
  Proof.
    move=> ????????? h1 /(gd_incl_e hincl) h2 ? h3 ? h4; apply: Ewhile_true; eauto.
  Qed.

  Local Lemma Hwhile_false : forall (s1 s2 : estate) a (c : cmd) (e : pexpr) (c' : cmd),
    sem P1 ev s1 c s2 -> Pc s1 c s2 ->
    sem_pexpr gd s2 e = ok (Vbool false) ->
    Pi_r s1 (Cwhile a c e c') s2.
  Proof. move=> ??????? h1 /(gd_incl_e hincl) ?; apply: Ewhile_false; eauto. Qed.

  Local Lemma Hfor : sem_Ind_for P1 ev Pi_r Pfor.
  Proof.
    move=> ????????? /(gd_incl_e hincl) h1 /(gd_incl_e hincl) h2 h3.
    apply: Efor;eauto.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof. move=> ???;constructor. Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons P1 ev Pc Pfor.
  Proof. move=> ???????? h1 ? h2 h3 h4;econstructor;eauto. Qed.

  Local Lemma Hcall : sem_Ind_call P1 ev Pi_r Pfun.
  Proof.
    move=> ????????? /(gd_incl_es hincl) h1 ? h2 /(gd_incl_wls hincl) h3.
    econstructor;eauto.
  Qed.

  Local Lemma Hproc : sem_Ind_proc P1 ev Pc Pfun.
  Proof. move=> ?????????? h1 h2 h3 ? h4 h5 h6; econstructor;eauto. Qed.

  Lemma gd_incl_fun m (fn : funname) (l : seq value) m0 vs:
      sem_call P1 ev m fn l m0 vs -> Pfun m fn l m0 vs.
  Proof.
    apply: (@sem_call_Ind _ _ _ P1 ev Pc Pi_r Pi Pfor Pfun
             Hnil Hcons HmkI Hasgn Hopn Hif_true Hif_false Hwhile_true Hwhile_false
             Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

End INCL. End INCL. Import INCL.

Module EXTEND. Section PROOFS.

  Context (is_glob : var -> bool).
  Context (fresh_id : glob_decls -> var -> Ident.ident).

  Let Pi (i:instr) :=
    forall gd1 gd2,
      extend_glob_i is_glob fresh_id i gd1 = ok gd2 ->
      gd_incl gd1 gd2.

  Let Pr (i:instr_r) := forall ii, Pi (MkI ii i).

  Let Pc (c:cmd) :=
    forall gd1 gd2,
      foldM (extend_glob_i is_glob fresh_id) gd1 c = ok gd2 ->
      gd_incl gd1 gd2.

  Local Lemma Hmk  : forall i ii, Pr i -> Pi (MkI ii i).
  Proof. move=> ?? h;apply h. Qed.

  Local Lemma Hnil : Pc [::].
  Proof. by move=> ?? [<-]. Qed.

  Local Lemma Hcons: forall i c, Pi i -> Pc c -> Pc (i::c).
  Proof.
    by move=> i c hi hc gd1 gd2 /=;t_xrbindP => gd3 /hi h1 /hc; apply: gd_inclT.
  Qed.

  (* TODO: Move *)
  Lemma hasPP T (a : pred T) (s : seq T): reflect (exists2 x : T, List.In x s & a x) (has a s).
  Proof.
    elim: s => /=;first by constructor => -[]. 
    move=> x l ih; apply (equivP orP);split.
    + by move=> [ h| /ih []];eauto.
    move=> [x' [<- ?| ??]];first by auto.
    by right; apply /ih;eauto.
  Qed.

  Lemma assoc_memP (T : eqType) U (s : seq (T * U)) (x : T) (w : U): assoc s x = Some w → List.In (x, w) s.
  Proof.
    by elim: s => //= -[x' u] l ih; case: eqP => [-> [<-] | ? /ih];auto.
  Qed.

  Local Lemma Hasgn: forall x tg ty e, Pr (Cassgn x tg ty e).
  Proof.
    move=> [ii ty|x|ws x e|ws x e] ?? e1 ??? //=. 1,3-4: by move=> [<-].
    case: ifP => ?; last by move=> [<-].
    case: e1 => // - [] // w [] // z; rewrite /add_glob.
    case:ifPn => hhas1; first by move=> [<-].
    case:ifPn => // /hasPP hhas2 [<-] g v.
    rewrite /get_global /get_global_value /=.
    case:eqP => heq //;subst g.
    case ha : assoc => [|// ].
    by have hin := assoc_memP ha; elim hhas2;eauto.
  Qed.

  Local Lemma Hopn : forall xs t o es, Pr (Copn xs t o es).
  Proof. by move=> xs t o es ii gd1 gd2 /= [<-]. Qed.

  Local Lemma Hif  : forall e c1 c2, Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof.
    move=> e c1 c2 hc1 hc2 ii gd1 gd2 /=.
    by t_xrbindP => gd3 /hc1 h1 /hc2; apply: gd_inclT.
  Qed.

  Local Lemma Hfor : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir,lo,hi) c).
  Proof. by move=> ????? hc ii gd1 gd2 /= /hc. Qed.

  Local Lemma Hwhile : forall a c e c', Pc c -> Pc c' -> Pr (Cwhile a c e c').
  Proof.
    move=> a c e c' hc hc' ii gd1 gd2 /=.
    by t_xrbindP => gd3 /hc h1 /hc'; apply gd_inclT.
  Qed.

  Local Lemma Hcall: forall i xs f es, Pr (Ccall i xs f es).
  Proof. by move=> i xs f es ii gd1 gd2 /= [<-]. Qed.

  Local Lemma extend_glob_cP c gd1 gd2 :
    foldM (extend_glob_i is_glob fresh_id) gd1 c = ok gd2 ->
    gd_incl gd1 gd2.
  Proof.
    apply (@cmd_rect Pr Pi Pc Hmk Hnil Hcons Hasgn Hopn Hif Hfor Hwhile Hcall c).
  Qed.

End PROOFS.

Lemma extend_glob_progP is_glob fresh_id P gd' :
  extend_glob_prog is_glob fresh_id P = ok gd' ->
  gd_incl (p_globs P) gd'.
Proof.
  rewrite /extend_glob_prog.
  elim: (p_funcs P) (p_globs P) => /= [gd [<-] // | fd fds hrec gd].
  by t_xrbindP => gd1 /extend_glob_cP h1 /hrec; apply: gd_inclT.
Qed.

End EXTEND. Import EXTEND.

Module RGP. Section PROOFS.

  Context (is_glob : var -> bool).
  Context (fresh_id : glob_decls -> var -> Ident.ident).

  Notation venv := (Mvar.t var).

  Section FDS.

  Context (P:uprog) (ev:unit).

  Context (fds: ufun_decls).
  Notation gd := (p_globs P).

  Hypothesis fds_ok : mapM (remove_glob_fundef is_glob gd) (p_funcs P) = ok fds.
  Hypothesis uniq_gd : uniq (map fst gd).
  Notation P' := {|p_globs := gd; p_funcs := fds; p_extra := p_extra P |}.

  Definition valid (m:venv) (s1 s2:estate) :=
    [/\ s1.(emem) = s2.(emem),
        (forall x, ~~is_glob x -> get_var (evm s1) x = get_var (evm s2) x),
        (forall x g, Mvar.get m x = Some g -> is_glob x) &
        (forall x g v,
           Mvar.get m x = Some g ->
           get_var (evm s1) x = ok v ->
           get_global gd g = ok v) ].

  Section REMOVE_GLOB_E.
    Context (m: venv) (ii: instr_info) (s1 s2: estate) (hvalid: valid m s1 s2).

    Let Pe e : Prop :=
      ∀ e' v,
        remove_glob_e is_glob ii m e = ok e' →
        sem_pexpr gd s1 e = ok v →
        sem_pexpr gd s2 e' = ok v.

    Let Pes es : Prop :=
      ∀ es' vs,
        mapM (remove_glob_e is_glob ii m) es = ok es' →
        sem_pexprs gd s1 es = ok vs →
        sem_pexprs gd s2 es' = ok vs.

    Lemma remove_glob_e_esP : (∀ e, Pe e) ∧ (∀ es, Pes es).
    Proof.
      case: hvalid => hmem hm1 hm2 hm3.
      apply: pexprs_ind_pair; subst Pe Pes; split => //=.
      - by move => _ _ [<-] [<-].
      - move => e he es hes q qs; t_xrbindP => e' ok_e' es' ok_es' <- {q} v ok_v vs ok_vs <- {qs} /=.
        by rewrite (he _ _ ok_e' ok_v) (hes _ _ ok_es' ok_vs).
      - by move => z _ _ [<-] [<-].
      - by move => b _ _ [<-] [<-].
      - by move => n _ _ [<-] [<-].
      -  move => [x []] e' v /=; rewrite /get_gvar /=.
        + case : ifP => hx.
          + case heq: (Mvar.get _ _) => [ g | // ] [<-].
            by move => /(hm3 _ _ _ heq); apply.
          by move=> [<-] h; rewrite /= /get_gvar -hm1 // hx.
        by case => [<-] h;rewrite /= /get_gvar /=.
      - move => ws x e he q v; case: ifPn => // hx; t_xrbindP => e' ok_e' <- {q} /=.
        apply: on_arr_gvarP; rewrite /on_arr_var => ???.
        have -> : (get_gvar gd s1.(evm) x) = (get_gvar gd s2.(evm) x).
        + by rewrite /get_gvar; case:ifP hx => //= hx /hm1.        
        by move=> -> /=; t_xrbindP => ?? /he /= -> //= -> /= ? -> /= ->.
      - move => ??? ih ??; case: ifPn => // hn.
        t_xrbindP => ? /ih h <- /= ??; rewrite (hm1 _ hn) => -> /= -> ?? /h -> /= -> ? /=.
        by rewrite hmem => -> <-.
      - by move=> ?? hrec ??; t_xrbindP => ? /hrec h <- /= ? /h -> /=.
      - by move=> ?? hrec1 ? hrec2 ??; t_xrbindP=> ? /hrec1 h1 ? /hrec2 h2 <- ? /= /h1 -> ? /h2 ->.
      - move => ?? ih ??; t_xrbindP => ? /ih{ih} ih <- ? /ih /=.
        by rewrite -/(sem_pexprs _ _) => ->.
      move=> ? ? hrec1 ? hrec2 ? hrec3 ??.
      by t_xrbindP => ? /hrec1 h1 ? /hrec2 h2 ? /hrec3 h3 <- ?? /= /h1 -> /= -> ?? /h2 -> /= -> ?? /h3 -> /= -> <-.
    Qed.

  End REMOVE_GLOB_E.

  Definition remove_glob_eP m ii s1 s2 e e' v h :=
    (@remove_glob_e_esP m ii s1 s2 h).1 e e' v.

  Definition remove_glob_esP m ii s1 s2 es es' vs h :=
    (@remove_glob_e_esP m ii s1 s2 h).2 es es' vs.

  Lemma write_var_remove (x:var_i) m s1 s2 v vm :
    ~~ is_glob x ->
    valid m s1 s2 ->
    set_var (evm s1) x v = ok vm ->
    exists s2', valid m (with_vm s1 vm) s2' /\ write_var x v s2 = ok s2'.
  Proof.
    rewrite /write_var /set_var => hglob hval; case:(hval) => hmem hm1 hm2 hm3.
    apply: on_vuP.
    + move=> ? -> <- /=;eexists;split;last reflexivity.
      split => //=.
      + move=> y hy; rewrite /get_var /= /on_vu.
        case: (v_var x =P y) => [<- | /eqP heq].
        + by rewrite !Fv.setP_eq.
        by rewrite !Fv.setP_neq //; apply (hm1 _ hy).
      move=> y g v0 hy.
      rewrite /get_var /on_vu Fv.setP_neq;first by apply: hm3 hy.
      by apply /eqP => ?;subst y; move: hglob; rewrite (hm2 _ _ hy).
    move=> ->; case:ifPn => // hx [<-] /=;eexists;split;last reflexivity.
    split => //=.
    + move=> y hy; rewrite /get_var /= /on_vu.
      case: (v_var x =P y) => [<- | /eqP heq].
      + by rewrite !Fv.setP_eq.
      by rewrite !Fv.setP_neq //; apply (hm1 _ hy).
    move=> y g v0 hy.
    rewrite /get_var /on_vu Fv.setP_neq;first by apply: hm3 hy.
    by apply /eqP => ?;subst y; move: hglob; rewrite (hm2 _ _ hy).
  Qed.

  Lemma remove_glob_lvP m ii s1 s1' s2 lv lv' v :
    valid m s1 s2 ->
    remove_glob_lv is_glob ii m lv = ok lv' ->
    write_lval gd lv v s1 = ok s1' ->
    exists s2',
      valid m s1' s2' /\ write_lval gd lv' v s2 = ok s2'.
  Proof.
    move=> hval; case:(hval) => hmem hm1 hm2 hm3; case:lv => [vi ty|x|ws x e|ws x e] /=.
    + move=> [<-]; apply on_vuP => [?|] hv /=;rewrite /write_none.
      + by move=> <-;exists s2;split => //; rewrite hv.
      by case : ifPn => // ? [<-]; exists s2; rewrite hv.
    + case: ifPn => // hg [<-] /=; rewrite /write_var.
      t_xrbindP => ? hset <-.
      apply (write_var_remove hg hval hset).
    + case: ifPn => hg //.
      t_xrbindP => ? /(remove_glob_eP hval) h <- ??.
      rewrite hmem (hm1 _ hg) /= => -> /= -> ?? /h -> /= -> ? -> ? /= -> <- /=.
      by eexists;split;last reflexivity; split.
    case: ifPn => hg //.
    t_xrbindP => ? /(remove_glob_eP hval) h <-.
    apply: on_arr_varP => ?? hty; rewrite (hm1 _ hg) => hget.
    t_xrbindP => ?? /h /= -> /= -> ?.
    rewrite /on_arr_var /= hget /= => -> ? /= -> ? /= hset <-.
    apply (write_var_remove hg hval hset).
  Qed.

  Lemma remove_glob_lvsP  m ii s1 s1' s2 lv lv' v :
    valid m s1 s2 ->
    mapM (remove_glob_lv is_glob ii m) lv = ok lv' ->
    write_lvals gd s1 lv v = ok s1' ->
    exists s2',
      valid m s1' s2' /\ write_lvals gd s2 lv' v = ok s2'.
  Proof.
    elim: lv lv' v s1 s1' s2 => //=.
    + by move=> ? []// s1 s1' s2 ? [<-] [<-]; exists s2.
    move=> x xs hrec lv' vs s1 s1' s2 hval.
    t_xrbindP=> x' /(remove_glob_lvP hval) h1 xs' /hrec h2 <-.
    case: vs => // v vs.
    t_xrbindP => s3 /h1 [s4 [hs4 w4]] /(h2 _ _ _ _ hs4) [s5 [hs5 w5]].
    exists s5;split => //.
    by rewrite /write_lvals /= w4.
  Qed.

  Let Pc s1 c s2 :=
    forall m m' c' fn, remove_glob (remove_glob_i is_glob gd fn) m c = ok (m', c') ->
    forall s1', valid m s1 s1' ->
    exists s2', valid m' s2 s2' /\ sem P' ev s1' c' s2'.

  Let Pi s1 i s2 :=
    forall m m' c' fn, remove_glob_i is_glob gd fn m i = ok (m', c') ->
    forall s1', valid m s1 s1' ->
    exists s2', valid m' s2 s2' /\ sem P' ev s1' c' s2'.

  Let Pi_r s1 i s2 := forall ii, Pi s1 (MkI ii i) s2.

  Let Pfor xi vs s1 c s2 :=
    ~~is_glob xi.(v_var) ->
    forall m m' c' fn, remove_glob (remove_glob_i is_glob gd fn) m c = ok (m', c') ->
    Mincl m m' ->
    forall s1', valid m s1 s1' ->
    exists s2', valid m s2 s2' /\ sem_for P' ev xi vs s1' c' s2'.

  Let Pfun m fn vs m' vs' :=
    sem_call P' ev m fn vs m' vs'.

  Local Lemma Hnil : sem_Ind_nil Pc.
  Proof.
    move=> s1 m m' c' fn /= [<- <-] s1' hv; exists s1';split => //.
    econstructor.
  Qed.

  Local Lemma Hcons : sem_Ind_cons P ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ hi _ hc m m' c' fn /=.
    t_xrbindP => -[mi ci] /hi{hi}hi [mc cc] /hc{hc}hc <- <- ? /hi [s2' [/hc [s3' [hv sc] si]]].
    exists s3';split => //=; apply: sem_app si sc.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI P ev Pi_r Pi.
  Proof. done. Qed.

  Lemma find_globP ii xi sz (w:word sz) g :
    find_glob ii xi gd w = ok g ->
    get_global gd g =  ok (Vword w).
  Proof.
    rewrite /find_glob /get_global /get_global_value.
    elim: gd uniq_gd => //= -[g' z'] gd hrec /andP /= [hg' huniq]; case: ifPn => /= /andP.
    + move=> [];case : z' => //= ws s /eqP heq /andP[] /eqP ? /eqP ? [?];subst.
      by rewrite eq_refl /= heq eq_refl zero_extend_u.
    move=> hn /(hrec huniq) hget {hrec}.
    case: eqP => heq //; subst g'.
    case heq : assoc hget hg' => [z1 | //].
    by rewrite (assoc_mem_dom' heq).
  Qed.

  Local Lemma Hasgn : sem_Ind_assgn P Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' he hv hw ii m m' c' fn /= hrm s1' hval.
    move: hrm; t_xrbindP => e' /(remove_glob_eP hval) -/(_ _ he) he'.
    have :
      (Let lv := remove_globals.remove_glob_lv is_glob ii m x in
      ok (m, [:: MkI ii (Cassgn lv tag ty e')])) = ok (m', c') ->
      exists s2', valid m' s2 s2' /\ sem P' ev s1' c' s2'.
    + t_xrbindP => x' /(remove_glob_lvP hval) -/(_ _ _ hw) [s2' [hs2' hw' ]] <- <-.
      exists s2';split => //; apply sem_seq1; constructor; econstructor; eauto.
    case: x hw => //=.
    move=> xi hxi hdef; case: ifPn => // hglob {hdef}.
    case: e' he' => // - [] // sz [] //= z [?]; subst v.
    case: andP => //= -[/eqP ? /eqP htxi];subst ty.
    move: hv; rewrite /truncate_val /= truncate_word_u /= => -[?]; subst v'.
    move: xi htxi hglob hxi.
    rewrite /write_var /set_var => -[[xty xn] xii] /= ? hglob; subst xty.
    rewrite /pof_val /= sumbool_of_boolET => -[<-].
    t_xrbindP => g hfind <- <-;exists s1'; split; last by constructor.
    set x := {| vtype := _ |}.
    case: hval => hm hm1 hm2 hm3; split => //=.
    + move=> y hy; rewrite /get_var /on_vu.
      rewrite Fv.setP_neq; first by apply hm1.
      by apply /eqP => ?;subst y;move: hy;rewrite hglob.
    + by move=> y gy;rewrite Mvar.setP; case:eqP => [<- // | ?]; apply hm2.
    move=> y gy v;rewrite Mvar.setP;case:eqP => [<- | /eqP hneq].
    + move=> [<-]. rewrite /get_var Fv.setP_eq /= => -[<-].
      by apply: find_globP hfind.
    by rewrite /get_var Fv.setP_neq //; apply hm3.
  Qed.

  Local Lemma Hopn : sem_Ind_opn P Pi_r.
  Proof.
   move=> s1 s2 t o xs es ho ii m m' c fn /= hrm s1' hval.
   move: hrm; t_xrbindP.
   move=> xs' /(remove_glob_lvsP hval) hxs' es' /(remove_glob_esP hval) hes' <- <-.
   move: ho;rewrite /sem_sopn; t_xrbindP => vs vres /hes' h1 h2 /hxs' [s2' [hval' h]].
   exists s2';split => //.
   by apply sem_seq1; constructor; constructor; rewrite /sem_sopn h1 /= h2.
  Qed.

  Lemma MinclP m1 m2 x g :
    Mincl m1 m2 ->
    Mvar.get m1 x = Some g ->
    Mvar.get m2 x = Some g.
  Proof.
    move=> /allP hincl.
    have /= h := Mvar.elementsP (x,g) m1.
    by move=> /h {h} /hincl;case: Mvar.get => //= g' /eqP ->.
  Qed.

  Lemma valid_Mincl m1 m2 s s' :
    Mincl m1 m2 ->
    valid m2 s s' ->
    valid m1 s s'.
  Proof.
    move=> hincl [hmem hm1 hm2 hm3];split => //.
    + by move=> x g /(MinclP hincl) -/hm2.
    by move=> x g v /(MinclP hincl); apply hm3.
  Qed.

  Lemma merge_incl_l m1 m2 : Mincl (merge_env m1 m2) m1.
  Proof.
    apply /allP => -[x g].
    rewrite /merge_env => /Mvar.elementsP /=.
    rewrite Mvar.map2P //. case: Mvar.get => // g1.
    by case: Mvar.get => //= g2; case:ifP => // _ [<-].
  Qed.

  Lemma merge_incl_r m1 m2 : Mincl (merge_env m1 m2) m2.
  Proof.
    apply /allP => -[x g].
    rewrite /merge_env => /Mvar.elementsP /=.
    rewrite Mvar.map2P //. case: Mvar.get => // g1.
    by case: Mvar.get => //= g2; case:ifP => // /eqP <- [<-].
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true P ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 he _ hc ii m m' c' fn /= hrm s1' hval.
    move: hrm; t_xrbindP => e' /(remove_glob_eP hval) -/(_ _ he) he'.
    move=> [m1 c1'] /hc -/(_ _ hval) [s2' [hval' hc1']].
    move=> [m2 c2'] h /= <- <-.
    exists s2'; split.
    + apply: valid_Mincl hval'; apply merge_incl_l.
    by apply sem_seq1; constructor; apply Eif_true.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false P ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 he _ hc ii m m' c' fn /= hrm s1' hval.
    move: hrm; t_xrbindP => e' /(remove_glob_eP hval) -/(_ _ he) he'.
    move=> [m1 c1'] h /= [m2 c2'] /hc -/(_ _ hval) [s2' [hval' hc1']] <- <-.
    exists s2'; split.
    + apply: valid_Mincl hval'; apply merge_incl_r.
    by apply sem_seq1; constructor; apply Eif_false.
  Qed.

  Lemma MinclR m : Mincl m m.
  Proof. by apply /allP => -[x g] /Mvar.elementsP ->. Qed.

  Lemma MinclT m2 m1 m3: Mincl m1 m2 -> Mincl m2 m3 -> Mincl m1 m3.
  Proof.
    move=> /allP h1 /allP h2; apply /allP => x /h1.
    case heq : (Mvar.get m2 x.1) => [g|//] /eqP ?; subst g.
    by apply h2; apply /Mvar.elementsP.
  Qed.

  Lemma loop2P fn check_c2 n m e c1 c2 m1:
    loop2 fn check_c2 n m = ok (Loop2_r e c1 c2 m1) ->
    exists m2 m3,
      [/\ check_c2 m3 = ok (Check2_r e (m1,c1) (m2,c2)), Mincl m3 m2 & Mincl m3 m].
  Proof.
    elim: n m => //= n hrec m; t_xrbindP.
    move=> [e' [m1' c1'] [m2' c2']] heq; case:ifPn => hincl.
    + move=> [] ????; subst e' c1' c2' m1'.
      by exists m2', m; split => //; apply MinclR.
    move=> /hrec [m2 [m3 [h1 h2]]] hm3; exists m2, m3; split=>//.
    apply: (MinclT hm3); apply merge_incl_l.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true P ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' _ hc he _ hc' _ hw ii m m' c'0 fn /= hrn s1' hval.
    move: hrn; t_xrbindP => -[e' c1' c2' m1] /loop2P [m2 [m3 []]].
    t_xrbindP => -[m4 c4] h1 /= e1 he1 [m5 c5] h2.
    have h1' := hc _ _ _ _ h1.
    have h2' := hc' _ _ _ _ h2.
    move=> ? [??] [??] hm hm1 ? <-;subst e1 m4 c4 m5 c5 m1.
    have /h1' [s2' [hs2 hc1]]: valid m3 s1 s1' by apply: valid_Mincl hval.
    have he' := remove_glob_eP hs2 he1 he.
    have [s3' [hs3 hc2]]:= h2' _ hs2.
    have : remove_glob_i is_glob gd fn m3 (MkI ii (Cwhile a c e c')) =
             ok (m', [::MkI ii (Cwhile a c1' e' c2')]).
    + by rewrite /= Loop.nbP /= h1 /= he1 /= h2 /= hm.
    move=> /hw{hw}hw; have /hw : valid m3 s3 s3' by apply: (valid_Mincl hm).
    move=> [s4' [hs4 hw']]; exists s4';split => //.
    apply sem_seq1; constructor; apply: Ewhile_true;eauto.
    by inversion hw';subst => {hw'};inversion H2;subst; inversion H4;subst.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false P ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' _ hc he ii m m' c'0 fn /= hrn s1' hval.
    move: hrn; t_xrbindP => -[e' c1' c2' m1] /loop2P [m2 [m3 []]].
    t_xrbindP => -[m4 c4] h1 /= e1 he1 [m5 c5] h2.
    move=> ? [??] [??] hm hm1 ? <-;subst e1 m4 c4 m5 c5 m1.
    have h1' := hc _ _ _ _ h1.
    have /h1' [s2' [hs2 hc1]]: valid m3 s1 s1' by apply: valid_Mincl hval.
    exists s2';split => //.
    apply sem_seq1;constructor;apply: Ewhile_false => //.
    by apply: remove_glob_eP he1 he.
  Qed.

  Local Lemma loopP fn check_c n m m' c':
    loop fn check_c n m = ok (m', c') ->
      exists m1,
      [/\ check_c m' = ok (m1,c'), Mincl m' m1 & Mincl m' m].
  Proof.
    elim: n m => //= n hrec m; t_xrbindP => -[m2 c2] /= hc.
    case:ifP => hincl.
    + by move=> []??; subst m' c2; exists m2;split => //;apply MinclR.
    move=> /hrec => -[m1 [hc' h1 h2]]. exists m1;split=>//.
    apply: (MinclT h2);apply merge_incl_l.
  Qed.

  Local Lemma Hfor : sem_Ind_for P ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi hlo hhi _ hfor ii m m' c' fn /= hrn s1' hval.
    case : ifPn hrn => // hglob.
    t_xrbindP => lo' /(remove_glob_eP hval) -/(_ _ hlo) hlo'.
    move=> hi' /(remove_glob_eP hval) -/(_ _ hhi) hhi'.
    move=> [m2 c2] /= /loopP [m1 [hc h1 h2]] [??];subst m2 c'.
    have hval': valid m' s1 s1' by apply: valid_Mincl hval.
    have [s2' [??]]:= hfor hglob _ _ _ _ hc h1 _ hval'.
    exists s2';split => //.
    apply sem_seq1;constructor;econstructor;eauto.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    move=> s xi c ii m m' c' fn hrm hincl s1' hval; exists s1';split => //; constructor.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons P ev Pc Pfor.
  Proof.
    move=> s1 s2 s3 s4 xi w ws c hw _ hc _ hfor hglob m m' c' fn hrm hincl s1' hval.
    move: hw; rewrite /write_var; t_xrbindP => vm hvm ?;subst s2.
    have [s2' [hs2' ws2']]:= write_var_remove hglob hval hvm.
    have [s3' [hs3' ws3']]:= hc _ _ _ _ hrm _ hs2'.
    have hval' := valid_Mincl hincl hs3'.
    have [s4' [hs4' ws4']]:= hfor hglob _ _ _ _ hrm hincl _ hval'.
    exists s4'; split => //; econstructor; eauto.
  Qed.

  Local Lemma Hcall : sem_Ind_call P ev Pi_r Pfun.
  Proof.
    move=> s1 m2 s2 fii xs fn args vargs rvs hargs _ hfun hres ii m m' c' fn0 /= hrm s1' hval.
    move: hrm; t_xrbindP => xs' hxs es' hes ??;subst m' c'.
    have hes' := remove_glob_esP hval hes hargs.
    have hval' : valid m (with_mem s1 m2) (with_mem s1' m2). 
    + by case: hval => hm hm1 hm2 hm3;split.
    have [s2' [hs2' hxs']]:= remove_glob_lvsP hval' hxs hres.
    exists s2';split => //.
    apply sem_seq1;constructor;econstructor;eauto.
    by case: hval => <-.
  Qed.

  Local Lemma get_fundefP fn f:
    get_fundef (p_funcs P) fn = Some f ->
    exists f',
       get_fundef (p_funcs P') fn = Some f' /\
       remove_glob_fundef is_glob gd (fn,f) = ok (fn, f').
  Proof.
    change (p_funcs P') with fds.
    elim: (p_funcs P) fds fds_ok => //=.
    move => [fn1 fd1] fds1 hrec fds'; t_xrbindP => -[fn1' fd1'] hf1 fds1' hfds1' ?; subst fds'.
    move: hf1;rewrite /remove_glob_fundef;t_xrbindP.
    move=> ? hparams ? hres mc hmc ??; subst fn1' fd1'.
    case: ifP => [/eqP eq | neq].
    + move=> [?]; subst fn1 fd1 => /=.
      rewrite eq_refl;eexists;split;first reflexivity.
      by rewrite hparams /= hres /= hmc.
    by move=> /(hrec _ hfds1') /=;rewrite neq.
  Qed.

  Local Lemma Hproc : sem_Ind_proc P ev Pc Pfun.
  Proof.
    move=> m1 m2 fn f vargs vargs' s0 s1 s2 vres vres' hget hargs hwa hi _ hc hres hres' hfi.
    rewrite /Pfun; have [f' [hget']]:= get_fundefP hget.
    rewrite /remove_glob_fundef; t_xrbindP => ? hparams res1 hres1 [m' c'] hrm ?;subst f'.
    have hval: valid (Mvar.empty var) s1 s1 by split.
    have [s2' [hs2' ws2]] := hc _ _ _ _ hrm _ hval.
    subst m2; case: (hs2') => /= hmem hm _ _.
    have hres2 : mapM (fun x : var_i => get_var (evm s2') x) (f_res f) = ok vres.
    + elim: (f_res f) (vres) res1 hres1 hres => //= x xs hrec vres0 res1.
      t_xrbindP => ?; case: ifPn => hglob // [<-] ? /hrec hres1 ? v hx vs /hres1 hxs ?.
      by subst res1 vres0; rewrite -hm //= hx /= hxs.
    econstructor; eauto.
  Qed.

  Local Lemma remove_glob_call m1 f vargs m2 vres :
     sem_call P ev m1 f vargs m2 vres ->
     Pfun m1 f vargs m2 vres.
  Proof.
    apply (@sem_call_Ind _ _ _ P ev Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn Hif_true Hif_false
              Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

  End FDS.

  Lemma remove_globP P P' f ev mem mem' va vr :
    remove_glob_prog is_glob fresh_id P = ok P' ->
    sem_call P ev mem f va mem' vr ->
    sem_call P' ev mem f va mem' vr.
  Proof.
    rewrite /remove_glob_prog; t_xrbindP => gd' /extend_glob_progP hgd.
    case: ifP => // huniq; t_xrbindP => fds hfds <- /(gd_incl_fun hgd) hf.
    apply: (remove_glob_call (P:={| p_globs := gd'; p_funcs := p_funcs P |}) hfds huniq hf).
  Qed.

End PROOFS. End RGP.
