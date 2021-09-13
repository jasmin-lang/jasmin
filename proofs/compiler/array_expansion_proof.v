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
Require Import psem array_expansion compiler_util ZArith.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Definition wf_t (m : t) := 
  forall x ai, Mvar.get m.(sarrs) x = Some ai ->
    ~ Sv.mem x m.(svars) /\
    forall i xi, Mi.get ai.(ai_elems) i = Some xi ->
      ~ Sv.mem xi m.(svars) /\
      xi.(vtype) == sword ai.(ai_ty) /\
      forall x' ai' i' xi',
        Mvar.get m.(sarrs) x' = Some ai' ->
        Mi.get ai'.(ai_elems) i' = Some xi' ->
        x <> x' \/ i <> i' -> xi != xi'.

Definition set_undef_e (t:stype) (v : exec (psem_t t)) := 
  match v with
  | Ok v => ok v
  | _ => Error ErrAddrUndef
  end.

Definition eval_array (vm : vmap) ws x i := 
  @on_arr_var _ (get_var vm x) 
     (fun n (t:WArray.array n) => 
        Let w := WArray.get AAscale ws t i in
        ok (pword_of_word w)).

Definition eq_alloc_vm (m : t) (vm1 vm2 : vmap) := 
  vm1 =[m.(svars)] vm2 /\
  forall x ai i xi, 
    Mvar.get m.(sarrs) x = Some ai ->
    Mi.get ai.(ai_elems) i = Some xi ->
    eval_uincl (set_undef_e (t := sword ai.(ai_ty)) (eval_array vm1 ai.(ai_ty) x i)) 
               (set_undef_e vm2.[xi]).

Definition eq_alloc (m : t) (s1 s2 : estate) := 
  eq_alloc_vm m s1.(evm) s2.(evm) /\
  s1.(emem) = s2.(emem).
    
Section Section.

Variable (fi : funname -> ufundef -> expand_info).
Variable p1 p2:uprog.

Local Notation gd := (p_globs p1).

Section Expr.

Context (m : t) (valid : wf_t m).

Lemma check_var_get s1 s2 x : 
  Sv.mem x (svars m) ->
  eq_alloc m s1 s2 ->
  get_var (evm s1) x = get_var (evm s2) x.
Proof. by move=> /Sv_memP hin -[] [] heq _ _; rewrite /get_var /= heq. Qed.


Lemma check_var_gets s1 s2 xs : 
  all (fun (x:var_i) => Sv.mem x (svars m)) xs ->
  eq_alloc m s1 s2 ->
  mapM (fun (x:var_i) => get_var (evm s1) x) xs = mapM (fun (x:var_i) => get_var (evm s2) x) xs.
Proof. 
  move=> hall heqa; elim: xs hall => //= x xs hrec /andP [].
  by move=> /(check_var_get) -/(_ _ _ heqa) -> /hrec ->.
Qed.

Lemma check_gvar_get s1 s2 x :
  check_gvar m x ->
  eq_alloc m s1 s2 ->
  get_gvar gd s1.(evm) x = get_gvar gd s2.(evm) x.
Proof. rewrite /get_gvar /check_gvar; case: is_lvar => //=; apply check_var_get. Qed.

Lemma eq_alloc_mem s1 s2 : eq_alloc m s1 s2 -> emem s1 = emem s2.
Proof. by case. Qed.

Lemma expand_esP_aux (s1 s2 : estate) es1 es2: 
  eq_alloc m s1 s2 ->
  expand_es m es1 = ok es2 -> 
  (∀ e, e \in es1 → 
   ∀ e2, expand_e m e = ok e2 → 
   ∀ v, sem_pexpr gd s1 e = ok v → sem_pexpr gd s2 e2 = ok v) -> 
  forall vs, sem_pexprs gd s1 es1 = ok vs -> sem_pexprs gd s2 es2 = ok vs.
Proof.
  move=> h; rewrite /sem_pexprs /expand_es.
  elim: es1 es2 => [ | e1 es1 hrec] es' /=.
  + by move=> [<-] _ ? [<-].
  t_xrbindP => e2 he1 es2 /hrec hes1 <- he ?? se1 ? /hes1 hes2 <- /=.
  rewrite (he _ _ _ he1 _ se1) ?mem_head //= hes2 // => e he'; apply: he.  
  by rewrite in_cons he' orbT.
Qed.
  
Lemma expand_eP (s1 s2: estate) : 
  eq_alloc m s1 s2 ->
  forall e1 e2, expand_e m e1 = ok e2 -> 
  forall v, sem_pexpr gd s1 e1 = ok v ->
            sem_pexpr gd s2 e2 = ok v.
Proof.
  move=> h; elim => /=.
  + by move=> z _ [<-] _ [<-].
  + by move=> b _ [<-] _ [<-].
  + by move=> n _ [<-] _ [<-].
  + by move=> x e2; t_xrbindP => _ /assertP /check_gvar_get -/(_ _ _ h) -> <-.
  + move=> aa sz x e hrec e2.
    case heq : check_gvar.
    + have hx := check_gvar_get heq h.
      t_xrbindP => e1 /hrec he <- v /=.
      rewrite hx; apply on_arr_gvarP => n t hty -> /=.
      by t_xrbindP => i vi /he -> /= -> /= w -> <-. 
    case hgetx : Mvar.get => [ai | //].
    case: (is_constP e) => // i.
    t_xrbindP => _ /assertP /eqP <- _ /assertP /eqP ->.
    case hgeti : Mi.get => [xi | //] [<-] v.
    apply on_arr_gvarP => n t hty hx /=.
    t_xrbindP => w hw <-; case: h => -[] _ /(_ _ _ _ _ hgetx hgeti).
    rewrite /get_gvar /= /get_var.
    have [hnin /(_ _ _ hgeti) [hnini [htyi _]] {hgeti}] := valid hgetx.
    case: xi htyi hnini => /= _ nxi /eqP -> hnini.
    rewrite /on_vu /= /eval_array.
    move/negbT: heq hx; rewrite /get_gvar negb_or => /andP []/negbNE -> _.
    rewrite /get_var /on_vu /= => -> /=; rewrite hw /=.
    case: (evm s2).[ _ ] => //= wi; rewrite /pval_uincl /=.
    rewrite /word_uincl => /andP; case: wi => wsi wi h3 /= [] h4 /eqP -> _.
    by have <- := cmp_le_antisym h3 h4; rewrite zero_extend_u.
  + move=> aa sz len x e hrec e2.
    t_xrbindP => _ /assertP he e1 /hrec hrec1 <- /=.
    rewrite (check_gvar_get he h) => v.
    apply on_arr_gvarP => n t hty -> /=.
    by t_xrbindP => i vi /hrec1 -> /= -> t' /= -> <-.
  + move=> sz x e hrec e2.
    t_xrbindP => _ /assertP hin e1 /hrec hrec1 <- /=.
    move=> v p vp; rewrite (check_var_get hin h) => -> /= -> /= i vi /hrec1 -> /= -> /=.
    by rewrite (eq_alloc_mem h) => ? -> <-.
  + by move=> o e1 hrec e2; t_xrbindP => e1' /hrec he1 <- /= ?? /he1 -> /= ->.
  + move=> o e1 hrec1 e2 hrec2 e'. 
    by t_xrbindP => e1' /hrec1 he1 e2' /hrec2 he2 <- /= ?? /he1 -> /= ? /he2 -> /=.
  + move=> op es hrec e'; t_xrbindP => es' hes' <- ?? h1 h2 /=.
    by have := expand_esP_aux h hes' hrec h1; rewrite /sem_pexprs => ->.
  move=> t b hrecb e1 hrec1 e2 hrec2 e'.
  t_xrbindP => b' /hrecb hb e1' /hrec1 he1 e2'  /hrec2 he2 <- /=.
  by move=> ??? /hb -> /= -> /= ?? /he1 -> /= -> ?? /he2 -> /= -> /= <-.
Qed.

Lemma expand_esP (s1 s2 : estate) : 
  eq_alloc m s1 s2 ->
  forall es1 es2, expand_es m es1 = ok es2 -> 
  forall vs, sem_pexprs gd s1 es1 = ok vs ->
             sem_pexprs gd s2 es2 = ok vs.
Proof. by move=> h es1 es2 hex; apply (expand_esP_aux h hex) => e _; apply expand_eP. Qed.

Lemma eq_alloc_write_var s1 s2 (x: var_i) v s1':
   eq_alloc m s1 s2 ->
   Sv.mem x (svars m) ->
   write_var x v s1 = ok s1' ->
   ∃ s2' : estate, write_var x v s2 = ok s2' ∧ eq_alloc m s1' s2'.
Proof.
  move=> h; case: (h) => -[heq ha] hmem /=.
  move=> /Sv_memP hin hw.
  have [vm2 [heq2 hw2]]:= write_var_eq_on hw heq.
  exists (with_vm s1' vm2); split.
  + have -> // : s2 = with_vm s1 (evm s2) by case: (s2) hmem => ?? /= <-.
  split => //; split; first by apply: eq_onI heq2; SvD.fsetdec.
  move=> x' ai i xi hai hxi.
  have [/negP /Sv_memP hnx' /(_ _ _ hxi) [] /negP /Sv_memP hnxi _]:= valid hai.
  rewrite /eval_array /= /on_arr_var /get_var.
  rewrite -(vrvP_var hw); last by SvD.fsetdec.
  have /= <- := (vrvP_var hw2); last by SvD.fsetdec.
  by apply: ha.
Qed.

Lemma eq_alloc_write_vars s1 s2 (xs: list var_i) vs s1':
   eq_alloc m s1 s2 ->
   all (fun (x:var_i) => Sv.mem x (svars m)) xs ->
   write_vars xs vs s1 = ok s1' ->
   ∃ s2' : estate, write_vars xs vs s2 = ok s2' ∧ eq_alloc m s1' s2'.
Proof.
  elim: xs vs s1 s2 s1' => /= [ | x xs hrec] [ | v vs] // s1 s2 s1' heqa.
  + by move=> _ [<-]; exists s2.
  move=> /andP [hx hall]; t_xrbindP => s1'' /(eq_alloc_write_var heqa hx) [s2'' [hw heqa']].
  by move=> /(hrec _ _ _ _ heqa' hall) [s2' [hws ?]]; exists s2'; rewrite hw /= hws /=.
Qed.

Lemma expand_lvP (s1 s2 : estate) : 
  eq_alloc m s1 s2 ->
  forall x1 x2, expand_lv m x1 = ok x2 ->
  forall v s1',
     write_lval gd x1 v s1 = ok s1' ->
     exists s2', write_lval gd x2 v s2 = ok s2' /\ eq_alloc m s1' s2'.
Proof.
  move=> h; case: (h) => -[heq ha] hmem [] /=.
  + move=> ii ty _ [<-] /= ?? /dup [] /write_noneP [->] _ hn.
    by exists s2; split => //; apply: uincl_write_none hn.
  + by move=> x; t_xrbindP => _ _ /assertP ? <- /= v1 s1'; apply eq_alloc_write_var.
  + move=> ws x e x2; t_xrbindP => _ /assertP hin e' he <- v s1' vx p /=.
    rewrite (check_var_get hin h) => -> /= -> /= pe ve.
    move=> /(expand_eP h he) -> /= -> /= ? -> /= mem.
    by rewrite -hmem => -> /= <-; exists (with_mem s2 mem).
  + move=> aa ws x e x2.
    case: ifPn => [hin | hnin].
    + t_xrbindP => e' he <- v s1' /=.
      apply on_arr_varP => n t hty.
      rewrite (check_var_get hin h) => -> /=.
      t_xrbindP => i vi /(expand_eP h he) -> /= -> /= ? -> /= t' -> /= vm' hs <-.
      rewrite -/(write_var x (Varr t') s2).
      have hw : write_var x (Varr t') s1 = ok (with_vm s1 vm') by rewrite /write_var hs.
      by apply (eq_alloc_write_var h hin hw).
    case hai: Mvar.get => [ai | //].
    case: is_constP => // i ; t_xrbindP => _ /assertP /eqP <- _ /assertP /eqP ->.
    case hxi: Mi.get => [xi | //] [<-] v s1'.
    apply on_arr_varP => n t hty hget /=.
    t_xrbindP => w hvw t' ht' vm' hs <-. 
    have [_ /(_ _ _ hxi)]:= valid hai.
    case: xi hxi => txi nxi; set xi := {| vname := _ |} => hxi [] hnxi /= [] /eqP ? hd; subst txi.
    rewrite /write_var /set_var /= /on_vu (to_word_to_pword hvw) /=.
    eexists; split; first by eauto.
    split => //; split.
    + apply: (eq_onT (vm2:= evm s1)).
      + apply eq_onS.
        apply (@disjoint_eq_on gd _ x _ _ (Varr t')).
        + by rewrite vrv_var; move/Sv_memP : hnin => hnin; apply/Sv.is_empty_spec; SvD.fsetdec.
        by rewrite /= /write_var hs.
      apply: (eq_onT heq); apply (@disjoint_eq_on gd _ (VarI xi x.(v_info)) _ _ (Vword w)).
      + by rewrite vrv_var; move/negP/Sv_memP:hnxi => hnxi /=; apply/Sv.is_empty_spec; SvD.fsetdec.
      by rewrite /= /write_var /set_var /= /on_vu (sumbool_of_boolET (cmp_le_refl _)).
    move=> x' ai' i' xi'.
    rewrite /eval_array/on_arr_var /= (get_var_set_var _ hs).
    case: ((v_var x) =P x') => [<- | hxx'].
    + rewrite hai => -[<-].
      rewrite hty /pof_val /= WArray.castK /=.
      rewrite (WArray.setP _ ht').
      case: (i =P i') => [<- /= | hii' hxi'].
      + by rewrite hxi => -[<-]; rewrite Fv.setP_eq /=.
      rewrite Fv.setP_neq.
      + by have := ha _ _ _ _ hai hxi'; rewrite /eval_array /on_arr_var hget.
      by apply (hd _ _ _ _ hai hxi'); auto.
    move=> hai' hxi'; rewrite Fv.setP_neq; first by apply: ha hai' hxi'.
    by apply (hd _ _ _ _ hai' hxi'); auto.
  move=> aa ws len x e x2; t_xrbindP => _ /assertP hin e' he <- /= v s1'.
  apply on_arr_varP => n t hty.
  rewrite (check_var_get hin h) => -> /=.
  t_xrbindP => i vi /(expand_eP h he) -> /= -> /= ? -> /= t' -> /= vm' hs <-.
  rewrite -/(write_var x (Varr t') s2).
  have hw : write_var x (Varr t') s1 = ok (with_vm s1 vm') by rewrite /write_var hs.
  by apply (eq_alloc_write_var h hin hw).
Qed.

Lemma expand_lvsP (s1 s2 : estate) : 
  eq_alloc m s1 s2 ->
  forall x1 x2, expand_lvs m x1 = ok x2 ->
  forall vs s1',
     write_lvals gd s1 x1 vs = ok s1' ->
     exists s2', write_lvals gd s2 x2 vs = ok s2' /\ eq_alloc m s1' s2'.
Proof.
  move=> heqa x1 x2 hex; elim: x1 x2 hex s1 s2 heqa => /=.
  + by move=> ? [<-] s1 s2 ? [ | //] ? [<-]; exists s2.
  move=> x1 xs1 hrec ?; t_xrbindP => x2 hx xs2 hxs <- s1 s2 heqa [//|v vs] s1'.
  t_xrbindP => s1'' /(expand_lvP heqa hx) [s2'' [hw heqa']] /(hrec _ hxs _ _ heqa') [s2' [??]].
  by exists s2'; split => //=; rewrite hw.
Qed.

End Expr.

Hypothesis Hcomp : expand_prog fi p1 = ok p2.

Lemma eq_globs : p_globs p2 = gd.
Proof. by move: Hcomp; rewrite /expand_prog; t_xrbindP => ?? <-. Qed.

Lemma all_checked fn fd1 :
  get_fundef (p_funcs p1) fn = Some fd1 ->
  exists fd2, get_fundef (p_funcs p2) fn = Some fd2 /\ 
              expand_fd fi fn fd1 = ok fd2.
Proof.
  move: Hcomp; case: p1 => pf1 pg pe.
  rewrite /expand_prog; t_xrbindP => /= pf2 hpf2 <- hfd1.
  have [fd2 hex hfd2]:= get_map_cfprog_name_gen hpf2 hfd1.
  by exists fd2.
Qed.

Local Notation ev := tt.

Let Pi_r s1 (i1:instr_r) s2:=
  forall ii m ii' i2 s1', 
    wf_t m -> eq_alloc m s1 s1' ->
    expand_i m (MkI ii i1) = ok (MkI ii' i2) ->
  exists s2', eq_alloc m s2 s2' /\ sem_i p2 ev s1' i2 s2'.

Let Pi s1 (i1:instr) s2:=
  forall m i2 s1', 
    wf_t m -> eq_alloc m s1 s1' ->
    expand_i m i1 = ok i2 ->
  exists s2', eq_alloc m s2 s2' /\ sem_I p2 ev s1' i2 s2'.

Let Pc s1 (c1:cmd) s2 :=
  forall m c2 s1', 
    wf_t m -> eq_alloc m s1 s1' ->
    mapM (expand_i m) c1 = ok c2 ->
  exists s2', eq_alloc m s2 s2' /\ sem p2 ev s1' c2 s2'.

Let Pfor (i1:var_i) vs s1 c1 s2 :=
  forall m c2 s1', 
    wf_t m -> eq_alloc m s1 s1' -> Sv.mem i1 m.(svars) ->
    mapM (expand_i m) c1 = ok c2 ->
  exists s2', eq_alloc m s2 s2' /\ sem_for p2 ev i1 vs s1' c2 s2'.

Let Pfun m fn vargs m' vres :=
  sem_call p2 ev m fn vargs m' vres.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof.
  move=> s1 m c2 s1' hwf heqa /= [<-]; exists s1'; split => //; constructor.
Qed.

Local Lemma Hcons : sem_Ind_cons p1 ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ Hi _ Hc m c2 s1' hwf heqa1 /=.
  t_xrbindP => i' /Hi -/(_ _ hwf heqa1) [s2' [heqa2 hsemi]].
  move=> c' /Hc -/(_ _ hwf heqa2) [s3' [heqa3 hsemc]] <-; exists s3'; split => //.
  econstructor; eauto.
Qed.

Local Lemma HmkI : sem_Ind_mkI p1 ev Pi_r Pi.
Proof.
  move=> ii i s1 s2 _ Hi m [ii' i2] s1' hwf heqa /Hi -/(_ _ hwf heqa) [s2' [heqa' hsemi]].
  exists s2'; split => //; constructor.
Qed.

Local Lemma Hassgn : sem_Ind_assgn p1 Pi_r.
Proof.
  move => s1 s2 x tag ty e v v' hse htr hw ii m ii' i2 s1' hwf heqa /=.
  t_xrbindP => x' hx e' he _ <-.
  have ? := expand_eP hwf heqa he hse.
  have [s2' [hw' heqa']] := expand_lvP hwf heqa hx hw.
  exists s2'; split => //;econstructor; rewrite ?eq_globs; eauto.
Qed.

Local Lemma Hopn : sem_Ind_opn p1 Pi_r.
Proof.
  move => s1 s2 t o xs es; rewrite /sem_sopn; t_xrbindP => vs ves hse ho hws.
  move=> ii m ii' e2 s1' hwf heqa /=; t_xrbindP => xs' hxs es' hes _ <-.
  have := expand_esP hwf heqa hes hse.
  have := expand_lvsP hwf heqa hxs hws.
  rewrite -eq_globs => -[s2' [hws' ?]] hse'; exists s2'; split => //.
  by constructor; rewrite /sem_sopn hse' /= ho.
Qed.

Local Lemma Hif_true : sem_Ind_if_true p1 ev Pc Pi_r.
Proof.
  move => s1 s2 e c1 c2 hse hs hrec ii m ii' ? s1' hwf  heqa /=.
  t_xrbindP => e' he c1' hc1 c2' hc2 _ <-.
  have := expand_eP hwf heqa he hse; rewrite -eq_globs => hse'.
  have [s2' [??]] := hrec _ _ _ hwf heqa hc1.
  by exists s2'; split => //; apply Eif_true.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p1 ev Pc Pi_r.
Proof.
  move => s1 s2 e c1 c2 hse hs hrec ii m ii' ? s1' hwf  heqa /=.
  t_xrbindP => e' he c1' hc1 c2' hc2 _ <-.
  have := expand_eP hwf heqa he hse; rewrite -eq_globs => hse'.
  have [s2' [??]] := hrec _ _ _ hwf heqa hc2.
  by exists s2'; split => //; apply Eif_false.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p1 ev Pc Pi_r.
Proof.
  move => s1 s2 s3 s4 a c1 e c2 _ hrec1 hse _ hrec2 _ hrecw ii m ii' ? s1' hwf heqa /=.
  t_xrbindP => e' he c1' hc1 c2' hc2 hii <-.
  have [sc1 [heqa1 hs1]]:= hrec1 _ _ _ hwf heqa hc1.
  have := expand_eP hwf heqa1 he hse; rewrite -eq_globs => hse'.
  have [sc2 [heqa2 hs2]]:= hrec2 _ _ _ hwf heqa1 hc2.
  have [| s2' [? hsw]]:= hrecw ii m ii' (Cwhile a c1' e' c2') _ hwf heqa2.
  + by rewrite /= he hc1 hc2 hii.
  exists s2'; split => //; apply: Ewhile_true hsw; eauto.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p1 ev Pc Pi_r.
Proof.
  move => s1 s2 a c e c' _ hrec1 hse ii m ii' ? s1' hwf heqa /=.
  t_xrbindP => e' he c1' hc1 c2' hc2 hii <-.
  have [s2' [heqa1 hs1]]:= hrec1 _ _ _ hwf heqa hc1.
  have := expand_eP hwf heqa1 he hse; rewrite -eq_globs => hse'.
  exists s2'; split => //; apply: Ewhile_false; eauto.
Qed.

Local Lemma Hfor : sem_Ind_for p1 ev Pi_r Pfor.
Proof.
  move => s1 s2 i d lo hi c vlo vhi hslo hshi _ hfor ii m ii' ? s1' hwf heqa /=.
  t_xrbindP => _ /assertP hin lo' hlo hi' hhi c' hc ? <-.
  have := expand_eP hwf heqa hlo hslo.
  have := expand_eP hwf heqa hhi hshi; rewrite -eq_globs => hshi' hslo'.
  have [s2' [??]]:= hfor _ _ _ hwf heqa hin hc.
  exists s2'; split => //; econstructor; eauto.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof.
  move=> s i c i2 c' s1' hwf heqa _; exists s1'; split => //; constructor.
Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p1 ev Pc Pfor.
Proof.
  move=> s1 s1w s2 s3 i w ws c Hwi _ Hc _ Hfor m c' s1' hwf heqa hin hc.
  have [s1w' [? heqa1']]:= eq_alloc_write_var hwf heqa hin Hwi.
  have [s2' [heqa2 ?]]:= Hc _ _ _ hwf heqa1' hc.
  have [s3' [??]]:= Hfor _ _ _ hwf heqa2 hin hc.
  exists s3'; split => //; econstructor; eauto.
Qed.

Local Lemma Hcall : sem_Ind_call p1 ev Pi_r Pfun.
Proof.
  move=> s1 m2 s2 ii xs fn args vargs vs Hes Hsc Hfun Hw ii1 m ii2 i2 s1' hwf heqa /=.
  t_xrbindP => xs' hxs es' hes ? <-.
  have := expand_esP hwf heqa hes Hes.
  have heqa': eq_alloc m (with_mem s1 m2) (with_mem s1' m2) by case: heqa.
  have [s2' []]:= expand_lvsP hwf heqa' hxs Hw.
  rewrite -eq_globs => ???; exists s2'; split => //; econstructor; eauto.
  by case: heqa => _ <-.
Qed.

Lemma wf_init_map ffi m : init_map ffi = ok m -> wf_t m.
Proof.
  rewrite /init_map; t_xrbindP.
  set svars_ := of_list _.
  pose wf_st := 
    fun (svm: Sv.t * Mvar.t array_info) =>
      [/\ wf_t {| svars := svars_; sarrs := svm.2 |}, 
          Sv.Subset svars_ svm.1 &
          (forall  x ai i xi, 
             Mvar.get svm.2 x = Some ai ->
             Mi.get (ai_elems ai) i = Some xi ->
             Sv.In xi svm.1)].
  suff : forall l svm svm', wf_st svm -> foldM init_array_info svm l = ok svm' -> wf_st svm'.
  + move=> h svm' /h []; first by split => //=.
    by move=> ? _ _ <-.
  elim => /= [ ??? [<-] // | vi vis hrec svm svm' hwf].
  t_xrbindP => svm1 heq; apply: hrec.
  move: heq; rewrite /init_array_info.
  case: svm hwf => sv1 m1 hwf; t_xrbindP => _ /assertP /Sv_memP hin [[sv2 m2] b].
  set ty := sword _.
  pose wf_sm := 
    fun (svmp : Sv.t * Mi.t var * Z) =>
      let '(sv,mi,_) := svmp in
        Sv.Subset sv1 sv /\
        (forall i xi, Mi.get mi i = Some xi ->
          [/\ ~Sv.In xi sv1, Sv.In xi sv, 
              vtype xi == ty &
              forall j xj, i <> j -> Mi.get mi j = Some xj -> xi <> xj]).
  suff : forall ids svmp svmp', 
     wf_sm svmp -> 
     foldM (init_elems ty) svmp ids = ok svmp' -> wf_sm svmp'.
  + move=> h /h{h}h [<-].           
    have /h{h}[hsub hmi] : wf_sm (sv1, Mi.empty var, 0%Z) by split.
    case: hwf => hwf hsub' hget; split => //.
    + move=> x ai /=; rewrite Mvar.setP; case: eqP.
      + move=> <- [<-]; split.
        + by apply/negP/Sv_memP; SvD.fsetdec.
        move=> i xi /= hgeti; have [/= hnin heqt hj] := hmi _ _ hgeti; split.
        + by apply/negP/Sv_memP; SvD.fsetdec.
        split => // x' ai' i' xi'. 
        rewrite Mvar.setP; case: eqP => [<- [<-] /= hgeti' hd| hne].
        + by case: (hmi _ _ hgeti) => ??? h; apply/eqP/(h i') => //; case: hd.
        move=> h1 h2 ?; have /= ?:= hget _ _ _ _ h1 h2; apply /eqP => heq.
        by apply hnin; rewrite heq.
      move=> /eqP hne /dup[] hgetx /hwf /= [? hgeti]; split => //.
      move=> i xi /dup[] hi /hgeti [?] [? h]; split => //; split => //.
      move=> x' ai' i' xi'; rewrite Mvar.setP; case: eqP.
      + move=> ? [<-]; subst x' => /= hi' ?.
        have /= ? := hget _ _ _ _ hgetx hi.
        by have [hnin ???]:= hmi _ _ hi'; apply/eqP => heq; apply hnin; rewrite -heq.
      by move=> ? hgetx'; have [? /(_ _ _ hi) [?] [?] /= ]:= hwf _ _ hgetx; apply.
    + by rewrite /=; SvD.fsetdec.
    move=> /= x ai i xi; rewrite Mvar.setP; case: eqP.
    + by move=> ? [<-]; subst x => /hmi [].
    move=> ? h1 h2; have /= := hget _ _ _ _ h1 h2; SvD.fsetdec.
  elim => /= [???[<-] // | id ids hrec] [[sv mi] i] svmp' hwfsm.
  t_xrbindP => svmp'' hsvmp''; apply hrec; move: hsvmp''.
  rewrite /init_elems; t_xrbindP => _ /assertP /Sv_memP hnin <-.
  case: hwfsm => h1 h2; split; first by SvD.fsetdec.
  move=> i1 xi1; rewrite Mi.setP; case: eqP => ?.
  + subst i1 => -[<-]; split => //; try SvD.fsetdec.
    move=> j xj hji; rewrite Mi.setP_neq; last by apply/eqP.
    by move=> /h2 [] hj1 hj2 _ _ heq; apply hnin; rewrite heq.
  move=> /h2 [] hi1 hi2 hi3 hi4; split => //; first by SvD.fsetdec.
  move=> j xj ji; rewrite Mi.setP; case: eqP => _; last by apply hi4. 
  by move=> [<-] heq; apply hnin; rewrite -heq.
Qed.

Local Lemma Hproc : sem_Ind_proc p1 ev Pc Pfun.
Proof.
  move=> m1 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hget Hca [?] Hw _ Hc Hres Hcr ?; subst s0 m2.
  have [fd2 [Hget2 /=] {Hget}]:= all_checked Hget.
  rewrite /expand_fd; t_xrbindP=> m.
  case: f Hca Hw Hc Hres Hcr => /=.
  move=> finfo ftyin fparams fbody ftyout fres fextra.
  set fd := {| f_info := finfo |} => Hca Hw Hc Hres Hcr hinit.
  t_xrbindP => _ /assertP hparams _ /assertP hres body' hbody hfd2; rewrite /Pfun.
  have hwf := wf_init_map hinit.
  have heqa : eq_alloc m {| emem := m1; evm := vmap0 |} {| emem := m1; evm := vmap0 |}.
  + split => //; split => //.
    move=> x ai i xi hai hxi.
    rewrite /eval_array /= /get_var !Fv.get0.
    have [_ /(_ _ _ hxi) [_] []/eqP -> _ /=]:= hwf _ _ hai.
    case: (vtype x) => //= p.
    case heq : (WArray.get AAscale (ai_ty ai) (WArray.empty p) i) => [w | ] //=.
    have []:= WArray.get_bound heq; rewrite /mk_scale => ???.
    have h : ((0 <= 0%N)%Z ∧ (0%N < wsize_size (ai_ty ai)))%Z.
    + by move=> /=; have := wsize_size_pos (ai_ty ai); Psatz.lia.
    have [_ /(_ 0 h)] := read_read8 heq.
    by rewrite WArray.get0 //= WArray.addE; have := wsize_size_pos (ai_ty ai); Psatz.lia.
  have [s1' [hparams' heqa1]] := eq_alloc_write_vars hwf heqa hparams Hw.
  have [s2' [heqa2 hsem]]:= Hc _ _ _ hwf heqa1 hbody.
  rewrite (check_var_gets hres heqa2) in Hres.
  by subst fd2; econstructor => /=; eauto; case: heqa2.
Qed.

Lemma expand_callP f mem mem' va vr:
  sem_call p1 ev mem f va mem' vr -> sem_call p2 ev mem f va mem' vr.
Proof.
  apply (@sem_call_Ind _ _ _ p1 ev Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
          Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
Qed.

End Section.
