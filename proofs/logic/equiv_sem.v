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
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.

Require Import strings word utils.
Require Import type var expr.
Require Import low_memory sem Ssem Ssem_props.
Import ZArith.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
(*Fixpoint st2sst_ty {t : stype} :=
  match t return sem_t t -> ssem_t t with
  | sword     => fun v => v
  | sint      => fun v => v
  | sbool     => fun v => v
  | sarr n    => fun v => 
       (fun i => 
          match @Array.get _ n v i return word with
          | Ok w => w
          | _      => n2w 0
          end)
  end.
*)
(* -------------------------------------------------------------------- *)
Definition sval_uincl (t:stype) : sem_t t -> ssem_t t -> Prop :=
  match t as t0 return sem_t t0 -> ssem_t t0 -> Prop with
  | sbool     => fun b1 b2 => b1 = b2
  | sint      => fun i1 i2 => i1 = i2
  | sword _   => fun w1 w2 => w1 = w2
  | sarr sz n => fun (t1:Array.array n (word sz)) (t2:FArray.array (word sz)) =>
      (forall i v, Array.get t1 i = ok v -> FArray.get t2 i = v)
  end.

Definition seval_uincl (t:stype) (v1: exec (sem_t t)) (v2: ssem_t t) := 
  match v1 with 
  | Ok  v1 => sval_uincl v1 v2
  | Error _ => True
  end.

Definition svm_uincl (vm:vmap) (svm:svmap) :=
  forall x, seval_uincl (vm.[x])%vmap (svm.[x])%vmap.

(* -------------------------------------------------------------------- *)
Definition sestate_uincl (s: estate) (ss: sestate) :=
  mem_to_smem s.(emem) = ss.(semem) /\ (svm_uincl s.(evm) ss.(sevm)).

Definition svalue_uincl (v: value) (sv: svalue) :=
  match v, sv with
  | Vbool b1, SVbool b2 => b1 = b2
  | Vint n1, SVint n2   => n1 = n2
  | Varr s _ t1, SVarr s' t2 =>
    if s == s' then forall i v, Array.get t1 i = ok v ->  truncate_word s (FArray.get t2 i) = ok v else False
  | Vword s w1, SVword s' w2  => if s == s' then truncate_word s w2 = ok w1 else False
  | Vundef ty, _ => sstype_of_stype ty = sval_sstype sv
  | _, _ => False
  end.

Lemma to_int_inv x i :
  to_int x = ok i →
  x = i.
Proof.
  case: x => // ? H.
    apply ok_inj in H; congruence.
  elim (@of_val_undef_ok sint _ _ H).
Qed.


Lemma to_word_inv s x (w:word s) :
  to_word s x = ok w →
  exists  {s'} (w': word s'), x = Vword w' /\ truncate_word s w' = ok w.
Proof.
  case: x => //;last by  move => st; rewrite /to_word; case: st => //=.
  move => s' w'. rewrite /to_word /truncate_word.
  elim le_ss' : cmp_le => //= eq_ww';apply ok_inj in eq_ww'.
  by exists s'; exists  w';split => //=; rewrite le_ss' eq_ww'.
Qed.

Lemma sto_word_inv s x (w:word s) :
  sto_word s x = ok w →
  exists  {s'} (w': word s'), x = SVword w' /\ truncate_word s w' = ok w.
Proof.
  case: x => // s' w'. rewrite /sto_word /truncate_word.
  elim le_ss' : cmp_le => //= eq_ww';apply ok_inj in eq_ww'.
  by exists s'; exists  w';split => //=; rewrite le_ss' eq_ww'.
Qed.

Lemma to_bool_inv x b :
  to_bool x = ok b →
  x = b.
Proof.
  case: x => // ? H.
  apply ok_inj in H; congruence.
  elim (@of_val_undef_ok sbool _ _ H).
Qed.
 

Require psem.

Definition sstype_stype_incl sst st :=
  match sst, st with
  |ssint, sint => true
  |ssbool, sbool => true
  |ssword s, sword s' => (s' <= s)%CMP
  |ssarr s, sarr s' _ => s == s'
  |_, _ => false
  end.

Lemma to_arr_inv s n a v :
  of_val (sarr s n) (@Varr s n a) = ok v -> a = v.
Proof. by rewrite /of_val /to_arr (eq_dec_refl wsize_eq_dec) pos_dec_n_n;simpl; apply ok_inj.
Qed.

Lemma of_sval_uincl v v' t z:
  svalue_uincl v v' ->
  of_val t v = ok z ->
  exists z', of_sval t v' = ok z' /\ sval_uincl z z' ∧ sstype_stype_incl (sval_sstype v') t. (* Subtype ?*)
Proof.
  case: v  => [b | n  | s n a | s  w | ty];
  case: v' => [b'| n' | s' a' | s' w'] //=;
  try (by case: t z=> //= z -> []->; exists z);
  try (move=> _ H; elim (of_val_undef_ok H); fail); last first.

  case: ifP => //= /eqP eq_ss' val_zw' H; subst s'.
  rewrite psem.truncate_word_u in val_zw'; apply ok_inj in val_zw'; subst w'.
  have H' := (of_vword H); move:H';  move => [s'' [le_ss' H']]; subst t.
  move:H;  rewrite /of_val; simpl.
  exists z; split => //=.


  case: (s =P s') => //= eq_ss';subst s'.
  move => //= H2 H. rewrite /of_sval. 
  have H' := (of_varr H). subst t; simpl; simpl in z.
  exists a'. split;last split => //=.
  rewrite eq_dec_refl; congr ok.
  apply to_arr_inv in H; subst z.
  move => i w H; apply H2 in H;rewrite psem.truncate_word_u in H.
  by apply ok_inj in H.
Qed.

Lemma svalue_uincl_int ve ve' z :
  svalue_uincl ve ve' -> to_int ve = ok z -> ve = z /\ ve' = z.
Proof.
  move=> h t; case: (@of_sval_uincl ve ve' sint z h t) => /= z' [t' q].
  apply sto_int_inv in t'; apply to_int_inv in t. intuition congruence.
Qed.


Lemma svalue_uincl_word ve ve' sz w :
  svalue_uincl ve ve' -> to_word sz ve = ok w ->
  exists sz', exists (w' : word sz'), exists sz'', exists (w'' : word sz''),
          truncate_word sz w' = ok w /\ ve = (Vword w') /\ ve' = (SVword w'').
Proof.
  move=> h t; case: (@of_sval_uincl ve ve' (sword sz) w h t) => /= z' [t' [sub rel]].
  subst z'.
  have h' := ((@to_word_inv sz ve w) t).
  move:h' => [sz' [w' [eq_vew' trunc_ww']]].
  have h' := ((@sto_word_inv sz ve' w) t').
  move:h' => [sz'' [w'' [eq_ve'w'' trunc_ww'']]].
  exists sz'. exists w'. exists sz''. exists w''.
  
  split => //=; split => //=.

  (*have h' := ((@to_word_inv sz ve w) t).
  move:h' => [sz'' [w'' [eq_vew'' trunc_ww'']]].

  have:sz' = sz''.
  move:h. rewrite /svalue_uincl eq_ve'w' eq_vew''.
  by case:ifP => //= /eqP . 
  move => eq_sz'sz''. subst sz''.
  rewrite eq_vew''.

  
  rewrite cmp_le_refl in h' => //.
  apply to_word_inv in t.
  move:t =>  [sz' [w' [eq_vw' trunc_w']]].
  rewrite eq_vw'.
  exists sz'. exists w'. split => //=;split => //=.
  Check sto_word_inv.
  apply to_word_inv in t. intuition congruence.*)
Qed.

(*Lemma svalue_uincl_word ve ve' sz w :
  svalue_uincl ve ve' -> to_word sz ve = ok w ->
  exists sz', exists (w' : word sz'),truncate_word sz w' = ok w /\ ve = (Vword w') /\ ve' = (SVword w').
Proof.
  move=> h t; case: (@of_sval_uincl ve ve' (sword sz) w h t) => /= z' [t' [sub rel]].
  subst z'.
  have h' := @sto_word_inv sz w sz w.
  rewrite cmp_le_refl in h' => //.
  apply to_word_inv in t.
  move:t =>  [sz' [w' [eq_vw' trunc_w']]].
  rewrite eq_vw'.
  exists sz'. exists w'. split => //=;split => //=.
  Check sto_word_inv.
  apply to_word_inv in t. intuition congruence.
Qed.*)

Lemma svalue_uincl_bool ve ve' b :
  svalue_uincl ve ve' -> to_bool ve = ok b -> ve = b /\ ve' = b.
Proof.
  move=> h t; case: (@of_sval_uincl ve ve' sbool b h t) => /= z' [t' q].
  apply sto_bool_inv in t'; apply to_bool_inv in t. intuition congruence.
Qed.

Lemma sget_var_uincl x vm1 vm2 v1:
  svm_uincl vm1 vm2 ->
  get_var vm1 x = ok v1 ->
  svalue_uincl v1 (sget_var vm2 x).
Proof.
move=> /(_ x); rewrite /seval_uincl; move=> H P; move: P H.
apply: on_vuP => [ y | ] ->.
case: x y => vi vt /= z <- /=.
case: vi z => //=.
move => s n z H;case:ifP => [_ | ] //=;last by move => /eqP.
by move => i w H'; apply H in H'; rewrite H' psem.truncate_word_u.
by move => s w H; case:ifP;  move => /eqP //= _; rewrite -H psem.truncate_word_u.
move=> H _; apply ok_inj in H; subst.
symmetry.
exact: sval_sstype_to_sval.
Qed.
(*
Lemma sget_vars_uincl (xs:seq var_i) vm1 vm2 vs1:
  svm_uincl vm1 vm2 ->
  mapM (fun x => get_var vm1 (v_var x)) xs = ok vs1 ->
  List.Forall2 svalue_uincl
      vs1 [seq sget_var vm2 (v_var x) | x <- xs].
Proof.
  move=> Hvm;elim: xs vs1=> /= [vs1 [] <- //|x xs IH vs1].
  apply: rbindP=> y /= Hy.
  apply: rbindP=> z /= Hz [] <-.
  apply: List.Forall2_cons.
  apply: sget_var_uincl=> //.
  by apply: IH.
Qed.

Lemma svuincl_sem_op2_b o ve1 ve1' ve2 ve2' v1 :
  svalue_uincl ve1 ve1' -> svalue_uincl ve2 ve2' -> sem_op2_b o ve1 ve2 = ok v1 ->
  exists v2 : svalue, ssem_op2_b o ve1' ve2' = ok v2 /\ svalue_uincl v1 v2.
Proof.
  rewrite /sem_op2_b /= /mk_sem_sop2 => Hvu1 Hvu2.
  apply: rbindP => z1 /(svalue_uincl_bool Hvu1) [] _ ->.
  apply: rbindP => z2 /(svalue_uincl_bool Hvu2) [] _ -> [] <- /=.
  by exists (o z1 z2).
Qed.

Lemma svuincl_sem_op2_i o ve1 ve1' ve2 ve2' v1 :
  svalue_uincl ve1 ve1' -> svalue_uincl ve2 ve2' -> sem_op2_i o ve1 ve2 = ok v1 ->
  exists v2 : svalue, ssem_op2_i o ve1' ve2' = ok v2 /\ svalue_uincl v1 v2.
Proof.
  rewrite /sem_op2_i /= /mk_sem_sop2 => Hvu1 Hvu2.
  apply: rbindP => z1 /(svalue_uincl_int Hvu1) [] _ ->.
  apply: rbindP => z2 /(svalue_uincl_int Hvu2) [] _ -> [] <- /=.
  by exists (o z1 z2).
Qed.

Lemma svuincl_sem_op2_w o ve1 ve1' ve2 ve2' v1 :
  svalue_uincl ve1 ve1' -> svalue_uincl ve2 ve2' -> sem_op2_w o ve1 ve2 = ok v1 ->
  exists v2 : svalue, ssem_op2_w o ve1' ve2' = ok v2 /\ svalue_uincl v1 v2.
Proof.
  rewrite /sem_op2_i /= /mk_sem_sop2 => Hvu1 Hvu2.
  apply: rbindP => z1 /(svalue_uincl_word Hvu1) [] _ ->.
  apply: rbindP => z2 /(svalue_uincl_word Hvu2) [] _ -> [] <- /=.
  by exists (SVword (o z1 z2)).
Qed.

Lemma svuincl_sem_op2_ib o ve1 ve1' ve2 ve2' v1 :
  svalue_uincl ve1 ve1' -> svalue_uincl ve2 ve2' -> sem_op2_ib o ve1 ve2 = ok v1 ->
  exists v2 : svalue, ssem_op2_ib o ve1' ve2' = ok v2 /\ svalue_uincl v1 v2.
Proof.
  rewrite /sem_op2_ib /= /mk_sem_sop2 => Hvu1 Hvu2.
  apply: rbindP => z1 /(svalue_uincl_int Hvu1) [] _ ->.
  apply: rbindP => z2 /(svalue_uincl_int Hvu2) [] _ -> [] <- /=.
  by exists (o z1 z2).
Qed.

Lemma svuincl_sem_op2_wb o ve1 ve1' ve2 ve2' v1 :
  svalue_uincl ve1 ve1' -> svalue_uincl ve2 ve2' -> sem_op2_wb o ve1 ve2 = ok v1 ->
  exists v2 : svalue, ssem_op2_wb o ve1' ve2' = ok v2 /\ svalue_uincl v1 v2.
Proof.
  rewrite /sem_op2_ib /= /mk_sem_sop2 => Hvu1 Hvu2.
  apply: rbindP => z1 /(svalue_uincl_word Hvu1) [] _ ->.
  apply: rbindP => z2 /(svalue_uincl_word Hvu2) [] _ -> [] <- /=.
  by exists (o z1 z2).
Qed.

Lemma svuincl_sem_op1_b o w w' r :
  svalue_uincl w w' → sem_op1_b o w = ok r →
  ∃ r' : svalue, ssem_op1_b o w' = ok r' ∧ svalue_uincl r r'.
Proof.
  move=> H.
  apply: rbindP => b Hb; apply to_bool_inv in Hb; subst.
  move=> Hr; apply ok_inj in Hr; subst.
  case: w' H => // b' <- {b'}.
  by exists (o b).
Qed.

Lemma svuincl_sem_op1_w o w w' r :
  svalue_uincl w w' → sem_op1_w o w = ok r →
  ∃ r' : svalue, ssem_op1_w o w' = ok r' ∧ svalue_uincl r r'.
Proof.
  move=> H.
  apply: rbindP => b Hb; apply to_word_inv in Hb; subst.
  move=> Hr; apply ok_inj in Hr; subst.
  case: w' H => // b' <- {b'}.
  by exists (SVword (o b)).
Qed.

Lemma svuincl_sem_op1_a w w' r :
  svalue_uincl w w' → sem_arr_init w = ok r →
  ∃ r' : svalue, ssem_arr_init w' = ok r' ∧ svalue_uincl r r'.
Proof.
  move=> H.
  apply: rbindP => b Hb; apply to_int_inv in Hb; subst.
  case: b H => // b H Hr; apply ok_inj in Hr; subst.
  case: w' H => // b' <- {b'}.
  eexists. split. reflexivity.
  move=> i v h; elim (Array.getP_empty h).
Qed.

Lemma svuincl_sem_op1 o w w' r :
  svalue_uincl w w' → sem_sop1 o w = ok r →
  ∃ r' : svalue, ssem_sop1 o w' = ok r' ∧ svalue_uincl r r'.
Proof.
  case: o => /=; eauto using svuincl_sem_op1_b, svuincl_sem_op1_w, svuincl_sem_op1_a.
Qed.

Section FORALL2.
  Import List.
  Context (A B: Type) (P: A → B → Prop).

  Definition forall2_inv_left ma mb :
    Forall2 P ma mb →
    match ma with
    | [::] => mb = [::]
    | a :: ma' => ∃ b mb', mb = b :: mb' ∧ P a b ∧ Forall2 P ma' mb'
  end.
  Proof.
    intros h.
    set (d ma mb :=
      match ma with [::] => mb = [::]
      | a :: ma' => ∃ b mb', mb = b :: mb' ∧ P a b ∧ Forall2 P ma' mb' end).
    change (d ma mb).
    now destruct h; simpl; eauto.
  Defined.

  Definition forall2_sym ma mb :
    Forall2 P ma mb →
    Forall2 (λ b a, P a b) mb ma.
  Proof. elim => //; eauto. Defined.

End FORALL2.*)

Section GLOB_DEFS.

Context (gd: glob_defs).

Lemma ssem_pexpr_uincl s ss e v1:
  sestate_uincl s ss ->
  sem_pexpr gd s e = ok v1 ->
  exists v2, ssem_pexpr gd ss e = ok v2 /\ svalue_uincl v1 v2.
Proof.
  move=> [Hu1 Hu2]; elim: e v1=>//= [z | b | sz e He | x | g | x p Hp | sz x p Hp | o e He | o e1 He1 e2 He2| eb Heb e1 He1 e2 He2 ] v1.
  + by move=> [] <-;exists z.
  + by move=> [] <-;exists b.
  + apply: rbindP => z; apply: rbindP => ve /He [] ve' [] -> Hvu Hto [] <-.
    case: (svalue_uincl_int Hvu Hto) => ??;subst; exists (SVword (wrepr sz z)); simpl; split => //=; case:ifP => /eqP //= _.
    by rewrite psem.truncate_word_u.
  + move=> ?; eexists; split=> //; exact: sget_var_uincl.
  + rewrite/get_global/sget_global; case: get_global_word => // v' h; apply ok_inj in h; subst.
    by exists (SVword v'); split => //=; rewrite psem.truncate_word_u.
  + have := Hu2 x;case x => -[xt xn] xi /= H H';move: H' H.
    apply: on_arr_varP=> /= sz n t -> /= /(sget_var_uincl Hu2) /=.
    case:ifP => _ //= Hsame.
    apply: rbindP => z;apply: rbindP => vp /Hp [] vp' [] Hvp' Hvu /(svalue_uincl_int Hvu) [Hvp1 Hvp2].
    apply: rbindP=> w Hw [] <- /= ?.
    rewrite Hvp' Hvp2 /=.
    eexists; split=> //. simpl.
    case:ifP => /eqP //= _.
    by rewrite (Hsame _ _ Hw).
  + apply: rbindP => w1.
    apply: rbindP => vx.
    move => /(sget_var_uincl Hu2).
    move => /svalue_uincl_word H/H.
    have Hu64 := (H U64).
    move => [sz' [w' [sz'' [w'' [tr_w' [temp->]]]]]]; subst => /=.
    apply:rbindP => wb.
    apply: rbindP => vb sem_vb. apply Hp in sem_vb. move:sem_vb => [v2 ssem_v2].
    move => point_wb.
    apply: rbindP  => wsz Hwsz val_wsz. apply ok_inj in val_wsz. subst.
    exists v2. simpl.
    apply: rbindP => vb => Hvb Hpvb;apply:rbindP => wsz read_wsz val_wsz.
    exists (SVword w'');subst.
    rewrite var_x. simpl.
    rewrite -Hu1 /=.
    case: (svalue_uincl_word Hvu Hto) => ??;subst.
    by apply rbindP => w /= /mem2smem_read -> [] <-;exists w.
  + apply: rbindP => w /He {He} [] w' [] ->; apply svuincl_sem_op1.
  + apply: rbindP => ve1 /He1 [] ve1' [] -> Hvu1.
    apply: rbindP => ve2 /He2 [] ve2' [] -> Hvu2 {He1 He2}.
    case:o=> [||[]|[]|[]|[]|[]|[]||||[]|[]|[]|[]|[]|[]] => /=;
    eauto using svuincl_sem_op2_i, svuincl_sem_op2_w, 
                svuincl_sem_op2_b, svuincl_sem_op2_ib, svuincl_sem_op2_wb.
  + apply: rbindP => b; apply: rbindP => ? /Heb {Heb} [] b' [] -> h.
    move=> Q; apply to_bool_inv in Q; subst.
    apply: rbindP => w1 /He1 {He1} [] w1' [] -> h1.
    apply: rbindP => w2 /He2 {He2} [] w2' [] -> h2.
    apply: rbindP => z1 Z1; apply: rbindP => z2 Z2.
    move=> Q; apply ok_inj in Q; subst.
    case: b' h => // b' <- {b'} /=.
    exists (if b then w1' else w2'); split; last by case: b.
    case: (of_sval_uincl h1 Z1) => x1 [] X1 [] _ ->; rewrite X1 /=.
    case: (of_sval_uincl h2 Z2) => x2 [] -> _ //.
Qed.
(*
Lemma ssem_pexprs_uincl s ss es vs1:
  sestate_uincl s ss ->
  sem_pexprs gd s es = ok vs1 ->
  exists vs2, ssem_pexprs gd ss es = ok vs2 /\
              List.Forall2 svalue_uincl vs1 vs2.
Proof.
  rewrite /sem_pexprs /ssem_pexprs; move=> Hvm;elim: es vs1 => [ | e es Hrec] vs1 /=.
  + by move=> [] <-;eauto.
  apply: rbindP => ve /(ssem_pexpr_uincl Hvm) [] ve' [] -> ?.
  by apply: rbindP => ys /Hrec [vs2 []] /= -> ? [] <- /=;eauto.
Qed.

Lemma svalue_of_value_uincl v :
  svalue_uincl v (svalue_of_value v).
Proof.
  case: v => //.
  + by move=> n a i w h; rewrite/FArray.get h.
  by case.
Qed.

Lemma svalues_of_values_uincl v :
  List.Forall2 svalue_uincl v (svalues_of_values v).
Proof.
  elim: v => [ | v vs ih ]; constructor; eauto using svalue_of_value_uincl.
Qed.

Lemma svuincl_app_w o vs vs' v :
  List.Forall2 svalue_uincl vs vs' →
  (app_w o) vs = ok v →
  ∃ v', sapp_w (w1 o) vs' = ok v' ∧ List.Forall2 svalue_uincl v v'.
Proof.
  case: vs => // x vs le; apply: rbindP => w /to_word_inv ?; subst x.
  case: vs le => // /forall2_inv_left [w'] [q] [?] [le] /forall2_inv_left hq h; subst.
  case: w' le => // w' /= ?; subst.
  rewrite h. eexists. split. reflexivity.
  exact: svalues_of_values_uincl.
Qed.

Lemma svuincl_app_b o vs vs' v :
  List.Forall2 svalue_uincl vs vs' →
  (app_b o) vs = ok v →
  ∃ v', sapp_b (w1 o) vs' = ok v' ∧ List.Forall2 svalue_uincl v v'.
Proof.
  case: vs => // x vs le; apply: rbindP => w /to_bool_inv ?; subst x.
  case: vs le => // /forall2_inv_left [w'] [q] [?] [le] /forall2_inv_left hq h; subst.
  case: w' le => // w' /= ?; subst.
  rewrite h. eexists. split. reflexivity.
  exact: svalues_of_values_uincl.
Qed.

Lemma svuincl_app_ww o vs vs' v :
  List.Forall2 svalue_uincl vs vs' →
  (app_ww o) vs = ok v →
  ∃ v', sapp_ww (w2 o) vs' = ok v' ∧ List.Forall2 svalue_uincl v v'.
Proof.
  case: vs => // x vs le; apply: rbindP => w /to_word_inv ?; subst x.
  case: vs le => // x vs le; apply: rbindP => w' /to_word_inv ?; subst x.
  case: vs le => // /forall2_inv_left [z] [q] [?] [le]
                    /forall2_inv_left [z'] [x] [hq] [le']
                    /forall2_inv_left hz' h; subst.
  case: z le => // z /= ?; subst.
  case: z' le' => // z' /= ?; subst.
  rewrite h. eexists. split. reflexivity.
  exact: svalues_of_values_uincl.
Qed.

Lemma svuincl_app_www o vs vs' v :
  List.Forall2 svalue_uincl vs vs' →
  (app_www o) vs = ok v →
  ∃ v', sapp_www (w3 o) vs' = ok v' ∧ List.Forall2 svalue_uincl v v'.
Proof.
  case: vs => // x vs le; apply: rbindP => w /to_word_inv ?; subst x.
  case: vs le => // x vs le; apply: rbindP => w' /to_word_inv ?; subst x.
  case: vs le => // x vs le; apply: rbindP => w'' /to_word_inv ?; subst x.
  case: vs le => // /forall2_inv_left [z] [q] [?] [le]
                    /forall2_inv_left [z'] [x] [hq] [le']
                    /forall2_inv_left [z''] [y] [hr] [le'']
                    /forall2_inv_left hz' h; subst.
  case: z le => // z /= ?; subst.
  case: z' le' => // z' /= ?; subst.
  case: z'' le'' => // z'' /= ?; subst.
  rewrite h. eexists. split. reflexivity.
  exact: svalues_of_values_uincl.
Qed.

Lemma svuincl_app_wwb o vs vs' v :
  List.Forall2 svalue_uincl vs vs' →
  (app_wwb o) vs = ok v →
  ∃ v', sapp_wwb (w3 o) vs' = ok v' ∧ List.Forall2 svalue_uincl v v'.
Proof.
  case: vs => // x vs le; apply: rbindP => w /to_word_inv ?; subst x.
  case: vs le => // x vs le; apply: rbindP => w' /to_word_inv ?; subst x.
  case: vs le => // x vs le; apply: rbindP => w'' /to_bool_inv ?; subst x.
  case: vs le => // /forall2_inv_left [z] [q] [?] [le]
                    /forall2_inv_left [z'] [x] [hq] [le']
                    /forall2_inv_left [z''] [y] [hr] [le'']
                    /forall2_inv_left hz' h; subst.
  case: z le => // z /= ?; subst.
  case: z' le' => // z' /= ?; subst.
  case: z'' le'' => // z'' /= ?; subst.
  rewrite h. eexists. split. reflexivity.
  exact: svalues_of_values_uincl.
Qed.

Lemma svuincl_app_w4 o vs vs' v :
  List.Forall2 svalue_uincl vs vs' →
  (app_w4 o) vs = ok v →
  ∃ v', sapp_w4 (w4 o) vs' = ok v' ∧ List.Forall2 svalue_uincl v v'.
Proof.
  case: vs => // x vs le; apply: rbindP => w /to_word_inv ?; subst x.
  case: vs le => // x vs le; apply: rbindP => w' /to_word_inv ?; subst x.
  case: vs le => // x vs le; apply: rbindP => w'' /to_word_inv ?; subst x.
  case: vs le => // x vs le; apply: rbindP => w''' /to_word_inv ?; subst x.
  case: vs le => // /forall2_inv_left [z] [q] [?] [le]
                    /forall2_inv_left [z'] [x] [hq] [le']
                    /forall2_inv_left [z''] [y] [hr] [le'']
                    /forall2_inv_left [z'''] [n] [hn] [le''']
                    /forall2_inv_left hz' h; subst.
  case: z le => // z /= ?; subst.
  case: z' le' => // z' /= ?; subst.
  case: z'' le'' => // z'' /= ?; subst.
  case: z''' le''' => // z''' /= ?; subst.
  rewrite h. eexists. split. reflexivity.
  exact: svalues_of_values_uincl.
Qed.

Lemma svuincl_exec_opn o vs vs' v :
  List.Forall2 svalue_uincl vs vs' -> exec_sopn o vs = ok v ->
  exists v', ssem_sopn o vs' = ok v' /\ List.Forall2 svalue_uincl v v'.
Proof.
  rewrite /exec_sopn /ssem_sopn;
    case: o;
    eauto using svuincl_app_w, svuincl_app_b, svuincl_app_ww, svuincl_app_www, svuincl_app_wwb, svuincl_app_w4.
  + move => x y; move: y x.
    case: vs => // ? vs /=; apply: rbindP => x /to_word_inv ?; subst.
    case: vs => // ? vs /=; apply: rbindP => y /to_word_inv ?; subst.
    case: vs => // h; apply ok_inj in h; subst.
    case/forall2_inv_left=> x' [q] [?] [hx]; subst.
    case/forall2_inv_left=> y' [r] [?] [hy]; subst.
    move/forall2_inv_left -> => {r}.
    case: x' hx => //= x' hx; subst.
    case: y' hy => //= y' hy; subst.
    eexists; split. reflexivity.
    case: (wumul x' y') => a b; rewrite/pval/spval/=. repeat constructor.
  + move => x y; move: y x.
    case: vs => // ? vs /=; apply: rbindP => x /to_word_inv ?; subst.
    case: vs => // ? vs /=; apply: rbindP => y /to_word_inv ?; subst.
    case: vs => // ? vs /=; apply: rbindP => z /to_bool_inv ?; subst.
    case: vs => // h; apply ok_inj in h; subst.
    case/forall2_inv_left=> x' [q] [?] [hx]; subst.
    case/forall2_inv_left=> y' [t] [?] [hy]; subst.
    case/forall2_inv_left=> z' [r] [?] [hz]; subst.
    move/forall2_inv_left -> => {r}.
    case: x' hx => //= x' hx; subst.
    case: y' hy => //= y' hy; subst.
    case: z' hz => //= z' hz; subst.
    eexists; split. reflexivity.
    case: (waddcarry x' y' z') => a b; rewrite/pval/spval/=. repeat constructor.
  + move => x y; move: y x.
    case: vs => // ? vs /=; apply: rbindP => x /to_word_inv ?; subst.
    case: vs => // ? vs /=; apply: rbindP => y /to_word_inv ?; subst.
    case: vs => // ? vs /=; apply: rbindP => z /to_bool_inv ?; subst.
    case: vs => // h; apply ok_inj in h; subst.
    case/forall2_inv_left=> x' [q] [?] [hx]; subst.
    case/forall2_inv_left=> y' [t] [?] [hy]; subst.
    case/forall2_inv_left=> z' [r] [?] [hz]; subst.
    move/forall2_inv_left -> => {r}.
    case: x' hx => //= x' hx; subst.
    case: y' hy => //= y' hy; subst.
    case: z' hz => //= z' hz; subst.
    eexists; split. reflexivity.
    case: (wsubcarry x' y' z') => a b; rewrite/pval/spval/=. repeat constructor.
  + move => x y; move: y x.
    case: vs => // h; apply ok_inj in h; subst v.
    move/forall2_inv_left => h; subst.
    eexists; split. reflexivity.
    repeat constructor.
  + move => x y; move: y x.
    case: vs => // x [] // y [] // z [] //; apply: rbindP => b /to_bool_inv ?; subst.
    move=> h /forall2_inv_left [b'] [q] [?] [hb]; subst.
    case/forall2_inv_left=> y' [t] [?] [hy]; subst.
    case/forall2_inv_left=> z' [r] [?] [hz]; subst.
    move/forall2_inv_left -> => {r}.
    case: b' hb => //= b' hb; subst.
    case: b' h; apply: rbindP => w /to_word_inv ?; subst; move => h; apply ok_inj in h; subst.
    * case: y' hy => //= y' hy; subst.
      eexists; repeat constructor.
    case: z' hz => //= z' hz; subst.
    eexists; repeat constructor.
Qed.

Lemma sset_vm_uincl vm vm' x z z' :
  svm_uincl vm vm' ->
  sval_uincl z z' ->
  svm_uincl (vm.[x <- ok z])%vmap (vm'.[x <- z'])%vmap.
Proof.
  move=> Hvm Hz y; case( x =P y) => [<- | /eqP Hneq];by rewrite ?Fv.setP_eq ?Fv.setP_neq.
Qed.
 

Lemma sset_var_uincl vm1 vm1' vm2 x v v' :
  svm_uincl vm1 vm1' ->
  svalue_uincl v v' ->
  set_var vm1 x v = ok vm2 ->
  exists vm2', sset_var vm1' x v' = ok vm2' /\ svm_uincl vm2 vm2'.
Proof.
  move=> Hvm Hv;rewrite /set_var /sset_var.
  apply: on_vuP.
  + move=> z /(of_sval_uincl Hv) [z'] [->] [le] _ <- /=.
    by exists (vm1'.[x <- z'])%vmap;split=>//; apply sset_vm_uincl.
  move/of_val_addr_undef => ?; subst v.
  case: eqP => // ht q; apply ok_inj in q; subst.
  case: (of_sval_ex Hv) => w [->] hv' /=. subst.
  eexists. split. reflexivity.
  move=> y; case: (x =P y) => [ <- | /eqP ne ]; last by rewrite ! Fv.setP_neq.
  rewrite ! Fv.setP_eq.
  case: (vtype x) w ht {Hv} => //.
  move=> p w _ i v h; elim (Array.getP_empty h).
Qed. Admitted.


Lemma SArray_set_uincl n (a1:Array.array n word) (a2: FArray.array word) (a1':Array.array n word) i v:
  @sval_uincl (sarr n) a1 a2 ->
  Array.set a1 i v = ok a1' ->
  exists a2', FArray.set a2 i v = a2' /\ @sval_uincl (sarr n) a1' a2'.
Proof.
  rewrite /Array.set;case:ifP=> //= ? H [] <-.
  exists (FArray.set a2 i v);split => // i' v';move: (H i' v').
  rewrite /Array.get;case:ifP=> //= Hbound.
  rewrite !FArray.setP;case:ifP=> //.
  by move=> ?? [] ->.
Qed.

Lemma swrite_var_uincl s ss s' v1 v2 x :
  sestate_uincl s ss ->
  svalue_uincl v1 v2 ->
  write_var x v1 s = ok s' ->
  exists ss' : sestate,
    swrite_var x v2 ss = ok ss' /\ sestate_uincl s' ss'.
Proof.
  move=> [? Hvm1] Hv;rewrite /write_var /swrite_var;apply: rbindP=> vm2 /=.
  by move=> /(sset_var_uincl Hvm1 Hv) [vm2' [-> ?]] [] <- /=; exists {| semem := semem ss; sevm := vm2' |}.
Qed.

Lemma swrite_vars_uincl s ss s' vs1 vs2 xs :
  sestate_uincl s ss ->
  List.Forall2 svalue_uincl vs1 vs2 ->
  write_vars xs vs1 s = ok s' ->
  exists ss' : sestate,
    swrite_vars xs vs2 ss =
    ok ss' /\ sestate_uincl s' ss'.
Proof.
  elim: xs s ss vs1 vs2 => /= [ | x xs Hrec] s ss vs1 vs2 Hvm [] //=.
  + by move=> [] <-;eauto.
  move=> {vs1 vs2} v1 v2 vs1 vs2 Hv Hvs;apply: rbindP => s1'.
  by move=> /(swrite_var_uincl Hvm Hv) [] vm2 [] -> Hvm2 /(Hrec _ _ _ _ Hvm2 Hvs).
Qed.

Lemma swrite_uincl s1 s' ss1 r v1 v2:
  sestate_uincl s1 ss1 ->
  svalue_uincl v1 v2 ->
  write_lval gd r v1 s1 = ok s' ->
  exists ss',
    swrite_lval gd r v2 ss1 = ok ss' /\ sestate_uincl s' ss'.
Proof.
  move=> Hs1 Hv;case:r => [xi ty | x | x p | x p] /=.
  + apply: on_vuP.
    * by move=> w1 h ?; subst; eauto.
    * case: eqP => // ne h H; apply ok_inj in H; subst; eauto.
  + rewrite /write_var /swrite_var;apply: rbindP=> vm2 /=.
    move: Hs1=> [Hmem1 Hvm1].
    rewrite -Hmem1.
    by move=> /(sset_var_uincl Hvm1 Hv) [vm2' [-> ?]] [] <- /=;exists {| semem := mem_to_smem (emem s1); sevm := vm2' |}.
  + apply: rbindP => vx; apply: rbindP=> x' Hx' /(svalue_uincl_word (sget_var_uincl (proj2 Hs1) Hx')) [] _ ->.
    apply: rbindP => ve; apply: rbindP => ve' /(ssem_pexpr_uincl Hs1) [ve''] [] -> Hve.
    move=> /(svalue_uincl_word Hve) [] _ -> /=.
    apply: rbindP => w /(svalue_uincl_word Hv) [] _ -> /=.
    move: Hs1=> [Hmem1 Hvm1].
    rewrite -Hmem1.
    by apply: rbindP => m' /mem2smem_write <- [] <-; exists {| semem := mem_to_smem m'; sevm := sevm ss1 |}.
  case: s1 Hs1 => m vm /=.
  case: ss1 => m' vm' Hs1.
  case Hs1 => /= ? hvm; subst.
  apply: on_arr_varP=> n a.
  case: x=> -[xt xn] xi /= -> /= /(sget_var_uincl hvm) h.
  t_xrbindP => ofs vp /(ssem_pexpr_uincl Hs1) [vp' [ -> Hvp ] ] /(svalue_uincl_int Hvp) [] ? ?; subst.
  move=> w /(svalue_uincl_word Hv) [] ? ? a'; subst.
  move=> /(SArray_set_uincl h) [] ? [] ? ha'; subst.
  move=> res /(sset_var_uincl (v' := SVarr _) hvm).
  move=>/(_ _ ha') [] res' [] hres' r ?; apply ok_inj in hres'; subst.
  rewrite /son_arr_var /=.
  by repeat econstructor.
Qed.

Lemma swrites_uincl s s' ss r v1 v2:
  sestate_uincl s ss ->
  List.Forall2 svalue_uincl v1 v2 ->
  write_lvals gd s r v1 = ok s' ->
  exists ss',
    swrite_lvals gd ss r v2 = ok ss' /\
    sestate_uincl s' ss'.
Proof.
  elim: r v1 v2 s ss=> [|r rs Hrec] v1 v2 s ss Hs /= [] //=.
  + by move=> [] <-; exists ss.
  move=> {v1 v2} v1 v2 vs1 vs2 Hv Hforall.
  apply: rbindP=> z /(swrite_uincl Hs Hv) [] x [] -> Hz.
  by move=> /(Hrec _ _ _ _ Hz Hforall).
Qed.

(* -------------------------------------------------------------------- *)*)
Section SEM.

Variable (p:prog).

Let Pc s1 c s2 :=
  forall ss1,
    sestate_uincl s1 ss1 -> exists ss2, ssem p gd ss1 c ss2 /\ sestate_uincl s2 ss2.

Let Pi_r s1 c s2 :=
  forall ss1,
    sestate_uincl s1 ss1 -> exists ss2, ssem_i p gd ss1 c ss2 /\ sestate_uincl s2 ss2.

Let Pi s1 c s2 :=
  forall ss1,
    sestate_uincl s1 ss1 -> exists ss2, ssem_I p gd ss1 c ss2 /\ sestate_uincl s2 ss2.

Let Pfor i zs s1 c s2 :=
  forall ss1,
    sestate_uincl s1 ss1 -> exists ss2, ssem_for p gd i zs ss1 c ss2 /\ sestate_uincl s2 ss2.

Let Pfun m1 fd vargs m2 vres :=
  forall vargs', List.Forall2 svalue_uincl vargs vargs' ->
    exists vres',
    ssem_call p gd (mem_to_smem m1) fd vargs' (mem_to_smem m2) vres' /\
    List.Forall2 svalue_uincl vres vres'.

(*Local Lemma Hnil s : Pc s [::] s.
Proof. by move=> vm1 Hvm1;exists vm1;split=> //;constructor. Qed.
*)
Local Lemma Hcons s1 s2 s3 i c :
  sem_I p gd s1 i s2 -> Pi s1 i s2 ->
  sem p gd s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.
Proof.
  move=> _ Hi _ Hc vm1 /Hi [vm2 []] Hsi /Hc [vm3 []] Hsc ?.
  by exists vm3;split=>//;econstructor;eauto.
Qed.
(*
Local Lemma HmkI ii i s1 s2 : sem_i p gd s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.
Proof. by move=> _ Hi vm1 /Hi [vm2 []] Hsi ?;exists vm2. Qed.
*)
Local Lemma Hasgn s1 s2 x tag st e :
  Let v := sem_pexpr gd s1 e in write_lval gd x v s1 = ok s2 ->
  Pi_r s1 (Cassgn x tag st e) s2.
Proof.
  move=> Hs2 vm1 Hvm1;apply:rbindP Hs2 => z /(ssem_pexpr_uincl Hvm1) [] z' [] Hz' Hz.
  move=> /(swrite_uincl Hvm1 Hz) [vm2 []] Hw ?;exists vm2;split=> //.
  by constructor;rewrite Hz' /= Hw.
Qed.
(*
Local Lemma Hopn s1 s2 t o xs es:
  sem_sopn gd o s1 xs es = ok s2 ->
  Pi_r s1 (Copn xs t o es) s2.
Proof.
  move=> H vm1 Hvm1; apply: rbindP H => rs;apply: rbindP => vs.
  move=> /(ssem_pexprs_uincl Hvm1) [] vs' [] H1 H2.
  move=> /(svuincl_exec_opn H2) [] rs' [] H3 H4.
  move=> /(swrites_uincl Hvm1 H4) [] vm2 [] ??.
  exists vm2;split => //;constructor.
  by rewrite H1 /= H3.
Qed.

Local Lemma Hif_true s1 s2 e c1 c2 :
  Let x := sem_pexpr gd s1 e in to_bool x = ok true ->
  sem p gd s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
Proof.
  move=> H _ Hc vm1 Hvm1;apply: rbindP H => v.
  move=> /(ssem_pexpr_uincl Hvm1) [] v' [] H1 H2.
  move=> /(svalue_uincl_bool H2) [] ??;subst.
  have [vm2 [??]]:= Hc _ Hvm1;exists vm2;split=>//.
  by apply SEif_true;rewrite // H1.
Qed.

Local Lemma Hif_false s1 s2 e c1 c2 :
  Let x := sem_pexpr gd s1 e in to_bool x = ok false ->
  sem p gd s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
Proof.
  move=> H _ Hc vm1 Hvm1;apply: rbindP H => v.
  move=> /(ssem_pexpr_uincl Hvm1) [] v' [] H1 H2.
  move=> /(svalue_uincl_bool H2) [] ??;subst.
  have [vm2 [??]]:= Hc _ Hvm1;exists vm2;split=>//.
  by apply SEif_false;rewrite // H1.
Qed.

Local Lemma Hwhile_true s1 s2 s3 s4 c e c' :
  sem p gd s1 c s2 -> Pc s1 c s2 ->
  Let x := sem_pexpr gd s2 e in to_bool x = ok true ->
  sem p gd s2 c' s3 -> Pc s2 c' s3 ->
  sem_i p gd s3 (Cwhile c e c') s4 -> Pi_r s3 (Cwhile c e c') s4 -> Pi_r s1 (Cwhile c e c') s4.
Proof.
  move=> _ Hc H _ Hc' _ Hw vm1 Hvm1;apply: rbindP H => v.
  have [vm2 [Hs2 Hvm2]] := Hc _ Hvm1.
  move=> /(ssem_pexpr_uincl Hvm2) [] v' [] H1 H2.
  move=> /(svalue_uincl_bool H2) [] ??;subst.
  have [vm3 [H4 /Hw [vm4] [??]]]:= Hc' _ Hvm2;exists vm4;split => //.
  by eapply SEwhile_true;eauto;rewrite H1.
Qed.

Local Lemma Hwhile_false s1 s2 c e c' :
  sem p gd s1 c s2 -> Pc s1 c s2 ->
  Let x := sem_pexpr gd s2 e in to_bool x = ok false ->
  Pi_r s1 (Cwhile c e c') s2.
Proof.
  move=> _ Hc H vm1 Hvm1; apply: rbindP H => v.
  have [vm2 [Hs2 Hvm2]] := Hc _ Hvm1.
  move=> /(ssem_pexpr_uincl Hvm2) [] v' [] H1 H2.
  move=> /(svalue_uincl_bool H2) [] ??;subst.
  by exists vm2;split=> //;apply: SEwhile_false=> //;rewrite H1.
Qed.

Local Lemma Hfor s1 s2 (i : var_i) d lo hi c (vlo vhi : Z) :
  Let x := sem_pexpr gd s1 lo in to_int x = ok vlo ->
  Let x := sem_pexpr gd s1 hi in to_int x = ok vhi ->
  sem_for p gd i (wrange d vlo vhi) s1 c s2 ->
  Pfor i (wrange d vlo vhi) s1 c s2 ->
  Pi_r s1 (Cfor i (d, lo, hi) c) s2.
Proof.
  move=> H H' _ Hfor vm1 Hvm1;apply: rbindP H => ?.
  move=> /(ssem_pexpr_uincl Hvm1) [] ? [] H1 H2.
  move=> /(svalue_uincl_int H2) [] ??;subst.
  apply: rbindP H' => ?.
  move=> /(ssem_pexpr_uincl Hvm1) [] ? [] H3 H4.
  move=> /(svalue_uincl_int H4) [] ??;subst.
  have [vm2 []??]:= Hfor _ Hvm1; exists vm2;split=>//.
  by econstructor;eauto;rewrite ?H1 ?H3.
Qed.

Local Lemma Hfor_nil s i c : Pfor i [::] s c s.
Proof. by move=> vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

Local Lemma Hfor_cons s1 s1' s2 s3 (i : var_i) (w : Z) (ws : seq Z) c :
  write_var i w s1 = ok s1' ->
  sem p gd s1' c s2 -> Pc s1' c s2 ->
  sem_for p gd i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.
Proof.
  move=> Hi _ Hc _ Hf vm1 Hvm1.
  have [//|vm1' [Hi' /Hc]] := @swrite_var_uincl _ _ _ _ (SVint w) _ Hvm1 _ Hi.
  move=> [vm2 [Hsc /Hf]] [vm3 [Hsf Hvm3]];exists vm3;split => //.
  by econstructor;eauto.
Qed.

Local Lemma Hcall s1 m2 s2 ii xs fn args vargs vs :
  sem_pexprs gd s1 args = ok vargs ->
  sem_call p gd (emem s1) fn vargs m2 vs ->
  Pfun (emem s1) fn vargs m2 vs ->
  write_lvals gd {| emem := m2; evm := evm s1 |} xs vs = ok s2 ->
  Pi_r s1 (Ccall ii xs fn args) s2.
Proof.
  move=> Hargs Hcall Hfd Hxs s Hs.
  have [vargs' [Hsa /Hfd Hc]]:= ssem_pexprs_uincl Hs Hargs.
  have Hvm1: sestate_uincl {| emem := m2; evm := evm s1 |} {| semem := mem_to_smem m2; sevm := sevm s |}.
    split=> //.
    by move: Hs=> [_ ?].
  move: Hc=> [vres' [Hvres'1 Hvres'2]].
  have [vm2' [??]]:= swrites_uincl Hvm1 Hvres'2 Hxs.
  exists vm2';split=>//;econstructor;eauto.
  rewrite (proj1 Hvm1) /= in Hvres'1.
  rewrite (proj1 Hs) /= in Hvres'1.
  exact: Hvres'1.
Qed.
*)
(*Local Lemma Hproc m1 m2 fn fd vargs s1 vm2 vres:
  get_fundef p fn = Some fd ->
  write_vars (f_params fd) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
  sem p gd s1 (f_body fd) {| emem := m2; evm := vm2 |} ->
  Pc s1 (f_body fd) {| emem := m2; evm := vm2 |} ->
  mapM (fun x : var_i => get_var vm2 x) (f_res fd) = ok vres ->
  List.Forall is_full_array vres ->
  Pfun m1 fn vargs m2 vres.
Proof.
  move=> Hget Hargs Hsem Hrec Hmap Hfull vargs' Uargs.
  have Hss0: sestate_uincl {| emem := m1; evm := vmap0 |} {| semem := mem_to_smem m1; sevm := svmap0 |}.
    split=> //=.
    rewrite /vmap0 /svmap0 /svm_uincl.
    move=> [vi v] /=.
    rewrite /sval_uincl.
    case: vi => // p0 i v0.
    rewrite /Array.get /FArray.get.
    case: ifP=> //.
  have [ss1 [Hargs' Hss1]]:= swrite_vars_uincl Hss0 Uargs Hargs.
  have [ss2 /= [] Hssem2 Ussem2] := Hrec _ Hss1.
  exists (map (fun x : var_i => sget_var ss2.(sevm) x) (f_res fd)); split=> //.
  econstructor=> //.
  exact: Hget.
  exact: Hargs'.
  have ->: {| semem := mem_to_smem m2; sevm := sevm ss2 |} = ss2.
    move: ss2 Hssem2 Ussem2=> [ss2_1 ss2_2] Hssem2 Ussem2 /=.
    by rewrite (proj1 Ussem2) /=.
  exact: Hssem2.
  by apply: (sget_vars_uincl (proj2 Ussem2)).
Qed.

Lemma sem_uincl s1 c s2 ss1 :
  sestate_uincl s1 ss1 ->
  sem p gd s1 c s2 ->
  exists ss2,
    ssem p gd ss1 c ss2 /\
    sestate_uincl s2 ss2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_Ind p gd Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

End SEM.

End GLOB_DEFS.
