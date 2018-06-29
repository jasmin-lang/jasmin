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
  | Vword s w1, SVword s' w2  => if s == s' then zero_extend s w2 = w1 else False
  | Vundef ty, _ => sstype_of_stype ty = sval_sstype sv
  | _, _ => False
  end.

Lemma to_int_inv x i :
  to_int x = ok i →
  x = i.
Proof.
  case: x => // ? H.
  * apply ok_inj in H; congruence.
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

Require psem.

Definition sstype_stype_incl sst st :=
  match sst, st with
  |ssint, sint => true
  |ssbool, sbool => true
  |ssword s, sword s' => (s' <= s)%CMP
  |ssarr s, sarr s' _ => s == s'
  |_, _ => false
  end.

Lemma of_val_arr s n a v :
  of_val (sarr s n) (@Varr s n a) = ok v -> a = v.
Proof. by rewrite /of_val /to_arr (eq_dec_refl wsize_eq_dec) pos_dec_n_n;simpl; apply ok_inj.
Qed.

Lemma svalue_uincl_refl_w s (w:word s):
  svalue_uincl (Vword w) (SVword w).
Proof.
  by rewrite /svalue_uincl;case:ifP => /eqP //=;rewrite zero_extend_u.
Qed.

Lemma of_sval_uincl v v' t z:
  svalue_uincl v v' ->
  of_val t v = ok z ->
  exists z', of_sval t v' = ok z' /\ sval_uincl z z' ∧ sstype_stype_incl (sval_sstype v') t. (* Subtype ?*)
Proof.
  case: v  => [b | n  | s n a | s  w | ty];case: v' => [b'| n' | s' a' | s' w'] //=;
  try (by case: t z=> //= z -> []->; exists z);
  try (move=> _ H; elim (of_val_undef_ok H); fail); last first.
  + case: ifP => //= /eqP eq_ss' val_zw' H; subst s'.
    rewrite zero_extend_u in val_zw'; subst w'.
    have := (of_vword H); move => [s''] [le_ss'] H'; subst t.
    move:H;  rewrite /of_val //.
    exists z; split => //=.
  case: (s =P s') => //= eq_ss';subst s'.
  move => //= H2 H. rewrite /of_sval. 
  have H' := (of_varr H). subst t => //=.
  exists a'. split;last split => //=.
  rewrite eq_dec_refl; congr ok.
  apply of_val_arr in H; subst z.
  move => i w H; apply H2 in H;rewrite psem.truncate_word_u in H.
  by apply ok_inj in H.
Qed.

Lemma svalue_uincl_int ve ve' z :
  svalue_uincl ve ve' -> to_int ve = ok z -> ve = z /\ ve' = z.
Proof.
  move=> h t; case: (@of_sval_uincl ve ve' sint z h t) => /= z' [t' q].
  apply sto_int_inv in t'; apply to_int_inv in t. intuition congruence.
Qed.

Lemma svalue_uincl_word_r ve ve' sz w :
  svalue_uincl ve ve' -> to_word sz ve = ok w ->
  exists sz', exists (w' : word sz'), exists sz'', exists (w'' : word sz''),
  truncate_word sz w' = ok w /\ ve = (Vword w') /\ ve' = (SVword w'').
Proof.
  move=> h t; case: (@of_sval_uincl ve ve' (sword sz) w h t) => /= z' [t' [sub rel]].
  subst z'.
  have := ((@to_word_inv sz ve w) t) => [] [sz'] [w'] [eq_vew'] trunc_ww'.
  have := ((@sto_word_inv sz ve' w) t') => [] [sz''] [w''] [eq_ve'w''] trunc_ww''.
  exists sz'; exists w'; exists sz''; exists w'';split => //=; split => //=.
Qed.

Variant svalue_uincl_word_spec sz (w : word sz) (ve : value) (ve' : svalue)
  : value -> svalue -> Prop
:=
| SValueUInclWord sz' sz'' (w' : word sz') (w'' : word sz''):
       truncate_word sz w'' = ok w
    -> ve = Vword w'
    -> ve' = SVword w''
    -> svalue_uincl_word_spec w ve ve' (Vword w') (SVword w'').

Lemma svalue_uincl_word ve ve' sz w :
  svalue_uincl ve ve' -> to_word sz ve = ok w ->
  svalue_uincl_word_spec w ve ve' ve ve'.
Proof.
move=> h ok_ve; move/of_sval_uincl: h => /(_ (sword sz) _ ok_ve).
case=> /= w' [ok_ve'] [? h]; subst w'.
case/to_word_inv: ok_ve=> [sz1] [w1] [? ok1];subst ve.
case/sto_word_inv: ok_ve'=> [sz2] [w2] [? ok2];subst ve'.
by constructor.
Qed.

Lemma svalue_uincl_bool ve ve' b :
  svalue_uincl ve ve' -> to_bool ve = ok b -> ve = b /\ ve' = b.
Proof.
  move=> h t; case: (@of_sval_uincl ve ve' sbool b h t) => /= z' [t' q].
  apply sto_bool_inv in t'; apply psem.to_boolI in t.
  intuition congruence.
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
+ by move => i w H'; apply H in H'; rewrite H' psem.truncate_word_u.
+ by move => s w H; case:ifP;  move => /eqP //= _; rewrite -H zero_extend_u.
move=> H _; apply ok_inj in H; subst.
symmetry.
exact: sval_sstype_to_sval.
Qed.

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

Ltac svalue_uincl :=
  repeat match goal with
  | H : svalue_uincl ?a ?b, K : to_word _ ?a = ok _ |- _ =>
    let R := fresh in
    case: (svalue_uincl_word H K) => {H K} ???? R ??; subst; move: R
  | H : svalue_uincl ?a ?b, K : to_bool ?a = ok _ |- _ =>
    case: (svalue_uincl_bool H K) => {H K} ??; subst
  | H : svalue_uincl ?a ?b, K : to_int ?a = ok _ |- _ =>
    case: (svalue_uincl_int H K) => {H K} ??; subst
  end.

Lemma svuincl_sem_op2 o v1 v1' v2 v2' v :
  svalue_uincl v1 v1'
  → svalue_uincl v2 v2'
    → sem_sop2 o v1 v2 = ok v
      → exists2 v' : svalue,
          ssem_sop2 o v1' v2' = ok v' & svalue_uincl v v'.
Proof.
rewrite /sem_sop2; case: o;
repeat match goal with
| |- ∀ _ : op_kind, _ => case
| |- ∀ _ : cmp_kind, _ => case
end;
rewrite /=; t_xrbindP; intros; svalue_uincl.
all: try by eexists; [ reflexivity | ].
all: repeat match goal with
| h : mk_sem_divmod _ _ _ = ok _ |- _ =>
  move: h; rewrite /mk_sem_divmod; case: ifP => // ? [?]; subst
end.
all: try by
rewrite /ssem_op2_w /ssem_op2_w8 /ssem_op2_wb
  /mk_ssem_sop2 /= => -> -> /=;
(eexists; [ reflexivity | ( done || exact: svalue_uincl_refl_w ) ]).
Qed.

Lemma svuincl_sem_op1 o v v' r :
  svalue_uincl v v' → sem_sop1 o v = ok r →
  exists2 r' : svalue, ssem_sop1 o v' = ok r' & svalue_uincl r r'.
Proof.
case: o => /=.
+ move=> sz sz' incl_v_v'; rewrite /sem_sop1 /=; t_xrbindP => /=.
  move=> v_w' /svalue_uincl_word -/(_ _ incl_v_v') {incl_v_v'}.
  case=> szv szv' wv wv' tr_w'_wv' _ _ rE; subst r.
  exists (SVword (sign_extend sz v_w')).
  * by rewrite /mk_ssem_sop1 /= tr_w'_wv'.
  * by rewrite /= eqxx zero_extend_u.
+ move=> sz sz' incl_v_v'; rewrite /sem_sop1 /=; t_xrbindP => /=.
  move=> v_w' /svalue_uincl_word -/(_ _ incl_v_v') {incl_v_v'}.
  case=> szv szv' wv wv' tr_w'_wv' _ _ rE; subst r.
  exists (SVword (zero_extend sz v_w')).
  * by rewrite /mk_ssem_sop1 /= tr_w'_wv'.
  * by rewrite /= eqxx zero_extend_u.
+ move=> Hvalue.
  apply: rbindP => b Hb; apply psem.to_boolI in Hb; subst.
  move=> Hr; apply ok_inj in Hr; subst.
  by case: v' Hvalue => // b' <- {b'}; eexists (negb b).
+ rewrite /sem_sop1 /= => sz h; t_xrbindP => ? hw <-.
  case: (svalue_uincl_word h hw) => ???? k ??; subst.
  eexists.
  * by rewrite /ssem_op1_w /mk_ssem_sop1 /= k.
  by rewrite /= eqxx zero_extend_u.
+ rewrite /sem_sop1 => -[|s] h /=; t_xrbindP => ? h' <-.
  * case: (svalue_uincl_int h h') => ??; subst.
    eexists; reflexivity.
  case: (svalue_uincl_word h h') => ???? k ??; subst.
  eexists.
  * by rewrite /ssem_op1_w /mk_ssem_sop1 /= k.
  by rewrite /= eqxx zero_extend_u.
Qed.

Section GLOB_DEFS.

Context (gd: glob_decls).

Lemma of_sval_sstype v: exists2 t, of_sval (sval_sstype v) v = ok t & to_sval t = v.
Proof.
rewrite/sval_sstype/of_sval.
case: v => [b | z | s a | s w];[by exists b| by exists z| exists a| exists w] => //=;
[by rewrite eq_dec_refl | by rewrite psem.truncate_word_u].
Qed.

Lemma svalue_uincl_type_eq v1 w1 v2 w2:
  svalue_uincl v1 w1 -> svalue_uincl v2 w2 ->
  is_defined v1 -> is_defined v2 ->
  type_of_val v1 == type_of_val v2 ->
  sval_sstype w1 = sval_sstype w2.
Proof.
rewrite /svalue_uincl /type_of_val /sval_sstype /is_defined.
case: v1; case: v2; case: w1; case w2 => //=.
+ move => s a s2 a2 s3 n a3 s4 n2 a4. case:eqP => //= eq; case: eqP => //= eq'; subst => z wsz _ _.
  by case/eqP => ->.
move => s w s' w' s'' w'' s''' w'''; case:eqP => //= eq; case: eqP => //= eq';subst; rewrite zero_extend_u.
by move => eq zero1 _ _ eq';case/eqP:eq' => -> . 
Qed.

Lemma ssem_pexpr_uincl_r s ss e v1:
  sestate_uincl s ss ->
  sem_pexpr gd s e = ok v1 ->
  exists2 v2, ssem_pexpr gd ss e = ok v2 & svalue_uincl v1 v2.
Proof.
  move=> [Hu1 Hu2]; elim: e v1=>//= [z | b | sz | sz e He | x | g | x p Hp | sz x p Hp | o e He | o e1 He1 e2 He2| eb Heb e1 He1 e2 He2 ] v1.
  + move=> [] <-. by exists z.
  + by move=> [] <-;exists b.
  + by move => ? [] <-; eexists; first reflexivity; rewrite /= eqxx => ?? /(@Array.getP_empty _ _ _ _).
  + apply: rbindP => z; apply: rbindP => ve /He [] ve' -> Hvu Hto [] <-.
    case: (svalue_uincl_int Hvu Hto) => ??;subst; exists (SVword (wrepr sz z)) => //=; case:ifP => /eqP //= _.
   by rewrite zero_extend_u.
  + move=> ?; eexists => //; exact: sget_var_uincl.
  + rewrite /get_global/sget_global.
    case: get_global_value => //= z [<-].
    by eexists => //=;rewrite zero_extend_u;case:eqP.
  + have := Hu2 x;case x => -[xt xn] xi /= H H';move: H' H.
    apply: on_arr_varP=> /= sz n t -> /= /(sget_var_uincl Hu2) /=.
    case:ifP => _ Hsame => //=;t_xrbindP.
    move => z vp /Hp [] vp' Hvp' Hvu /(svalue_uincl_int Hvu) [Hvp1  Hvp2] w Hw <- /= ?.
    rewrite Hvp' Hvp2 /=;eexists => //=.
    case:ifP => /eqP //= _;rewrite /truncate_word in Hsame.
    by have H:= (Hsame _ _ Hw); rewrite cmp_le_refl in H;apply ok_inj in H.
  + t_xrbindP => w1 vx var_vx /psem.of_val_word [sz' [w' [hsz ? ?]]].
    subst. move => w2 vp sem_vp point_vp wsz read_wsz ?. subst. have test := sget_var_uincl Hu2 var_vx.
    have : svalue_uincl (Vword w') (sget_var (sevm ss) x) -> (sget_var (sevm ss) x) = SVword w'.
    * case: sget_var => //= ? ?. case: eqP => // ? ?; subst; by rewrite zero_extend_u.
      move => /(_ test) -> /=.
      rewrite /truncate_word hsz /=. have [w2_ -> uincl_vpw2 /=] := Hp _ sem_vp .
      rewrite -Hu1 -(mem2smem_read read_wsz).
    have mem_read_wsz := mem2smem_read read_wsz.
    have :sto_pointer w2_ = ok w2; last move => -> //=.
    * have := svalue_uincl_word uincl_vpw2 point_vp;case => s3 s4 w3 w4 trunc_w3 vp_w3 word_w4.
      subst; rewrite /sto_pointer /sto_word -trunc_w3;move:uincl_vpw2;rewrite /svalue_uincl.
      case:eqP => //= eq_s3s4; subst.
    rewrite /sto_pointer /sto_word.
    exists (SVword wsz); rewrite -mem_read_wsz => //=.
    by case:eqP => //= _; rewrite mem_read_wsz zero_extend_u. 
  + apply: rbindP => w  /He {He} [] w' sem_w' uincl_ww' sem_sop1.
    rewrite sem_w' /=.
    by have :=svuincl_sem_op1 uincl_ww' sem_sop1.
  + apply: rbindP => ve1 /He1 [] ve1' -> Hvu1.
    apply: rbindP => ve2 /He2 [] ve2' -> Hvu2 {He1 He2} /=.
    exact: svuincl_sem_op2.
  + apply: rbindP => b; apply: rbindP => ? /Heb {Heb} [] b' -> h.
    move=> Q; apply psem.to_boolI in Q; subst.
    apply: rbindP => w1 /He1 {He1} [] w1' -> h1.
    apply: rbindP => w2 /He2 {He2} [] w2' -> h2.
    case:ifP => //= type_w1w2;case:ifP => //= def_w1w2 => w1_w2;apply ok_inj in w1_w2;
    move:w1_w2;case:ifP => valb ?;subst;[exists w1'|exists w2'];
    rewrite /svalue_uincl in h; move:h; case:b' => //= b' eq;subst; [rewrite valb|] => //=;
    move:def_w1w2 => /andP [def_v1 def_w2];                                                                                               
    have := svalue_uincl_type_eq h1 h2 def_v1 def_w2 type_w1w2; move => eq_sstype;
    have := of_sval_sstype w1';
    move =>[sem_w1' val_w1' to_val_semw1'];
    rewrite val_w1' => //=;rewrite eq_sstype;
    have := of_sval_sstype w2'; move => [sem_w2' val_w2' to_val_semw2'];
    rewrite val_w2' => //=.
Qed.

Lemma truncate_svalue_uincl v1 v2 ty v1':
  svalue_uincl v1 v2 ->
  truncate_val ty v1 = ok v1' ->
  exists v2', truncate_sval ty v2 = ok v2' /\  svalue_uincl v1' v2'.
Proof.
  case:v1 => [b|z|s n a|s w|t];case v2; try (by move => ? ?//=;subst);rewrite /truncate_val;
  try( by move => b';rewrite /svalue_uincl => ?;subst; case:ty => //= h;apply ok_inj in h;subst;rewrite /truncate_sval //=;eexists);
  try (by rewrite of_val_undef => //=).
  + move => sz a';rewrite /svalue_uincl;case: eqP => //= ?;subst => Ha.
    t_xrbindP;case: ty => //= sz2 w2 a2.
    case:wsize_eq_dec => //= ?;case:CEDecStype.pos_dec => //= ?;subst.
    move => H;apply ok_inj in H;subst => Hv1';subst => //=.
    rewrite /truncate_sval.
    eexists;split => //=.
    - rewrite eq_dec_refl => //=.
    - move => //=;case:eqP => //=.
  + move => sz wsz.
    rewrite /svalue_uincl;case:eqP => //= ?;subst.
    rewrite zero_extend_u => ?;subst;t_xrbindP.
    case: ty => //= s2 w2;rewrite /truncate_word.
    case:ifP => //= cmp_s2sz h;apply ok_inj in h;subst => ?;subst.
    eexists;split;first by rewrite /truncate_sval //=  /truncate_word cmp_s2sz //=.
    by move => //=;case:eqP => //= _;rewrite zero_extend_u.
Qed.

Lemma svalue_uincl_truncate v1 v2 ty v1' v2' :
  svalue_uincl v1 v2 ->
  truncate_val ty v1 = ok v1' ->
  truncate_sval ty v2 = ok v2' ->
  svalue_uincl v1' v2'.
Proof.
  case: v1;case:v2 => //=;
  try (by move => b ? ?;subst; rewrite /truncate_val /of_val //=; case:ty => //=;move => h;apply ok_inj in h;subst;
          rewrite /truncate_sval => //= h;apply ok_inj in h; subst);
  try (by move => b;case;case: ty => //=).
  + move => s a s' n a';case:ifP => //= /eqP ?;subst => Ha';case:ty => //= s2 n2.
    rewrite /truncate_sval //=;case:wsize_eq_dec => //= ?;subst => //=.
    rewrite /truncate_val //= eq_dec_refl; case:CEDecStype.pos_dec => //= ?;subst.
    move =>//= h h';apply ok_inj in h;apply ok_inj in h';subst.
    by rewrite /svalue_uincl;case:eqP.
  + move => s w s' w';case:eqP => //= ?;subst; rewrite zero_extend_u => ?;subst.
    case: ty => //= s'; rewrite /truncate_val //=.
    t_xrbindP => w2;rewrite /truncate_word;case:cmp_le => h //= ?; apply ok_inj in h; subst.
    rewrite /truncate_sval //= /truncate_word;case:cmp_le => //= h;apply ok_inj in h;subst.
    by case:eqP => //=;rewrite zero_extend_u.
  + case:ty => //=;move => s n s' a; case => //=.
  + case:ty => //=;move => s s' w; case => //=.
Qed.
    
Lemma ssem_pexpr_uincl s ss e ty v1 v1':
  sestate_uincl s ss ->
  sem_pexpr gd s e = ok v1 ->
  truncate_val ty v1 = ok v1' ->
  exists v2,exists v2', ssem_pexpr gd ss e = ok v2 /\ (truncate_sval ty v2 = ok v2' /\ svalue_uincl v1' v2').
Proof.
  move =>uincl sem_e trunc.
  have := ssem_pexpr_uincl_r uincl sem_e => [] [v2] ssem_e uincl_v1_v2.
  have := truncate_svalue_uincl uincl_v1_v2 trunc => [] [v2'] [trunc_v2] _.
  exists v2;exists v2'.
  rewrite ssem_e trunc_v2.
  split => //=;split => //=.
  by apply (svalue_uincl_truncate uincl_v1_v2 trunc trunc_v2).
Qed.

Lemma ssem_pexprs_uincl s ss es vs1:
  sestate_uincl s ss ->
  sem_pexprs gd s es = ok vs1 ->
  exists vs2, ssem_pexprs gd ss es = ok vs2 /\
              List.Forall2 svalue_uincl vs1 vs2.
Proof.
  rewrite /sem_pexprs /ssem_pexprs; move=> Hvm;elim: es vs1 => [ | e es Hrec] vs1 /=;first  by move=> [] <-;eauto.
  apply: rbindP => ve /(ssem_pexpr_uincl_r Hvm) [] ve' -> ?.
  by apply: rbindP => ys /Hrec [vs2 []] /= -> ? [] <- /=;eauto.
Qed.

Lemma svalue_of_value_uincl v :
  svalue_uincl v (svalue_of_value v).
Proof.
  case: v => // [s n a | s w|t];move => //=;try (rewrite eq_refl).
  + by move => i w h; rewrite/FArray.get h psem.truncate_word_u.
  + by rewrite zero_extend_u.
  + by case t => //=.
Qed.

Lemma svalues_of_values_uincl v :
  List.Forall2 svalue_uincl v (svalues_of_values v).
Proof.
  elim: v => [ | v vs ih ]; constructor; eauto using svalue_of_value_uincl.
Qed.

Ltac split_list :=
  repeat match goal with
  | |- ∀ v vs, List.Forall2 _ (v :: vs) _ → _ =>
      move => ?? /List_Forall2_inv_l [?] [?] [?] []; subst => ?
  | |- List.Forall2 _ [::] _ → _ => move => /List_Forall2_inv_l ?; subst
  | |- List.Forall2 _ ?vs _ → _ => case: vs => //=; t_xrbindP
  end.

Lemma svuincl_app_w sz o vs vs' v :
  List.Forall2 svalue_uincl vs vs' →
  (app_w sz o) vs = ok v →
  exists2 v', sapp_w sz (w1 o) vs' = ok v' & List.Forall2 svalue_uincl v v'.
Proof.
  split_list => ?? ok_v; svalue_uincl => h; rewrite /= h /= ok_v.
  eexists; [ reflexivity | exact: svalues_of_values_uincl ].
Qed.

Lemma svuincl_app_b o vs vs' v :
  List.Forall2 svalue_uincl vs vs' →
  (app_b o) vs = ok v →
  exists2 v', sapp_b (w1 o) vs' = ok v' & List.Forall2 svalue_uincl v v'.
Proof.
  split_list => ?? ok_v; svalue_uincl; rewrite /= ok_v.
  eexists; [ reflexivity | exact: svalues_of_values_uincl ].
Qed.

Lemma svuincl_app_ww sz o vs vs' v :
  List.Forall2 svalue_uincl vs vs' →
  (app_ww sz o) vs = ok v →
  exists2 v', sapp_ww sz (w2 o) vs' = ok v' & List.Forall2 svalue_uincl v v'.
Proof.
  split_list => ???? ok_v; svalue_uincl => h h'; rewrite /= h h' /= ok_v.
  eexists; [ reflexivity | exact: svalues_of_values_uincl ].
Qed.

 Lemma svuincl_app_www sz o vs vs' v :
  List.Forall2 svalue_uincl vs vs' →
  (app_www sz o) vs = ok v →
  exists2 v', sapp_www sz (w3 o) vs' = ok v' & List.Forall2 svalue_uincl v v'.
Proof.
  split_list => ?????? ok_v; svalue_uincl => h h' h''; rewrite /= h h' h'' /= ok_v.
  eexists; [ reflexivity | exact: svalues_of_values_uincl ].
Qed.

 Lemma svuincl_app_ww8 sz o vs vs' v :
  List.Forall2 svalue_uincl vs vs' →
  (app_ww8 sz o) vs = ok v →
  exists2 v', sapp_ww8 sz (w3 o) vs' = ok v' & List.Forall2 svalue_uincl v v'.
Proof.
  split_list => ?????? ok_v; svalue_uincl => h h' h''; rewrite /= h h' h'' /= ok_v.
  eexists; [ reflexivity | exact: svalues_of_values_uincl ].
Qed.

Lemma svuincl_app_wwb sz o vs vs' v :
  List.Forall2 svalue_uincl vs vs' →
  (app_wwb sz o) vs = ok v →
  exists2 v', sapp_wwb sz (w3 o) vs' = ok v' & List.Forall2 svalue_uincl v v'.
Proof.
  split_list => ?????? ok_v; svalue_uincl => h h'; rewrite /= h h' /= ok_v.
  eexists; [ reflexivity | exact: svalues_of_values_uincl ].
Qed.

Lemma svuincl_app_w4 sz o vs vs' v :
  List.Forall2 svalue_uincl vs vs' →
  (app_w4 sz o) vs = ok v →
  exists2 v', sapp_w4 sz (w4 o) vs' = ok v' & List.Forall2 svalue_uincl v v'.
Proof.
  split_list => ???????? ok_v; svalue_uincl => /= -> -> -> -> /=; rewrite ok_v.
  eexists; [ reflexivity | exact: svalues_of_values_uincl ].
Qed.

Lemma svuincl_app_w8 sz o vs vs' v :
  List.Forall2 svalue_uincl vs vs' →
  (app_w8 sz o) vs = ok v →
  exists2 v', sapp_w8 sz (w2 o) vs' = ok v' & List.Forall2 svalue_uincl v v'.
Proof.
  split_list => ???? ok_v; svalue_uincl => /= -> -> /=; rewrite ok_v.
  eexists; [ reflexivity | exact: svalues_of_values_uincl ].
Qed.

Lemma svuincl_exec_opn o vs vs' v :
  List.Forall2 svalue_uincl vs vs' -> exec_sopn o vs = ok v ->
  exists2 v', ssem_sopn o vs' = ok v' & List.Forall2 svalue_uincl v v'.
Proof.
  rewrite /exec_sopn /ssem_sopn;case: o;
    eauto using svuincl_app_w, svuincl_app_b, svuincl_app_ww, svuincl_app_www,
                svuincl_app_wwb, svuincl_app_w4, svuincl_app_w8, svuincl_app_ww8;
    move => s.
  + by split_list => ???? <-; svalue_uincl => /= -> ->;
    eexists; [ reflexivity | exact: svalues_of_values_uincl ].
  + by split_list => ?????? <-; svalue_uincl => /= -> ->;
    eexists; [ reflexivity | exact: svalues_of_values_uincl ].
  + by split_list => ?????? <-; svalue_uincl => /= -> ->;
    eexists; [ reflexivity | exact: svalues_of_values_uincl ].
  + by split_list => _ _ <-;
    eexists; [ reflexivity | exact: svalues_of_values_uincl ].
  + by move: s; split_list => ?? <-; svalue_uincl => /= ->;
    eexists; [ reflexivity | exact: svalues_of_values_uincl ].
    split_list => _ _ b ?; svalue_uincl.
    case: b; t_xrbindP => ??; svalue_uincl => /= -> <-;
    (eexists; [ reflexivity | exact: svalues_of_values_uincl ]).
  + by split_list => ?? _ _ <-; svalue_uincl => /= ->;
    eexists; [ reflexivity | exact: svalues_of_values_uincl ].
  + by rewrite /x86_vpinsr;
    split_list => ?????? ok_v; svalue_uincl => /= -> -> -> /=;
    eexists; [ reflexivity | exact: svalues_of_values_uincl ].
  by rewrite /x86_vinserti128; move: s;
  split_list => ?????? <-; svalue_uincl => /= -> -> ->;
  eexists; [ reflexivity | exact: svalues_of_values_uincl ].
Qed.

Lemma sset_vm_uincl vm vm' x z z' :
  svm_uincl vm vm' ->
  sval_uincl z z' ->
  svm_uincl (vm.[x <- ok z])%vmap (vm'.[x <- z'])%vmap.
Proof.
  move=> Hvm Hz y; case( x =P y) => [<- | /eqP Hneq];by rewrite ?Fv.setP_eq ?Fv.setP_neq.
Qed.
 
Lemma sset_undef_vm_uincl vm vm' x z :
  svm_uincl vm vm' ->
  svm_uincl (vm.[x <- undef_error])%vmap (vm'.[x <- z])%vmap.
Proof.
  move=> Hvm y; case( x =P y) => [<- | /eqP Hneq];by rewrite ?Fv.setP_eq ?Fv.setP_neq.
Qed.

Lemma sset_var_uincl vm1 vm1' vm2 x v v' :
  svm_uincl vm1 vm1' ->
  svalue_uincl v v' ->
  set_var vm1 x v = ok vm2 ->
  exists vm2', sset_var vm1' x v' = ok vm2' /\ svm_uincl vm2 vm2'.
Proof.
  move=> Hvm Hv; rewrite /set_var /sset_var; apply: on_vuP.
  + move=> z /(of_sval_uincl Hv) [z'] [->] [le] _ <- /=.
    by exists (vm1'.[x <- z'])%vmap;split=>//; apply sset_vm_uincl.
  move/of_val_addr_undef => [ty [under_ty incl_ty]]. subst v.
  case: ifP => //=; move: Hv; rewrite /is_sword => svalue_ty.
  move => a b;  apply ok_inj in  b; subst; move:a.
  rewrite /of_sval; case: x incl_ty => //=.
  case => //= [v | v | s p v]; case E: ty => [||sz px|sz] //=; subst ty.
  + move => _ _; set x := Var _ _; case: v' svalue_ty => //= b svalue_ty.
    exists (vm1'.[x <- b])%vmap; split=> //.
    by apply/sset_undef_vm_uincl.
  + move => _ _; set x := Var _ _; case: v' svalue_ty => //= i svalue_ty.
    exists (vm1'.[x <- i])%vmap; split=> //.
    by apply/sset_undef_vm_uincl.
  + move=> /eqP ? _; subst sz; case: v' svalue_ty => //= s' a [?]; subst s'.
    rewrite eq_dec_refl /=; set x := Var _ _.
    exists (vm1'.[x <- a])%vmap; split=> //.
    by apply/sset_vm_uincl => //= i w h; case: (Array.getP_empty h).
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
  elim: xs s ss vs1 vs2 => /= [ | x xs Hrec] s ss vs1 vs2 Hvm [] //=; first by move=> [] <-;eauto.
  move=> {vs1 vs2} v1 v2 vs1 vs2 Hv Hvs;apply: rbindP => s1'.
  by move=> /(swrite_var_uincl Hvm Hv) [] vm2 [] -> Hvm2 /(Hrec _ _ _ _ Hvm2 Hvs).
Qed.

Lemma svm_state_uincl s ss:
  sestate_uincl s ss ->
  svm_uincl (evm s) (sevm ss).
Proof.
by rewrite /sestate_uincl => [[_ svm] ?].
Qed.

Lemma var_vtype_arr x m sz n (a: Array.array n (word sz)):
  get_var m x = ok (Varr a) ->
  vtype x = sarr sz n.
Proof.
  case E: (vtype x);
  case: x E => //= st vn ->;rewrite /get_var /on_vu //=.
  + by case: (m.[{| vtype := sbool; vname := vn |}])%vmap => //=;case.
  + by case: (m.[{| vtype := sint; vname := vn |}])%vmap => //=;case.
  + case: (m.[{| vtype := sarr _ _ ; vname := vn |}])%vmap => //=.
    * move => a' eq; apply ok_inj in eq;subst;congruence.
    case => //=.
  + by case: (m.[{| vtype := sword _ ; vname := vn |}])%vmap => //=;case.
Qed.

Lemma swrite_uincl s1 s' ss1 r v1 v2:
  sestate_uincl s1 ss1 ->
  svalue_uincl v1 v2 ->
  write_lval gd r v1 s1 = ok s' ->
  exists2 ss',
    swrite_lval gd r v2 ss1 = ok ss' & sestate_uincl s' ss'.
Proof.
  move=> Hs1 Hv;case:r => [xi ty | x | s x p | x p] /=.
  + apply: on_vuP.
    * by move=> w1 h ?; subst; eauto.
    * rewrite /of_val. case:ty => //=; rewrite /to_bool /to_int;
      by case:v1 Hv => //=; case => //=;exists ss1 => //=; apply ok_inj in H0;rewrite -H0.
  + rewrite /write_var /swrite_var;apply: rbindP=> vm2 /=.
    move: Hs1=> [Hmem1 Hvm1].
    rewrite -Hmem1.
    by move=> /(sset_var_uincl Hvm1 Hv) [vm2' [-> ?]] [] <- /=;exists {| semem := mem_to_smem (emem s1); sevm := vm2' |}.
  + t_xrbindP => w v get_s1 point_v w' v' sem_s1 point_v' w2 trad_v1 m write_m mem_s'; subst.
    have := ssem_pexpr_uincl_r Hs1 sem_s1.
    move => [vb ssem_p]; rewrite ssem_p => //=.
    move => /svalue_uincl_word -/(_ _ _ point_v').
    case => sz2 sz2' wsz2 wsz2' trunc_wsz2' val_v' val_vb;subst.  
    have uincl_v_evms1 : svalue_uincl v (sget_var (sevm ss1) x)
      by apply: (@sget_var_uincl _ _ (sevm ss1) _ _ get_s1); apply svm_state_uincl.
    move:uincl_v_evms1 => /svalue_uincl_word -/(_ _ _ point_v).
    case => sz sz' wsz wsz' trunc_wsz trad_v get_x //=.
    rewrite /sto_pointer /sto_word trunc_wsz trunc_wsz2' => //=.
    move:Hv => /svalue_uincl_word /(_ trad_v1).
    case => sf sf' wf wf' trunc_wf' trad_wf trad_wf';subst.
    rewrite trunc_wf' => //=.
    eexists => //=.
    rewrite /sestate_uincl.
    have svm_incl := svm_state_uincl Hs1 => //=.
    have := mem2smem_write write_m => ->.
    rewrite /svm_uincl in svm_incl.
    by move:Hs1 => [-> _].
  rewrite /on_arr_var; t_xrbindP; case => //= s n a get_x.
  have vtype_x := var_vtype_arr get_x.
  t_xrbindP => i vi sem_p val_vi w trad_v1 a2 set_a2_w vm setvar ?; subst;rewrite /son_arr_var.
  case: x get_x setvar vtype_x => -[] [] //= w' p' xn _.
  set x := Var _ _; move=> get_x setvar [??]; subst w' p'.
  case: (svalue_uincl_word Hv trad_v1) => sz sz' wsz wsz' trunc ? ?;subst v1 v2.
  rewrite /sto_word; rewrite trunc {trunc}.
  have := ssem_pexpr_uincl_r Hs1 sem_p;move => [v' -> uincl_viv'] //=.
  have :=svalue_uincl_int uincl_viv' val_vi => {uincl_viv'};move => [? ?];subst => //=.
  rewrite /x /sset_var /= eq_dec_refl /=.
  set ss' := SEstate _ _; exists ss' => //.
  split; first by rewrite /ss' /=; case: Hs1.
  move=> y; rewrite /ss' /=; case: (x =P y) => [<-|/eqP ne_xy]; last first.
  + rewrite Fv.setP_neq //; case: Hs1 => _ /(_ y).
    suff ->: ((evm s1).[y] = vm.[y])%vmap by apply.
    elim/set_varP: setvar => //=;by move=> ? _ <-; rewrite Fv.setP_neq.
  + rewrite Fv.setP_eq /= -/x => {ss'}; elim/set_varP: setvar.
    * move=> t tE <-; rewrite Fv.setP_eq /= => z v.
      move: t tE; rewrite /x /= => a3.
      rewrite eq_dec_refl pos_dec_n_n => -[?] get_z; subst a3.
      rewrite FArray.setP; case: eqP => [|/eqP neq_iz].
      * move=> ?; subst z; move: set_a2_w; rewrite /Array.set.
        case: ifP => //= _ -[?]; subst a2.
        move: get_z; rewrite /Array.get; case: ifP => _ //=.
        by rewrite FArray.setP_eq => -[].
      * rewrite -/x; elim/on_vuP: get_x => //= t tE.
        case: Hs1 => _ /(_ x); rewrite {}tE /= => h /Varr_inj1 ?;subst; apply h.
        move: set_a2_w get_z; rewrite /Array.set.
        case: ifP => // _ [] <- /=; rewrite /Array.get.
        by case: ifP => // _; rewrite FArray.setP_neq.
    * by move => _; rewrite /x //= eq_dec_refl pos_dec_n_n.
Qed.

Lemma swrites_uincl s s' ss r v1 v2:
  sestate_uincl s ss ->
  List.Forall2 svalue_uincl v1 v2 ->
  write_lvals gd s r v1 = ok s' ->
  exists2 ss',
    swrite_lvals gd ss r v2 = ok ss' &
    sestate_uincl s' ss'.
Proof.
  elim: r v1 v2 s ss=> [|r rs Hrec] v1 v2 s ss Hs /= [] //=; first by move=> [] <-; exists ss.
  move=> {v1 v2} v1 v2 vs1 vs2 Hv Hforall.
  apply: rbindP=> z /(swrite_uincl Hs Hv) [] x -> Hz.
  by move=> /(Hrec _ _ _ _ Hz Hforall).
Qed.

End GLOB_DEFS.
(* -------------------------------------------------------------------- *)
Section SEM.

Variable (p:prog).
Notation gd := (p_globs p).

Let Pc s1 c s2 :=
  forall ss1,
    sestate_uincl s1 ss1 -> exists ss2, ssem p ss1 c ss2 /\ sestate_uincl s2 ss2.

Let Pi_r s1 c s2 :=
  forall ss1,
    sestate_uincl s1 ss1 -> exists ss2, ssem_i p ss1 c ss2 /\ sestate_uincl s2 ss2.

Let Pi s1 c s2 :=
  forall ss1,
    sestate_uincl s1 ss1 -> exists ss2, ssem_I p ss1 c ss2 /\ sestate_uincl s2 ss2.

Let Pfor i zs s1 c s2 :=
  forall ss1,
    sestate_uincl s1 ss1 -> exists ss2, ssem_for p i zs ss1 c ss2 /\ sestate_uincl s2 ss2.

Let Pfun m1 fd vargs m2 vres :=
  forall vargs', List.Forall2 svalue_uincl vargs vargs' ->
    exists vres',
    ssem_call p (mem_to_smem m1) fd vargs' (mem_to_smem m2) vres' /\
    List.Forall2 svalue_uincl vres vres'.

Local Lemma Hnil : sem_Ind_nil Pc.
Proof. by move=> s vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

Local Lemma Hcons : sem_Ind_cons p Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ Hi _ Hc vm1 /Hi [vm2 []] Hsi /Hc [vm3 []] Hsc ?.
  by exists vm3;split=>//;econstructor;eauto.
Qed.

Local Lemma HmkI : sem_Ind_mkI p Pi_r Pi.
Proof. by move=> ii i s1 s2 _ Hi vm1 /Hi [vm2 []] Hsi ?;exists vm2. Qed.

Local Lemma Hasgn : sem_Ind_assgn p Pi_r.
Proof.
  move => s1 s2 x tag st e v v' sem_e.
  move => trunc_v write_v' s1' uincl_s1'.
  have := ssem_pexpr_uincl uincl_s1' sem_e trunc_v.
  move => [v2] [v2'] [ssem_e] [trunc_v2 uincl_v2'].
  have := (swrite_uincl uincl_s1' uincl_v2' write_v')=>  [] [ss2' write_v2'] uincl_ss2'; exists ss2';split => //=.
  by have := (SEassgn tag ssem_e trunc_v2 write_v2').
Qed.

Local Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move=> s1 s2 t o xs es H vm1 Hvm1; apply: rbindP H => rs;apply: rbindP => vs.
  move=> /(ssem_pexprs_uincl Hvm1) [] vs' [] H1 H2.
  move=> /(svuincl_exec_opn H2) [] rs' H3 H4.
  move=> /(swrites_uincl Hvm1 H4) [] vm2 ??.
  exists vm2;split => //;constructor.
  by rewrite H1 /= H3.
Qed.

Local Lemma Hif_true : sem_Ind_if_true p Pc Pi_r.
Proof.
  move => s1 s2 e c1 c2 H1 _ Hc vm1 Hvm1.
  have {H1} [v' H1] := ssem_pexpr_uincl_r Hvm1 H1.
  move => /(svalue_uincl_bool) /(_ erefl) [_ ?]; subst.
  have [vm2 [??]]:= Hc _ Hvm1; exists vm2; split => //.
  by apply SEif_true; rewrite // H1.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p Pc Pi_r.
Proof.
  move => s1 s2 e c1 c2 H _ Hc vm1 Hvm1.
  have [v' H1] := ssem_pexpr_uincl_r Hvm1 H.
  move => /svalue_uincl_bool /(_ erefl) [_ ?]; subst.
  have [vm2 [??]]:= Hc _ Hvm1;exists vm2;split=>//.
  by apply SEif_false;rewrite // H1.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p Pc Pi_r.
Proof.
  move => s1 s2 s3 s4 c e c' _ Hc H _ Hc' _ Hw vm1 Hvm1.
  have [vm2 [Hs2 Hvm2]] := Hc _ Hvm1.
  have [v' H1] := ssem_pexpr_uincl_r Hvm2 H.
  move=> /svalue_uincl_bool /(_ erefl) [_ ?]; subst.
  have [vm3 [H4 /Hw [vm4] [??]]]:= Hc' _ Hvm2;exists vm4;split => //.
  by eapply SEwhile_true;eauto;rewrite H1.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p Pc Pi_r.
Proof.
  move => s1 s2 c e c' _ Hc h vm1 Hvm1.
  have [vm2 [Hs2 Hvm2]] := Hc _ Hvm1.
  have [v' H1] := ssem_pexpr_uincl_r Hvm2 h.
  move => /(svalue_uincl_bool) /(_ erefl) [_ ?]; subst.
  by exists vm2;split=> //;apply: SEwhile_false=> //;rewrite H1.
Qed.

Local Lemma Hfor : sem_Ind_for p Pi_r Pfor.
Proof.
  move => s1 s2 i d lo hi c vlo vhi H H' _ Hfor vm1 Hvm1.
  have [? H1] := ssem_pexpr_uincl_r Hvm1 H.
  move=> /svalue_uincl_int /(_ erefl) [_ ?]; subst.
  have [? H3] := ssem_pexpr_uincl_r Hvm1 H'.
  move=> /svalue_uincl_int /(_ erefl) [_ ?]; subst.
  have [vm2 []??]:= Hfor _ Hvm1; exists vm2;split=>//.
  by econstructor;eauto;rewrite ?H1 ?H3.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof. by move=> s i c vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p Pc Pfor.
Proof.
  move=> s1 s1' s2 s3 i w ws c Hi _ Hc _ Hf vm1 Hvm1.
  have [//|vm1' [Hi' /Hc]] := @swrite_var_uincl _ _ _ _ (SVint w) _ Hvm1 _ Hi.
  move=> [vm2 [Hsc /Hf]] [vm3 [Hsf Hvm3]];exists vm3;split => //.
  by econstructor;eauto.
Qed.
 
Local Lemma Hcall : sem_Ind_call p Pi_r Pfun.
Proof.
  move=> s1 m2 s2 ii xs fn args vargs vs Hargs Hcall Hfd Hxs s Hs.
  have [vargs' [Hsa /Hfd Hc]]:= ssem_pexprs_uincl Hs Hargs.
  have Hvm1: sestate_uincl {| emem := m2; evm := evm s1 |} {| semem := mem_to_smem m2; sevm := sevm s |}.
  * split=> //.
    by move: Hs=> [_ ?].
  move: Hc=> [vres' [Hvres'1 Hvres'2]].
  have [vm2' ??]:= swrites_uincl Hvm1 Hvres'2 Hxs.
  exists vm2';split=>//;econstructor;eauto.
  by rewrite (proj1 Hvm1) (proj1 Hs) in Hvres'1.
Qed.
  
Lemma mapM2_truncate_val tys vs1' vs1 vs2' : 
  mapM2 ErrType truncate_val tys vs1' = ok vs1 ->
  List.Forall2 svalue_uincl vs1' vs2' ->
  exists vs2, mapM2 ErrType truncate_sval (sstypes_of_stypes tys) vs2' = ok vs2 /\ 
    List.Forall2 svalue_uincl vs1 vs2.
Proof.
  elim: tys vs1' vs1 vs2' => [ | t tys hrec] [|v1' vs1'] //=.
  + by move => ? ? [<-] /List_Forall2_inv_l ->; eauto.
  move=> vs1 vs2';t_xrbindP => v1 htr vs2 htrs <- /List_Forall2_inv_l [v] [vs] [->] [hv hvs].
  have temp := psem.truncate_value_uincl.
  have [v2 [-> hv2] /=]:= truncate_svalue_uincl hv htr.
  by have [vs2'' [-> hvs2] /=] := hrec _ _ _ htrs hvs;eauto.
Qed.

Lemma Hproc2 : sem_Ind_proc p Pc Pfun.
Proof.
  move => m1 m2 fn f vargs vargs' s vm2 vres vres'.
  move => Hget HM2 Hwrite Hsem HPc HmapM Htrunc.
  rewrite /Pfun => vargs2 Huincl_vargs2.
  have := mapM2_truncate_val HM2 Huincl_vargs2 => [] [vargs2'] [HM2_vargs2] Huincl_vargs2'.

  have Hss0: sestate_uincl {| emem := m1; evm := vmap0 |} {| semem := mem_to_smem m1; sevm := svmap0 |}.
  * split=> //=.
    rewrite /vmap0 /svmap0 /svm_uincl.
    move=> [vi v] /=.
    rewrite /sval_uincl.
    case: vi => // p0 i v0.
    rewrite /Array.get /FArray.get.
    case: ifP=> //.
  have := swrite_vars_uincl Hss0 Huincl_vargs2' Hwrite => [] [ss] [Hwrite_vargs2'] Huincl_s_ss.
  have := HPc ss Huincl_s_ss => [] [ss'] //= [Hssem_ss'] Huincl_ss'.
  set vres2 := (map (fun x : var_i => sget_var ss'.(sevm) x) (f_res f)).
  have  Huincl_vres2 : List.Forall2 svalue_uincl vres vres2.
  * rewrite /vres2.
    move:Huincl_ss' => [Hmem_ss'] Hsvm_ss'.
    by have := sget_vars_uincl Hsvm_ss' HmapM.
  have Hval_ss': {| semem := mem_to_smem m2; sevm := sevm ss' |} = ss'.
  * move:ss' Hssem_ss' Huincl_ss' vres2 Huincl_vres2 => [ss'_1 ss'_2] Hssem_ss' Huincl_ss' vres2 Huincl_vres2.
    by rewrite (proj1 Huincl_ss').
  rewrite -Hval_ss' in Hssem_ss'.
  have := mapM2_truncate_val Htrunc Huincl_vres2 => [] [vres2'] [HM2_vres2] Huincl_vres2'.
  have Hssem_vres2' : ssem_call p (mem_to_smem m1) fn vargs2 (mem_to_smem m2) vres2' .
  * by apply: SEcallRun Hget HM2_vargs2 Hwrite_vargs2' Hssem_ss' _ HM2_vres2.
  exists vres2';split=> //=.
Qed.

Lemma sem_uincl s1 c s2 ss1 :
  sestate_uincl s1 ss1 ->
  sem p s1 c s2 ->
  exists ss2,
    ssem p ss1 c ss2 /\
    sestate_uincl s2 ss2.
Proof.
  move=> H1 H2.
  apply : (@sem_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc2); eassumption.
Qed.

End SEM.


