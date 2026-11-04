From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Import gen_map utils strings.
Require Import wsize.
Require Import type.
Import Utf8.
Notation lword8   := (lword U8).
Notation lword16  := (lword U16).
Notation lword32  := (lword U32).
Notation lword64  := (lword U64).
Notation lword128 := (lword U128).
Notation lword256 := (lword U256).
Notation ty_msf := (aword msf_size).
Notation cty_msf := (cword msf_size).

Lemma is_aboolP t : reflect (t=abool) (is_abool t).
Proof. by case: t => /=; constructor. Qed.

Lemma is_aarrP ty : reflect (exists ws n, ty = aarr ws n) (is_aarr ty).
Proof. by case: ty; constructor; eauto => -[?] [?]. Qed.

Lemma is_word_typeP ty ws :
  is_word_type ty = Some ws -> ty = aword ws.
Proof. by case: ty => //= w [->]. Qed.

Lemma gt0_arr_size ws len : (0 < len)%Z -> (0 < arr_size ws len)%Z.
Proof. by move=> ?; rewrite arr_sizeE; apply Z.mul_pos_pos. Qed.

Lemma convertible_sym ty1 ty2 : convertible ty1 ty2 -> convertible ty2 ty1.
Proof.
  case: ty1 ty2 => [||ws1 n1|ws1] [||ws2 n2|ws2] //=.
  + by rewrite eq_sym.
  by rewrite eq_sym.
Qed.

Lemma convertible_trans ty2 ty1 ty3 :
  convertible ty1 ty2 -> convertible ty2 ty3 -> convertible ty1 ty3.
Proof.
  case: ty1 ty2 => [||ws1 n1|ws1] [||ws2 n2|ws2] //=.
  + by move=> /eqP ->.
  by move=> /eqP ->.
Qed.

Lemma convertible_eval_atype ty1 ty2 :
  convertible ty1 ty2 ->
  eval_atype ty1 = eval_atype ty2.
Proof.
  case: ty1 ty2 => [||ws1 n1|ws1] [||ws2 n2|ws2] //=.
  + by move=> /eqP <-.
  by move=> /eqP [<-].
Qed.

Lemma all2_convertible_eval_atype tys1 tys2 :
  all2 convertible tys1 tys2 ->
  map eval_atype tys1 = map eval_atype tys2.
Proof.
  elim: tys1 tys2 => [|ty1 tys1 ih1] [|ty2 tys2] //=.
  by move=> /andP [/convertible_eval_atype -> /ih1 ->].
Qed.

Lemma subatypeE ty ty' :
  subatype ty ty' →
  match ty' return Prop with
  | aword sz' => ∃ sz, ty = aword sz ∧ (sz ≤ sz')%CMP
  | _         => convertible ty ty'
end.
Proof.
  case: ty => [||ws n|ws]; try by move/eqP => <-.
  + by case: ty'.
  by case: ty' => //; eauto.
Qed.

Lemma subatypeEl ty ty' :
  subatype ty ty' →
  match ty return Prop with
  | aword sz => ∃ sz', ty' = aword sz' ∧ (sz ≤ sz')%CMP
  | _        => convertible ty ty'
  end.
Proof.
  case: ty => [||ws n|ws] //=.
  by case: ty' => //; eauto.
Qed.

Lemma subatype_trans ty2 ty1 ty3 :
  subatype ty1 ty2 -> subatype ty2 ty3 -> subatype ty1 ty3.
Proof.
  case: ty1 => //= [/eqP<-|/eqP<-|ws1 n1|ws1] //.
  + by case: ty2 => //= ws2 n2 /eqP ->.
  by case: ty2 => //= ws2 hle; case: ty3 => //= ws3; apply: cmp_le_trans hle.
Qed.

Lemma is_aword_subatype t1 t2 : subatype t1 t2 -> is_aword t1 = is_aword t2.
Proof.
  by case: t1 => //= [/eqP <-|/eqP <-|??|?] //; case:t2.
Qed.

Lemma subctypeE ty ty' :
  subctype ty ty' →
  match ty' with
  | cword sz' => ∃ sz, ty = cword sz ∧ (sz ≤ sz')%CMP
  | _         => ty = ty'
end.
Proof.
  case: ty => [||n|ws]; try by move/eqP => <-.
  by case: ty' => //; eauto.
Qed.

Lemma subatype_subctype ty1 ty2 :
  subatype ty1 ty2 ->
  subctype (eval_atype ty1) (eval_atype ty2).
Proof.
  case: ty1 ty2 => [||ws1 n1|ws1] [||ws2 n2|ws2] //=.
  by move=> /eqP <-.
Qed.
