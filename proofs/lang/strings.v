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

(* -------------------------------------------------------------------- *)
Require Import ZArith.
Require Export String.
From mathcomp Require Import all_ssreflect.
Require Import utils gen_map.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Scheme Equality for Ascii.ascii.
(* ascii_beq :  Ascii.ascii ->  Ascii.ascii -> bool *)
(* ascii_eq_dec *)

Lemma ascii_eqP : Equality.axiom ascii_beq. 
Proof. 
  move=> x y;apply:(iffP idP).
  + by apply: internal_ascii_dec_bl.
  by apply: internal_ascii_dec_lb.
Qed.

Definition ascii_eqMixin := EqMixin ascii_eqP.
Canonical  ascii_eqType  := EqType Ascii.ascii ascii_eqMixin.

Definition ascii_choiceMixin := CanChoiceMixin Ascii.ascii_nat_embedding.
Canonical  ascii_choiceType  := ChoiceType Ascii.ascii ascii_choiceMixin.

Definition ascii_countMixin := CanCountMixin Ascii.ascii_nat_embedding.
Canonical  ascii_countType  := CountType Ascii.ascii ascii_countMixin.

Definition ascii_cmp (c c': Ascii.ascii) := 
  match c, c' with
  | Ascii.Ascii b1  b2  b3  b4  b5  b6  b7  b8,
    Ascii.Ascii b1' b2' b3' b4' b5' b6' b7' b8' =>
     Lex (bool_cmp b1 b1')
    (Lex (bool_cmp b2 b2')
    (Lex (bool_cmp b3 b3')
    (Lex (bool_cmp b4 b4')
    (Lex (bool_cmp b5 b5')
    (Lex (bool_cmp b6 b6')
    (Lex (bool_cmp b7 b7') (bool_cmp b8 b8')))))))
  end.

Instance asciiO : Cmp ascii_cmp.
Proof.
  constructor=> [[]????????| []???????? []???????? | []????????][] ???????? /=;
    rewrite !Lex_lex. 
  + by apply @cmp_sym; do !(apply LexO;[apply boolO | ]);apply boolO. 
  + by move=> c;apply @cmp_ctrans; do !(apply LexO;[apply boolO | ]);apply boolO. 
  do !move=> /lex_eq [] /= /(@cmp_eq _ _ boolO) ->.
  by move=> /(@cmp_eq _ _ boolO) ->.
Qed.

(* -------------------------------------------------------------------- *)
Scheme Equality for String.string.
(* string_beq is defined
   string_eq_dec is defined *)

Lemma string_eqP : Equality.axiom string_beq. 
Proof. 
  move=> x y;apply:(iffP idP).
  + by apply: internal_string_dec_bl.
  by apply: internal_string_dec_lb.
Qed.

Definition string_eqMixin := EqMixin string_eqP.
Canonical  string_eqType  := EqType string string_eqMixin.

Fixpoint string_cmp s1 s2 := 
  match s1, s2 with
  | EmptyString , String _  _  => Lt
  | EmptyString , EmptyString  => Eq
  | String c1 s1, String c2 s2 => Lex (ascii_cmp c1 c2) (string_cmp s1 s2)
  | String _  _ , EmptyString  => Gt
  end.

Instance stringO: Cmp string_cmp.
Proof.
  constructor. 
  + elim=> [ | c1 s1 Hs1] [ | c2 s2] //=.
    rewrite !Lex_lex;apply lex_sym. apply asciiO. apply Hs1.
  + move=> y x;elim:x y => [ | cx sx Hs] [ | cy sy] [ | cz sz] c //=; try by apply ctrans_Eq.
    + by apply ctrans_Lt. + by apply ctrans_Gt.
    rewrite !Lex_lex;apply lex_trans;[apply cmp_ctrans | apply Hs].
  elim=> [ | c1 s1 Hs1] [ | c2 s2] //=.
  by rewrite Lex_lex=> /lex_eq /= [] /(@cmp_eq _ _ asciiO) -> /Hs1 ->. 
Qed.



(* -------------------------------------------------------------------- *)

Fixpoint code (s : string) :=
  if s is String a s then a :: code s else [::].

Fixpoint decode (s : seq Ascii.ascii) :=
  if s is a :: s then String a (decode s) else EmptyString.

Lemma codeK : cancel code decode.
Proof. by elim=> //= a s ->. Qed.

Definition string_choiceMixin := CanChoiceMixin codeK.
Canonical  string_choiceType  := ChoiceType string string_choiceMixin.

Definition string_countMixin := CanCountMixin codeK.
Canonical  string_countType  := CountType string string_countMixin.


(* -------------------------------------------------------------------- *)
(*
Definition a2P_app c n := 
  match c with
  | Ascii.Ascii b1 b2 b3 b4 b5 b6 b7 b8 =>
    b2P_app b1 (b2P_app b2 (b2P_app b3 (b2P_app b4
      (b2P_app b5 (b2P_app b6 (b2P_app b7 (b2P_app b8 n)))))))
  end.

Definition a2P c := a2P_app c xH.

Lemma a2P_appP c n : a2P_app c n = FMapPositive.append (a2P c) n.
Proof. by case: c=> * => /=;rewrite !b2P_appP -!appendA. Qed.

Lemma log_a2P c : log_inf (a2P c) = 8%Z.
Proof. by case: c=> * /=;rewrite !log_b2P_app. Qed.

Lemma a2P_app_inj c1 c2 n1 n2 : a2P_app c1 n1 = a2P_app c2 n2 -> c1 = c2 /\ n1 = n2.
Proof. 
  case: c1 => ???? ????; case: c2 => ???? ???? /=.
  by do !(move=> /b2P_app_inj [] ->).
Qed.

Fixpoint s2P_app s n:= 
  match s with
  | EmptyString => n
  | String c s => s2P_app s (a2P_app c n)
  end.

Definition s2P s := s2P_app s xH.

Lemma s2P_appP s n : s2P_app s n = FMapPositive.append (s2P s) n.
Proof. 
  elim: s n => [ | c s Hs] n //=.
  by rewrite /s2P /= !Hs /= a2P_appP -!appendA. 
Qed.
  
Lemma s2P_app_inj s1 s2 n1 n2: 
  log_inf n1 = log_inf n2 ->
  s2P_app s1 n1 = s2P_app s2 n2 -> s1 = s2 /\ n1 = n2.
Proof.
  elim: s1 s2 n1 n2 => [ | c1 s1 Hs1] [ | c2 s2] //= n1 n2 Hlog.
  + move=> Heq;move:Hlog;rewrite Heq.
    rewrite s2P_appP a2P_appP !log_app log_a2P=> ?.
    by have ?:= log_inf_correct1 (s2P s2);omega.
  + move=> Heq;move:Hlog;rewrite -Heq.
    rewrite s2P_appP a2P_appP !log_app log_a2P=> ?.
    by have ?:= log_inf_correct1 (s2P s1);omega.
  move=> /Hs1 [].
  + by rewrite !a2P_appP !log_app !log_a2P Hlog.
  by move=> -> /a2P_app_inj [] -> ->.
Qed.

Lemma s2P_inj : injective s2P.
Proof. by move=> s1 s2;rewrite /s2P => /s2P_app_inj []. Qed.

Module InjString.

  Definition t := [eqType of string].

  Definition t2P := s2P.
 
  Definition t2P_inj := s2P_inj.

End InjString.
*)

Module CmpString.

  Definition t : eqType := [eqType of string].

  Definition cmp : t -> t -> comparison := string_cmp.

  Definition cmpO : Cmp cmp := stringO.
  
End CmpString.

Module Ms := Mmake CmpString.
Delimit Scope mstring_scope with ms.
Notation "m .[ x ]" := (@Ms.get _ m x) : mstring_scope.
Notation "m .[ x  <- v ]" := (@Ms.set _ m x v) : mstring_scope.
Arguments Ms.get T%type_scope m%mstring_scope k.
Arguments Ms.set T%type_scope m%mstring_scope k v.
 