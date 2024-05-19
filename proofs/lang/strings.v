Require Import ZArith.
Require Export String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice.
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
  exact: (eq_axiom_of_scheme internal_ascii_dec_bl internal_ascii_dec_lb).
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

#[global]
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
  exact: (eq_axiom_of_scheme internal_string_dec_bl internal_string_dec_lb).
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

#[global]
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

Module CmpString.

  Definition t : eqType := [eqType of string].

  Definition cmp : t -> t -> comparison := string_cmp.

  Definition cmpO : Cmp cmp := stringO.

End CmpString.

Module Ms := Mmake CmpString.
Declare Scope mstring_scope.
Delimit Scope mstring_scope with ms.
Notation "m .[ x ]" := (@Ms.get _ m x) : mstring_scope.
Notation "m .[ x  <- v ]" := (@Ms.set _ m x v) : mstring_scope.
Arguments Ms.get T%type_scope m%mstring_scope k.
Arguments Ms.set T%type_scope m%mstring_scope k v.

