From elpi.apps Require Import derive.std.
From Coq Require Import ZArith.
From Coq Require Export String.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice.
Require Import utils gen_map.

(* -------------------------------------------------------------------- *)
#[only(eqbOK)] derive Ascii.ascii.
(* ascii_eqb :  Ascii.ascii ->  Ascii.ascii -> bool *)
(* ascii_eqb_OK *)

HB.instance Definition _ := hasDecEq.Build Ascii.ascii ascii_eqb_OK.
HB.instance Definition _ := Countable.copy Ascii.ascii
  (can_type Ascii.ascii_nat_embedding).

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
#[only(eqbOK)] derive string.
(* string_eqb is defined
   string_eqb_OK is defined *)

HB.instance Definition _ := hasDecEq.Build string string_eqb_OK.

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

  Definition t : eqType := string.

  Definition cmp : t -> t -> comparison := string_cmp.

  Definition cmpO : Cmp cmp := stringO.

End CmpString.

Module Ms := Mmake CmpString.
Declare Scope mstring_scope.
Delimit Scope mstring_scope with ms.
Notation "m .[ x ]" := (@Ms.get _ m x) : mstring_scope.
Notation "m .[ x  <- v ]" := (@Ms.set _ m x v) : mstring_scope.
Arguments Ms.get T%_type_scope m%_mstring_scope k.
Arguments Ms.set T%_type_scope m%_mstring_scope k v.

