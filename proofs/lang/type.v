(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith gen_map utils strings.
Require Export wsize.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom array_length_abstract : Type.
Inductive array_length :=
| AL_const : positive -> array_length
| AL_abstract : array_length_abstract -> array_length.
Definition const_length : positive -> array_length := AL_const.
Axiom array_length_abstract_beq : rel array_length_abstract.
Definition array_length_beq len1 len2 :=
  match len1, len2 with
  | AL_const p1, AL_const p2 => Pos.eqb p1 p2
  | AL_abstract a1, AL_abstract a2 => array_length_abstract_beq a1 a2
  | _, _ => false
  end.
Axiom array_length_abstract_eq_axiom : Equality.axiom array_length_abstract_beq.
Lemma array_length_eq_axiom : Equality.axiom array_length_beq.
Proof.
  move=> [ p1 | a1 ] [ p2 | a2 ] /=; try by constructor.
  + case: Pos.eqb_spec; constructor; congruence.
  case: array_length_abstract_eq_axiom; constructor; congruence.
Qed.
Definition array_length_abstract_eqMixin := Equality.Mixin array_length_abstract_eq_axiom.
Definition array_length_eqMixin := Equality.Mixin array_length_eq_axiom.
Canonical  array_length_abstract_eqType := Eval hnf in EqType array_length_abstract array_length_abstract_eqMixin.
Canonical  array_length_eqType  := Eval hnf in EqType array_length array_length_eqMixin.
Axiom array_length_abstract_cmp : array_length_abstract -> array_length_abstract -> comparison.
Definition array_length_cmp len1 len2 :=
  match len1, len2 with
  | AL_const p1, AL_const p2 => Pos.compare p1 p2
  | AL_const _, _ => Lt
  | _, AL_const _ => Gt
  | AL_abstract a1, AL_abstract a2 => array_length_abstract_cmp a1 a2
  end.
#[export] Declare Instance array_length_abstractO : Cmp array_length_abstract_cmp.
#[export] Instance array_lengthO : Cmp array_length_cmp.
Proof.
  split.
  + move=> [ p1 | a1 ] [ p2 | a2 ] //=.
    + apply positiveO.
    apply array_length_abstractO.
  + move=> [ p1 | a1 ] [ p2 | a2 ] [ p3 | a3 ] //=;
      try (by apply ctrans_Eq);eauto using ctrans_Lt, ctrans_Gt; apply cmp_ctrans.
  move=> [ p1 | a1 ] [ p2 | a2 ] //= h.
  + by rewrite (@cmp_eq _ _ positiveO _ _ h).
  by rewrite (@cmp_eq _ _ array_length_abstractO _ _ h).
Qed.
(* Definition array_length_dec len1 len2 := Bool.reflect_dec _ _ (array_length_eq_axiom len1 len2). *)
Axiom array_length_abstract_dec : forall (p1 p2:array_length_abstract), {p1 = p2} + {True}.
Axiom array_length_abstract_dec_r : forall n1 n2 tt, array_length_abstract_dec n1 n2 = right tt -> n1 != n2.

(* ** Syntax
 * -------------------------------------------------------------------- *)

Variant stype : Type :=
| sbool
| sint
| sarr  of array_length
| sword of wsize.

(* -------------------------------------------------------------------- *)
(*
Definition string_of_stype (ty: stype) : string :=
  match ty with
  | sbool => "sbool"
  | sint => "sint"
  | sarr n => "(sarr " ++ " ?)"
  | sword sz => "(sword " ++ string_of_wsize sz ++ ")"
  end.
*)

(* -------------------------------------------------------------------- *)
Notation sword8   := (sword U8).
Notation sword16  := (sword U16).
Notation sword32  := (sword U32).
Notation sword64  := (sword U64).
Notation sword128 := (sword U128).
Notation sword256 := (sword U256).

(* -------------------------------------------------------------------- *)

Definition stype_beq (ty1 ty2 : stype) :=
  match ty1, ty2 with
  | sbool, sbool => true
  | sint, sint => true
  | sarr len1, sarr len2 => len1 == len2
  | sword ws1, sword ws2 => ws1 == ws2
  | _, _ => false
  end.

Lemma stype_axiom : Equality.axiom stype_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + case: x; case: y => //=.
    + move=> len1 len2 /eqP. congruence.
    move=> ?? /eqP. congruence.
  move=> <-. by case: x => //=.
Qed.

Definition stype_eqMixin     := Equality.Mixin stype_axiom.
Canonical  stype_eqType      := Eval hnf in EqType stype stype_eqMixin.


(* ** Comparison
 * -------------------------------------------------------------------- *)

Definition stype_cmp t t' :=
  match t, t' with
  | sbool   , sbool         => Eq
  | sbool   , _             => Lt

  | sint    , sbool         => Gt
  | sint    , sint          => Eq
  | sint    , _             => Lt

  | sword _ , sarr _        => Lt
  | sword w , sword w'      => wsize_cmp w w'
  | sword _ , _             => Gt

  | sarr n  , sarr n'        => array_length_cmp n n'
  | sarr _  , _             => Gt
  end.

#[global]
Instance stypeO : Cmp stype_cmp.
Proof.
  constructor.
  + by case => [||n|w] [||n'|w'] //=; apply cmp_sym.
  + by move=> y x; case: x y=> [||n|w] [||n'|w'] [||n''|w''] c//=;
       try (by apply ctrans_Eq);eauto using ctrans_Lt, ctrans_Gt; apply cmp_ctrans.
  case=> [||n|w] [||n'|w'] //= h.
  + by rewrite (@cmp_eq _ _ array_lengthO _ _ h).
  by rewrite (@cmp_eq _ _ wsizeO _ _ h).
Qed.

Module CmpStype.

  Definition t : eqType := [eqType of stype].

  Definition cmp : t -> t -> comparison := stype_cmp.

  Definition cmpO : Cmp cmp := stypeO.

End CmpStype.

Module CEDecStype.

  Definition t := [eqType of stype].

  Fixpoint pos_dec (p1 p2:positive) : {p1 = p2} + {True} :=
    match p1 as p1' return {p1' = p2} + {True} with
    | xH =>
      match p2 as p2' return {xH = p2'} + {True} with
      | xH => left (erefl xH)
      | _  => right I
      end
    | xO p1' =>
      match p2 as p2' return {xO p1' = p2'} + {True} with
      | xO p2' =>
        match pos_dec p1' p2' with
        | left eq =>
          left (eq_rect p1' (fun p => xO p1' = xO p) (erefl (xO p1')) p2' eq)
        | _ => right I
        end
      | _ => right I
      end
    | xI p1' =>
      match p2 as p2' return {xI p1' = p2'} + {True} with
      | xI p2' =>
        match pos_dec p1' p2' with
        | left eq =>
          left (eq_rect p1' (fun p => xI p1' = xI p) (erefl (xI p1')) p2' eq)
        | _ => right I
        end
      | _ => right I
      end
    end.

  Definition array_length_dec (len1 len2 : array_length) : {len1 = len2} + {True} :=
    match len1 return { len1 = len2 } + {True} with
    | AL_const n1 =>
      match len2 with
      | AL_const n2 =>
        match pos_dec n1 n2 with
        | left eqn => left (f_equal AL_const eqn)
        | right _ => right I
        end
      | _ => right I
      end
    | AL_abstract a1 =>
      match len2 return _ with
      | AL_const _ => right I
      | AL_abstract a2 =>
        match array_length_abstract_dec a1 a2 with
        | left eqn => left (f_equal AL_abstract eqn)
        | right _ => right I
        end
      end
    end.

  Definition eq_dec (t1 t2:t) : {t1 = t2} + {True} :=
    match t1 as t return {t = t2} + {True} with
    | sbool =>
      match t2 as t0 return {sbool = t0} + {True} with
      | sbool => left (erefl sbool)
      | _     => right I
      end
    | sint =>
      match t2 as t0 return {sint = t0} + {True} with
      | sint => left (erefl sint)
      | _     => right I
      end
    | sarr n1 =>
      match t2 as t0 return {sarr n1 = t0} + {True} with
      | sarr n2 =>
        match array_length_dec n1 n2 with
        | left eqn => left (f_equal sarr eqn)
        | right _ => right I
        end
      | _          => right I
      end
    | sword w1 =>
      match t2 as t0 return {sword w1 = t0} + {True} with
      | sword w2 =>
        match wsize_eq_dec w1 w2 with
        | left eqw => left (f_equal sword eqw)
        | right _ => right I
        end
      | _     => right I
      end
    end.

  Lemma pos_dec_r n1 n2 tt: pos_dec n1 n2 = right tt -> n1 != n2.
  Proof.
    case: tt.
    elim: n1 n2 => [n1 Hrec|n1 Hrec|] [n2|n2|] //=.
    + by case: pos_dec (Hrec n2) => //= -[] /(_ (erefl _)).
    by case: pos_dec (Hrec n2) => //= -[] /(_ (erefl _)).
  Qed.

  Lemma array_length_dec_r len1 len2 tt: array_length_dec len1 len2 = right tt -> len1 != len2.
  Proof.
    case: tt; case: len1 len2 => [ p1 | a1 ] [ p2 | a2 ] //=.
    + case: pos_dec (@pos_dec_r p1 p2 I) => [Heq _ | [] neq ] //=.
      move=> _; apply/eqP => -[].
      by move/eqP: (neq erefl).
    case: array_length_abstract_dec (@array_length_abstract_dec_r a1 a2 I) => [Heq _ | [] neq ] //=.
    move=> _; apply/eqP => -[].
    by move/eqP: (neq erefl).
  Qed.

  Lemma eq_dec_r t1 t2 tt: eq_dec t1 t2 = right tt -> t1 != t2.
  Proof.
    case: tt;case:t1 t2=> [||n|w] [||n'|w'] //=.
    + case: array_length_dec (@array_length_dec_r n n' I) => [Heq _ | [] neq ] //=.
      move => _; apply/eqP => -[].
      by move/eqP: (neq erefl).
    case: wsize_eq_dec => // eqw.
    by move=> _;apply /eqP;congruence.
  Qed.

End CEDecStype.

Module Mt := DMmake CmpStype CEDecStype.

Declare Scope mtype_scope.
Delimit Scope mtype_scope with mt.
Notation "m .[ x ]" := (@Mt.get _ m x) : mtype_scope.
Notation "m .[ x  <- v ]" := (@Mt.set _ m x v) : mtype_scope.
Arguments Mt.get P m%mtype_scope k.
Arguments Mt.set P m%mtype_scope k v.


Definition is_sbool t := t == sbool.

Lemma is_sboolP t : reflect (t=sbool) (is_sbool t).
Proof. by rewrite /is_sbool;case:eqP => ?;constructor. Qed.

Definition is_sword t := if t is sword _ then true else false.

Definition is_sarr t := if t is sarr _ then true else false.

Definition is_not_sarr t := ~~is_sarr t.

Lemma is_sarrP ty : reflect (exists n, ty = sarr n) (is_sarr ty).
Proof. by case: ty; constructor; eauto => [[]]. Qed.

Definition is_word_type (t:stype) :=
  if t is sword sz then Some sz else None.

Lemma is_word_typeP ty ws :
  is_word_type ty = Some ws -> ty = sword ws.
Proof. by case: ty => //= w [->]. Qed.

Definition vundef_type (t:stype) :=
  match t with
  | sword _ => sword8
  | sarr _  => sarr (const_length 1)
  | _       => t
  end.

(* -------------------------------------------------------------------- *)
Definition compat_type t1 t2 :=
  match t1 with
  | sint    => t2 == sint
  | sbool   => t2 == sbool
  | sword _ => is_sword t2
  | sarr _  => is_sarr t2
  end.

Lemma compat_typeC t1 t2 : compat_type t1 t2 = compat_type t2 t1.
Proof. by case: t1 t2 => [||n1|wz1] [||n2|wz2]. Qed.

Lemma compat_type_refl t : compat_type t t.
Proof. by case: t => [||n|wz]. Qed.
#[global]
Hint Resolve compat_type_refl : core.

Lemma compat_type_trans t2 t1 t3 : compat_type t1 t2 -> compat_type t2 t3 -> compat_type t1 t3.
Proof.
  case: t1 => /=.
  + by move => /eqP -> /eqP ->.
  + by move => /eqP -> /eqP ->.
  + by case: t2.
  by case: t2.
Qed.

Lemma compat_type_undef t : compat_type t (vundef_type t).
Proof. by case t. Qed.

(* -------------------------------------------------------------------- *)
Definition subtype (t t': stype) :=
  match t with
  | sword w => if t' is sword w' then (w ≤ w')%CMP else false
  | sarr n => if t' is sarr n' then n == n' else false
  | _ => t == t'
  end.

Lemma subtypeE ty ty' :
  subtype ty ty' →
  match ty' with
  | sword sz' => ∃ sz, ty = sword sz ∧ (sz ≤ sz')%CMP
  | sarr n'   => ∃ n, ty = sarr n ∧ (n <= n')%CMP
  | _         => ty = ty'
end.
Proof.
  destruct ty; try by move/eqP => <-.
  + by case: ty'=> //= p' /eqP ->; eauto.
  by case: ty' => //; eauto.
Qed.

Lemma subtypeEl ty ty' :
  subtype ty ty' →
  match ty with
  | sword sz => ∃ sz', ty' = sword sz' ∧ (sz ≤ sz')%CMP
  | sarr n   => ∃ n', ty' = sarr n' ∧ (n <= n')%CMP
  | _        => ty' = ty
  end.
Proof.
  destruct ty; try by move/eqP => <-.
  + by case: ty'=> //= p' /eqP ->; eauto.
  by case: ty' => //; eauto.
Qed.

Lemma subtype_refl x : subtype x x.
Proof. by case: x => /=. Qed.
#[global]
Hint Resolve subtype_refl : core.

Lemma subtype_trans y x z : subtype x y -> subtype y z -> subtype x z.
Proof.
  case: x => //= [/eqP<-|/eqP<-|n1|sx] //.
  + case: y => //= n2 h1;case: z => //= n3 h2.
    by apply: eq_op_trans h2.
  case: y => //= sy hle;case: z => //= sz;apply: cmp_le_trans hle.
Qed.

Lemma subtype_compat t1 t2 : subtype t1 t2 -> compat_type t1 t2.
Proof.
  by case: t1 => [/eqP ->| /eqP -> | p | w] // ; case: t2.
Qed.

Lemma array_length_cmp_1 len : (const_length 1 <= len)%CMP.
Proof.
  by case: len => // p; case: p.
Qed.
(*
Lemma compat_subtype_undef t1 t2 : compat_type t1 t2 → subtype (vundef_type t1) t2.
Proof.
  case: t1 => [/eqP ->|/eqP ->|?|?] //=; case: t2 => // *.
  + by apply array_length_cmp_1.
  by apply wsize_le_U8.
Qed.
*)