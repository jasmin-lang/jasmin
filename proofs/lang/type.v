(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith gen_map utils strings.
Require Export wsize.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Syntax
 * -------------------------------------------------------------------- *)

Variant stype : Set :=
| sbool
| sint
| sarr  of positive
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
Scheme Equality for stype.

Lemma stype_axiom : Equality.axiom stype_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_stype_dec_bl.
  by apply: internal_stype_dec_lb.
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

  | sarr n  , sarr n'        => Pos.compare n n'
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
  + by rewrite (@cmp_eq _ _ positiveO _ _ h).
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
        match pos_dec n1 n2 with
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

  Lemma eq_dec_r t1 t2 tt: eq_dec t1 t2 = right tt -> t1 != t2.
  Proof.
    case: tt;case:t1 t2=> [||n|w] [||n'|w'] //=.
    + case: pos_dec (@pos_dec_r n n' I) => [Heq _ | [] neq ] //=.
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
  | sarr _  => sarr 1
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
  | sarr n => if t' is sarr n' then (n <=? n')%Z else false
  | _ => t == t'
  end.

Lemma subtypeE ty ty' :
  subtype ty ty' →
  match ty' with
  | sword sz' => ∃ sz, ty = sword sz ∧ (sz ≤ sz')%CMP
  | sarr n'   => ∃ n, ty = sarr n ∧ (n <= n')%Z
  | _         => ty = ty'
end.
Proof.
  destruct ty; try by move/eqP => <-.
  + by case: ty'=> //= p' /ZleP ?; eauto.
  by case: ty' => //; eauto.
Qed.

Lemma subtypeEl ty ty' :
  subtype ty ty' →
  match ty with
  | sword sz => ∃ sz', ty' = sword sz' ∧ (sz ≤ sz')%CMP
  | sarr n   => ∃ n', ty' = sarr n' ∧ (n <= n')%Z
  | _        => ty' = ty
  end.
Proof.
  destruct ty; try by move/eqP => <-.
  + by case: ty'=> //= p' /ZleP ?; eauto.
  by case: ty' => //; eauto.
Qed.

Lemma subtype_refl x : subtype x x.
Proof. case: x => //= ?;apply Z.leb_refl. Qed.
#[global]
Hint Resolve subtype_refl : core.

Lemma subtype_trans y x z : subtype x y -> subtype y z -> subtype x z.
Proof.
  case: x => //= [/eqP<-|/eqP<-|n1|sx] //.
  + case: y => //= n2 /ZleP h1;case: z => //= n3 /ZleP h2.
    by apply /ZleP;apply: Z.le_trans h1 h2.
  case: y => //= sy hle;case: z => //= sz;apply: cmp_le_trans hle.
Qed.

Lemma subtype_compat t1 t2 : subtype t1 t2 -> compat_type t1 t2.
Proof.
  by case: t1 => [/eqP ->| /eqP -> | p | w] // ; case: t2.
Qed.


Lemma compat_subtype_undef t1 t2 : compat_type t1 t2 → subtype (vundef_type t1) t2.
Proof.
  case: t1 => [/eqP ->|/eqP ->|?|?] //=; case: t2 => // *.
  + by apply /ZleP; Psatz.lia.
  by apply wsize_le_U8.
Qed.
