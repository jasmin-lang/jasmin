(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Coq Require Import ZArith.
Require Import gen_map utils strings.
Require Export wsize.
Import Utf8.

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
Notation ty_msf := (sword msf_size).

(* -------------------------------------------------------------------- *)
Scheme Equality for stype.

Lemma stype_axiom : Equality.axiom stype_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_stype_dec_bl internal_stype_dec_lb).
Qed.

HB.instance Definition _ := hasDecEq.Build stype stype_axiom.


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

  Definition t : eqType := stype.

  Definition cmp : t -> t -> comparison := stype_cmp.

  Definition cmpO : Cmp cmp := stypeO.

End CmpStype.

Module CEDecStype.

  Definition t : eqType := stype.

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
Arguments Mt.get P m%_mtype_scope k.
Arguments Mt.set P m%_mtype_scope k v.


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

(* -------------------------------------------------------------------- *)
Definition subtype (t t': stype) :=
  match t with
  | sword w => if t' is sword w' then (w ≤ w')%CMP else false
  | _ => t == t'
  end.

Lemma subtypeE ty ty' :
  subtype ty ty' →
  match ty' with
  | sword sz' => ∃ sz, ty = sword sz ∧ (sz ≤ sz')%CMP
  | _         => ty = ty'
end.
Proof.
  destruct ty; try by move/eqP => <-.
  by case: ty' => //; eauto.
Qed.

Lemma subtypeEl ty ty' :
  subtype ty ty' →
  match ty with
  | sword sz => ∃ sz', ty' = sword sz' ∧ (sz ≤ sz')%CMP
  | _        => ty' = ty
  end.
Proof.
  destruct ty; try by move/eqP => <-.
  by case: ty' => //; eauto.
Qed.

Lemma subtype_refl x : subtype x x.
Proof. case: x => //=. Qed.
#[global]
Hint Resolve subtype_refl : core.

Lemma subtype_trans y x z : subtype x y -> subtype y z -> subtype x z.
Proof.
  case: x => //= [/eqP<-|/eqP<-|n1|sx] //.
  + by case: y => //= n2 /eqP ->.
  case: y => //= sy hle;case: z => //= sz;apply: cmp_le_trans hle.
Qed.

Lemma is_sword_subtype t1 t2 : subtype t1 t2 -> is_sword t1 = is_sword t2.
Proof.
  by case: t1 => //= [/eqP <-|/eqP <-|?|?] //;case:t2.
Qed.

(* -------------------------------------------------------------------- *)
Variant extended_type (len:Type) : Type :=
  | ETbool
  | ETint
  | ETarr of len
  | ETword of (option signedness) & wsize.

Definition tbool {len} := ETbool len.
Definition tint  {len} := ETint len.
Definition tarr  {len} (l : len) := ETarr l.
Definition tword {len} ws : extended_type len:= ETword len None ws.
Definition twint {len} (s : signedness) (ws : wsize) := ETword len (Some s) ws.
Definition tuint {len} ws : extended_type len := twint Unsigned ws.
Definition tsint {len} ws : extended_type len := twint Signed ws.

Definition to_stype (t:extended_type positive) : stype :=
  match t with
  | ETbool      => sbool
  | ETint       => sint
  | ETarr l     => sarr l
  | ETword _ ws => sword ws
  end.

Section EQ.
Context {L : eqType}.

Definition ext_type_beq (ty1 ty2 : extended_type L) :=
  match ty1, ty2 with
  | ETbool, ETbool => true
  | ETint, ETint => true
  | ETarr len, ETarr len' => len == len'
  | ETword sg ws, ETword sg' ws' => (sg == sg') && (ws == ws')
  | _, _ => false
  end.

Lemma extended_type_axiom : Equality.axiom ext_type_beq.
Proof.
  case => [||len|sg ws] [||len'|sg' ws'] /=; try by constructor.
  + by case: eqP => [-> | h]; constructor => // -[].
  case: eqP => [-> | h1] /=; last by constructor => -[] /h1.
  by case: eqP => [-> | h2] /=; constructor => // -[] /h2.
Qed.

HB.instance Definition _ := hasDecEq.Build (extended_type L) extended_type_axiom.
End EQ.




