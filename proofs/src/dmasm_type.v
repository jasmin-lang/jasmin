(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import ZArith gen_map dmasm_utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Syntax
 * -------------------------------------------------------------------- *)

(* more expressive than required, but leads to simpler definitions *)
Inductive stype : Set :=
| sbool : stype
| sint  : stype
| sarr  : positive -> stype
| sword : stype.

(* -------------------------------------------------------------------- *)
Scheme Equality for stype. 
(* Definition stype_beq : stype -> stype -> bool *)

Lemma steq_axiom : Equality.axiom stype_beq. 
Proof. 
  move=> x y;apply:(iffP idP).
  + by apply: internal_stype_dec_bl.
  by apply: internal_stype_dec_lb.
Qed.

Definition stype_eqMixin     := Equality.Mixin steq_axiom.
Canonical  stype_eqType      := Eval hnf in EqType stype stype_eqMixin.

(* ** Comparison 
 * -------------------------------------------------------------------- *)

Definition stype_cmp t t' :=
  match t, t' with
  | sbool      , sbool         => Eq 
  | sbool      , _             => Lt

  | sint       , sbool         => Gt
  | sint       , sint          => Eq
  | sint       , _             => Lt

  | sword      , sarr _        => Lt
  | sword      , sword         => Eq 
  | sword      , _             => Gt

  | sarr  n    , sarr  n'      => Pos.compare n n'
  | sarr  _    , _             => Gt
  end.

Instance stypeO : Cmp stype_cmp.
Proof.
  constructor.
  + elim=> [||n|] [||n'|] //=.
    apply cmp_sym.
  + move=> y x;elim: x y=> [||n|] [||n'|] [||n''|] c//=;
    try (by apply ctrans_Eq);eauto using ctrans_Lt, ctrans_Gt.
    apply cmp_ctrans.
  elim=> [||n|] [||n'|] //=.
  by move=> H; have -> := (@cmp_eq _ _ positiveO _ _ H). 
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
        | left eqn => left (eq_rect n1 (fun n => sarr n1 = sarr n) (erefl (sarr n1)) n2 eqn)
        | right _ => right I
        end
      | _          => right I
      end
    | sword =>
      match t2 as t0 return {sword = t0} + {True} with
      | sword => left (erefl sword)
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
    case: tt;elim:t1 t2=> [||n|] [||n'|] //=.
    case: pos_dec (@pos_dec_r n n' I) => [Heq _ | [] neq ] //=.
    move: (neq (erefl _))=> /eqP H _;rewrite !eqE /=.
    by case H':positive_beq=> //;move:H'=> /internal_positive_dec_bl.
  Qed.

End CEDecStype.

Module Mt := DMmake CmpStype CEDecStype.

Delimit Scope mtype_scope with mt.
Notation "m .[ x ]" := (@Mt.get _ m x) : mtype_scope.
Notation "m .[ x  <- v ]" := (@Mt.set _ m x v) : mtype_scope.
Arguments Mt.get P m%mtype_scope k.
Arguments Mt.set P m%mtype_scope k v.
