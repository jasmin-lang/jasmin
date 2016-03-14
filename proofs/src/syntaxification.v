(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import JMeq ZArith.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple finfun.
From mathcomp Require Import choice fintype eqtype div seq zmodp.

Require Import pos_map word dmasm_utils dmasm_type dmasm_var dmasm_sem.
Require Import dmasm_sem_props dmasm_Ssem symbolic_expr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.
Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
Parameter nat2id : nat -> ident.

(* -------------------------------------------------------------------- *)
Class find (T : Type) (x : T) (xs : seq T) (i:nat).

Instance find0 (T : Type) (x : T) (xs : seq T)
 : find x (x :: xs) 0.

Instance findS (T : Type) (x : T) (y : T) (ys :  seq T) i
 {_: find x ys i}
 : find x (y :: ys) i.+1 | 1.

(* -------------------------------------------------------------------- *)
Class closed (T : Type) (xs : seq T).

Instance closed_nil T
 : closed (T:=T) nil.

Instance closed_cons T (x : T) (xs : seq T)
 {_: closed xs}
 : closed (x :: xs).

(* -------------------------------------------------------------------- *)
Class ereify
  (t : stype) (e : pexpr t) (es : spexpr t)
  (S : seq { st : stype & pexpr st}).

Instance ereify_var (t : stype) (e : pexpr t) i S
  `{@find { st : stype & pexpr st } (Tagged pexpr e) S i}
  : ereify e (Evar (Var t (nat2id i))) S
  | 100.

Definition ereifyl t (e : pexpr t) (es : spexpr t) S
  {_: @ereify t e es S}
  `{closed _ S}
  := (es, S).

(* -------------------------------------------------------------------- *)
Ltac ereify xes xS :=
  match goal with
  |- ?e = _ =>
     match eval red in (ereifyl (e := e)) with
     | (?es, ?S) => pose xes := es; pose xS := S
     end
  end.

(* -------------------------------------------------------------------- *)
Goal Pvar (Var sbool "") = Pvar (Var sbool "").
Proof.


ereify a b
.