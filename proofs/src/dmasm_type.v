(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import strings ZArith FMapPositive dmasm_utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.

(* ** Syntax
 * -------------------------------------------------------------------- *)

(* more expressive than required, but leads to simpler definitions *)
Inductive stype : Set :=
| sword : stype
| sbool : stype
| sprod : stype -> stype -> stype
| sarr  : forall (n : nat), stype -> stype.

Notation "st1 ** st2" := (sprod st1 st2) (at level 40, left associativity).

Fixpoint n2P_app (n:nat) p := 
  match n with 
  | 0 => p
  | S n => n2P_app n (xI p)
  end.

Definition n2P (n:nat) := n2P_app n xH.

Lemma n2P_appP n p : n2P_app n p = append (n2P n) p.
Proof.
  elim: n p => [ | n Hn] p //=;rewrite !Hn.
  by rewrite /n2P /= 2!Hn -!appendA.
Qed.

Lemma log_n2P n : log_inf (n2P n) = Z_of_nat n.
Proof. 
  elim:n => [ | n Hn] //=.
  rewrite /n2P /= n2P_appP log_app Zpos_P_of_succ_nat /=;omega.
Qed.

Lemma n2P_app_inj n1 n2 p1 p2 : 
  log_inf p1 = log_inf p2 -> 
  n2P_app n1 p1 = n2P_app n2 p2 -> 
  n1 = n2 /\ p1 = p2.
Proof.
  elim: n1 n2 p1 p2=> [ | n1 Hn1] [ | n2] p1 p2 //= Heq.
  + by move=> Hp;move:Heq;rewrite Hp n2P_appP log_app log_n2P /= => ?; omega.
  + by move=> Hp;move:Heq;rewrite-Hp n2P_appP log_app log_n2P /= => ?; omega.
  move=> /Hn1 [];first by rewrite /= Heq.
  by move=> [->] [].
Qed.

Fixpoint st2P_app (st:stype) p := 
  match st with
  | sword       => xO (xO p)
  | sbool       => xO (xI p)
  | sprod t1 t2 => xI (xO (st2P_app t1 (st2P_app t2 p)))
  | sarr  n  t  => xI (xI (n2P_app n (st2P_app t p)))
  end.

(* C'est vraiment de la merde cette condition de garde. Ca passe sans pb avec des sizes*)
(*
Fixpoint P2st (p:positive) := 
  match p with
  | xO (xO p) => Some (sword, p)
  | xO (xI p) => Some (sbool, p)
  | xI (xO p) => 
    match P2st p with
    | Some (t1, p') => 
      match P2st p' with
      | Some (t2, p') => Some (t1 ** t2, p')
      | None => None
      end
    | None => None
    end
  | _ => None
  end. *)


Definition st2P st := st2P_app st xH.

Lemma st2P_appP st p: st2P_app st p = append (st2P st) p.
Proof.
  elim: st p=> [ | | t1 Ht1 t2 Ht2 | n t1 Ht] p //=.
  + by rewrite !Ht1 !Ht2 -!appendA.
  by rewrite !Ht !n2P_appP -!appendA.
Qed.

Lemma st2P_app_inj st1 st2 p1 p2 : 
  log_inf p1 = log_inf p2 -> 
  st2P_app st1 p1 = st2P_app st2 p2 -> 
  st1 = st2 /\ p1 = p2.
Proof.
  elim: st1 st2 p1 p2 => [ | | t1 Ht1 t2 Ht2 | n t1 Ht] 
    [ | | t1' t2' | n' t'] //= p1 p2 Hlog [] //.
  + have {Ht2} ? := Ht2 _ _ _ Hlog.


