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
  | 0 => xI p
  | S n => xO (n2P_app n p)
  end.

Definition n2P n := n2P_app n xH.

Fixpoint P2n (p:positive) := 
  match p with
  | xO p => 
    match P2n p with
    | Some (n, p) => Some (S n, p)
    | None => None
    end
  | xI p => Some (0%nat, p)
  | xH   => None
  end.

Lemma n2P_appP n p : n2P_app n p = append (n2P n) p.
Proof.
  by elim: n p => //= n Hn p;rewrite !Hn -appendA.
Qed.

Lemma n2PK n p: P2n (n2P_app n p) = Some (n, p).
Proof. by elim: n => [ | n Hn] //=;rewrite Hn. Qed.

Fixpoint plog p : nat := 
  match p with
  | xH => 0
  | xO p => S (plog p)
  | xI p => S (plog p)
  end.

Lemma plog_app p1 p2 : plog (append p1 p2) = (plog p1 + plog p2)%nat.
Proof.
  by elim: p1 => [p1 Hp1 | p1 Hp1 | ] //=;rewrite Hp1 addSn.
Qed.

Fixpoint st2P_app (st:stype) p := 
  match st with
  | sword       => xO (xO p)
  | sbool       => xO (xI p)
  | sprod t1 t2 => xI (xO (st2P_app t1 (st2P_app t2 p)))
  | sarr  n  t  => xI (xI (n2P_app n (st2P_app t p)))
  end.

Fixpoint P2st_aux (p:positive) (log:nat) := 
  match p, log with
  | xO (xO p2), _ => 
    Some (sword, p2)

  | xO (xI p2), _ => 
    Some (sbool, p2)

  | xI (xO p'), S log => 
    match P2st_aux p' log with
    | Some (t1, p1') => 
      match P2st_aux p1' log with
      | Some (t2, p2') => Some (t1 ** t2, p2')
      | None => None
      end
    | None => None
    end

  | xI (xI p'), S log =>
     match P2n p' with 
     | Some (n', p1') =>
       match P2st_aux p1' log with
       | Some (st, p2') => Some (sarr n' st, p2') 
       | _ => None
       end 
     | _ => None
     end

  | _, _ => None
  end. 

Definition st2P st := st2P_app st xH.

Lemma st2P_appP st p : st2P_app st p = append (st2P st) p.
Proof.
  elim: st p=> [ | | t1 Ht1 t2 Ht2 | k t Ht] p //=.
  + by rewrite !(Ht1, Ht2) -!appendA.
  + by rewrite !(Ht, n2P_appP) -!appendA.
Qed.

Lemma st2PK n st p:
  plog (st2P_app st p) <= n -> P2st_aux (st2P_app st p) n = Some (st, p).
Proof.
  elim: n st p => [[]//|n ih] [| |t1 t2|k t] //= p ltn.
  + rewrite !ih 1?ltnW //; move: ltn; rewrite ltnS.
    by rewrite !st2P_appP !plog_app; apply/leq_ltn_trans/leq_addl.
  + rewrite n2PK ih //; move: ltn; rewrite ltnS n2P_appP plog_app.
    by move/ltnW/(leq_trans _); apply; apply/leq_addl.
Qed.

Lemma st2P_inj : injective st2P.
Proof. 
  rewrite /st2P => t1 t2 heq.
  have := @st2PK (plog (st2P_app t1 xH)) t1 xH (leqnn _).
  have := @st2PK (plog (st2P_app t2 xH)) t2 xH (leqnn _).
  by rewrite heq=> -> [] ->.
Qed.

(*

Lemma P2n_lt p1 p2 n : P2n p1 = Some (n, p2) -> plog p2 < plog p1.
Proof.
  elim:p1 n p2=> [ p1 Hp1 | p1 Hp1 | ] p2 n //=.
  + by move=> [] _ ->;apply ltnSn.
  case: P2n Hp1 => [ [n' p'] H [] _ <-| //]. 
  apply: (@ltn_trans (plog p1));first by apply: (H _).
  by apply ltnSn.
Qed.

Require Import Recdef.
 
Lemma elt_SS n : n < S (S n).
Proof. by apply: (@ltn_trans (S n));apply: ltnSn. Qed.

Definition ex_log p1 p2 (H:plog p1 < (plog p2).+2) : {p1 | plog p1 < (plog p2).+2 } :=
  exist (fun p => plog p < (plog p2).+2) p1 H. 

Function P2st (p:positive){measure (plog p)} : 
   option (stype * {p1 | plog p1 < plog p}) := 
  match p as p0 return option (stype * {p1 | plog p1 < plog p0}) with
  | xO (xO p2) => 
    Some (sword, ex_log (elt_SS (plog p2))) 

  | xO (xI p2) => 
    Some (sbool, ex_log (elt_SS (plog p2))) 

  | xI (xO p') => 
    match P2st p' with
    | Some (t1, exist p1' Hlt1) => 
      match P2st p1' with
      | Some (t2, exist p2' Hlt2) => 
        Some (t1 ** t2, ex_log (ltn_trans (ltn_trans Hlt2 Hlt1) (elt_SS (plog p'))))
      | None => None
      end
    | None => None
    end

  | xI (xI p') =>
     match P2n p' as o return (forall p2 n, o = Some (n, p2) -> plog p2 < plog p') ->
                               option (stype * {p2 | plog p2 < (plog p').+2}) with
    | Some (n', p1') =>
      fun (H: forall p2 n, Some(n',p1') = Some (n,p2) -> plog p2 < plog p') =>
        match P2st p1' with
        | Some (st, exist p2' Hlt2) =>
          let Hlt1 := H p1' n' (erefl (Some(n',p1'))) in
          Some (sarr n' st, ex_log (ltn_trans (ltn_trans Hlt2 Hlt1) (elt_SS (plog p'))))
        | _ => None
        end 
    | _ => fun _ => None
    end (@P2n_lt p')

  | _ => None
  end. 

*)


