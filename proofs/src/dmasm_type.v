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


(* -------------------------------------------------------------------- *)
Scheme Equality for stype. 
(* Definition stype_beq : stype -> stype -> bool *)

Definition eq_stype (st1 st2 : stype) : {st1 = st2} + {st1<>st2}.
Proof. apply stype_eq_dec. Qed.

Lemma steq_axiom : Equality.axiom stype_beq. 
Proof. 
  move=> x y;apply:(iffP idP).
  + by apply: internal_stype_dec_bl.
  by apply: internal_stype_dec_lb.
Qed.

Definition stype_eqMixin     := Equality.Mixin steq_axiom.
Canonical  stype_eqType      := Eval hnf in EqType stype stype_eqMixin.

Parameter st2n : stype -> nat.
Parameter n2st : nat -> stype.
Lemma codeK_stype : cancel st2n n2st. 
Admitted.

Definition stype_choiceMixin := CanChoiceMixin codeK_stype.
Canonical  stype_choiceType  := ChoiceType stype stype_choiceMixin.

(* -------------------------------------------------------------------- *)
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

Module DInjSType.

  Definition t := [eqType of stype].

  Definition t2P := st2P.
 
  Definition t2P_inj := st2P_inj.
  
  Fixpoint n_dec (n1 n2:nat) : {n1 = n2} + {True} :=
    match n1 as n return {n = n2} + {True} with
    | O => 
      match n2 as n0 return {O = n0} + {True} with
      | O => left (erefl O)
      | _ => right I
      end
    | S n1 =>
      match n2 as n0 return {S n1 = n0} + {True} with
      | S n2 => 
        match n_dec n1 n2 with
        | left eq =>
          left (eq_rect n1 (fun n => S n1 = S n) (erefl (S n1)) n2 eq)
        | right _ => 
          right I
        end
      | _ => right I
      end
    end.
          
  Fixpoint eq_dec (t1 t2:t) : {t1 = t2} + {True} :=
    match t1 as t return {t = t2} + {True} with 
    | sword =>
      match t2 as t0 return {sword = t0} + {True} with
      | sword => left (erefl sword)
      | _     => right I
      end
    | sbool =>
      match t2 as t0 return {sbool = t0} + {True} with
      | sbool => left (erefl sbool)
      | _     => right I
      end
    | sprod t1 t1' =>
      match t2 as t0 return {t1 ** t1' = t0} + {True} with
      | sprod t2 t2' =>
        match eq_dec t1 t2 with
        | left eq1 =>
          match eq_dec t1' t2' with
          | left eq2 => 
            let aux  := eq_rect t1 (fun t => t1 ** t1' = t ** t1') (erefl (t1 ** t1')) t2 eq1 in
            let aux' := eq_rect t1' (fun t => t1 ** t1' = t2 ** t) aux t2' eq2 in
            left aux'
          | right _  => right I
          end
        | right _  => right I
        end
      | _            => right I
      end
    | sarr n1 t1 =>
      match t2 as t0 return {sarr n1 t1 = t0} + {True} with
      | sarr n2 t2 =>
        match n_dec n1 n2 with
        | left eqn =>
          match eq_dec t1 t2 with
          | left eqt =>
            let auxn  := 
                eq_rect n1 (fun n => sarr n1 t1 = sarr n t1) (erefl (sarr n1 t1)) n2 eqn in
            let auxt := eq_rect t1 (fun t => sarr n1 t1 = sarr n2 t) auxn t2 eqt in
            left auxt
          | right _ => right I
          end
        | right _  => right I
        end
      | _          => right I
      end
    end.

  Lemma n_dec_r n1 n2 tt: n_dec n1 n2 = right tt -> n1 <> n2.
  Proof.
    case: tt;elim: n1 n2 => [|n1 Hn1] [|n2] //=.
    by case: n_dec (Hn1 n2) => // -[] neq _ [] *;apply neq.
  Qed.

  Lemma eq_dec_r t1 t2 tt: eq_dec t1 t2 = right tt -> t1 <> t2.
  Proof.
    case: tt;elim:t1 t2=> [|| t1 Ht1 t2 Ht2 | n t Ht] [|| t1' t2' | n' t'] //=.
    + case: eq_dec (Ht1 t1') => [? _ | [] neq _ [] *];last by apply neq.
      by case: eq_dec (Ht2 t2') => // -[] neq _ [] *;apply neq.
    + case: n_dec (@n_dec_r n n' I) => [? _ | [] neq _ [] *];last by apply neq.
      by case: eq_dec (Ht t') => // -[] neq _ [] *;apply neq.
  Qed.
    
End DInjSType.

Module DMst := DMmake DInjSType.

Delimit Scope mtype_scope with mt.
Notation "m .[ x ]" := (@DMst.get _ m x) : mtype_scope.
Notation "m .[ x  <- v ]" := (@DMst.set _ m x v) : mtype_scope.
Arguments DMst.get P m%mtype_scope k.
Arguments DMst.set P m%mtype_scope k v.
