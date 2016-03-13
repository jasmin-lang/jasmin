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

(* ** Comparison 
 * -------------------------------------------------------------------- *)

Module OrdDecStype.

  Definition t :=  stype.

  Fixpoint cmp t t' : comparison :=
    match t, t' with
    | sword      , sword         => Eq 
    | sword      , _             => Lt
    | sbool      , sword         => Gt
    | sbool      , sbool         => Eq 
    | sbool      , _             => Lt
    | sprod _  _ , sword         => Gt
    | sprod _  _ , sbool         => Gt
    | sprod t1 t2, sprod t1' t2' =>  
      match cmp t1 t1' with
      | Lt => Lt
      | Eq => cmp t2 t2'
      | Gt => Gt
      end
    | sprod _  _ , sarr  _   _   => Lt
    | sarr  n  t , sarr  n'  t'  => 
      match Nat.compare n n' with
      | Lt => Lt
      | Eq => cmp t t'
      | Gt => Gt
      end
    | sarr  _  _ , _             => Gt
    end.

  Lemma cmp_eq x y: cmp x y = Eq <-> x = y.
  Proof.
    elim: x y => [||t1 Ht1 t2 Ht2 | n t Ht] [||t1' t2'|n' t'] //=.
    + case: cmp (Ht1 t1') => [ | H | H].
      + rewrite Ht2=> -[->] // _;split=> [-> | []] //.
      + by split=> //;rewrite H=> -[].
      by split=> //;rewrite H=> -[].
    case: Nat.compare_spec=> [-> | H | H].
    + rewrite Ht;split => [-> | []] //.
    + by split=>// -[] ??;omega.
    by split=>// -[] ??;omega.
  Qed.

  Lemma cmp_sym x y: cmp x y = CompOpp (cmp y x).
  Proof.
    elim: x y=> [||t1 Ht1 t2 Ht2 | n t Ht] [||t1' t2'|n' t'] //=.
    + by rewrite Ht1 Ht2;case: cmp.
    by rewrite Nat.compare_antisym Ht;case: Nat.compare.
  Qed. 
                                           
  Definition c_trans c1 c2 := 
    nosimpl (
    match c1, c2 with
    | Eq, _  => Some c2 
    | _ , Eq => Some c1
    | Lt, Lt => Some Lt 
    | Gt, Gt => Some Gt
    | _ , _  => None 
    end).
 
  Lemma c_transC c1 c2 : c_trans c1 c2 = c_trans c2 c1.
  Proof. by case: c1 c2 => -[]. Qed.

  Lemma c_trans_Lt c1 c2 : c_trans Lt c1 = Some c2 -> Lt = c2.
  Proof. by rewrite /c_trans;case:c1=> //= -[] <-. Qed.

  Lemma c_trans_Gt c1 c2 : c_trans Gt c1 = Some c2 -> Gt = c2.
  Proof. by rewrite /c_trans;case:c1=> //= -[] <-. Qed.

  Lemma cmp_trans_c y x z c: c_trans (cmp x y) (cmp y z) = Some c -> cmp x z = c.
  Proof.
    elim: x y z c => [||t1 Ht1 t2 Ht2 | n t Ht] 
                   [||t1' t2'|n' t'] /=
                   [||t1'' t2''|n'' t''] c => //=;
      try ((by move=> []) ||
           (by apply c_trans_Lt) || 
           (by apply c_trans_Gt)).
    + case: cmp (Ht1 t1' t1'') (Ht2 t2' t2'');case: (cmp t1' t1'') => //.
      + by move=> H1 H2 /H2;rewrite (H1 Eq).
      + by move=> H1 H2;rewrite (H1 Lt) // c_transC;apply c_trans_Lt.
      + by move=> H1 _ ;rewrite (H1 Gt) // c_transC;apply c_trans_Gt.
      + by move=> H1 H2;rewrite (H1 Lt) // c_transC;apply c_trans_Lt.
      + by move=> H1 H2;rewrite /c_trans =>-[] ?;subst;rewrite (H1 Lt).
      + by move=> H1 H2;rewrite (H1 Gt) // c_transC;apply c_trans_Gt.
      by move=> H1 H2;rewrite /c_trans =>-[] ?;subst;rewrite (H1 Gt).
    case: Nat.compare_spec=> [ ? | | ];case: Nat.compare_spec=> [ ? | | //];subst=> //.
    + by rewrite Nat.compare_refl;apply Ht.
    + by move=> /nat_compare_lt ->;rewrite c_transC;apply c_trans_Lt.  
    + by move=> /nat_compare_gt ->;rewrite c_transC;apply c_trans_Gt. 
    + by move=> /nat_compare_lt -> /c_trans_Lt.  
    + move=> ??;have /nat_compare_lt -> : (n < n'')%coq_nat by omega.
      by apply c_trans_Lt.
    + by move=> /nat_compare_gt -> /c_trans_Gt.  
    move=> ??;have /nat_compare_gt -> : (n'' < n)%coq_nat by omega.
    by apply c_trans_Gt.        
  Qed.

  Lemma cmp_trans y x z c: cmp x y = c -> cmp y z = c -> cmp x z = c.
  Proof.
    by move=> H1 H2;apply (@cmp_trans_c y);rewrite H1 H2;case: c {H1 H2}.
  Qed.

End OrdDecStype.

Module CEDecStype.

  Definition t := [eqType of stype].
  
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

  Lemma n_dec_r n1 n2 tt: n_dec n1 n2 = right tt -> n1 != n2.
  Proof.
    case: tt;elim: n1 n2 => [|n1 Hn1] [|n2] //=.
    by case: n_dec (Hn1 n2) => //= -[] H _;apply H.
  Qed.
 
  Lemma eq_dec_r t1 t2 tt: eq_dec t1 t2 = right tt -> t1 != t2.
  Proof.
    case: tt;elim:t1 t2=> [|| t1 Ht1 t2 Ht2 | n t Ht] [|| t1' t2' | n' t'] //=.
    + case: eq_dec (Ht1 t1') => [? _ | [] neq _ ].
      + case: eq_dec (Ht2 t2') => // -[] neq _.
        by move: (neq (erefl _));rewrite !eqE /= andbC => /negPf ->. 
      by move: (neq (erefl _));rewrite !eqE /= => /negPf ->.   
    case: n_dec (@n_dec_r n n' I) => [Heq _ | [] neq ].
    + case: eq_dec (Ht t') => // -[] neq _;rewrite Heq.
      by move: (neq (erefl _));rewrite !eqE /= andbC => /negPf ->. 
    move: (neq (erefl _))=> /eqP H _;rewrite !eqE /=.
    by case H':nat_beq=> //;move:H'=> /internal_nat_dec_bl.
  Qed.

End CEDecStype.

Module DMst := DMmake CEDecStype OrdDecStype.

Delimit Scope mtype_scope with mt.
Notation "m .[ x ]" := (@DMst.get _ m x) : mtype_scope.
Notation "m .[ x  <- v ]" := (@DMst.set _ m x v) : mtype_scope.
Arguments DMst.get P m%mtype_scope k.
Arguments DMst.set P m%mtype_scope k v.


