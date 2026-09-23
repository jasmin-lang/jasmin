(* * The language of the safety conditions.

   A safety condition is a boolean expression on the arguments of an
   operation: [IVar n] denotes its n-th argument and the expression operators
   themselves are used to compute. Conditions are interpreted with the
   *total* semantics of [sem_op_total.v], so that their meaning does not
   depend on the failures they are there to rule out.

   This file holds the language, its typing, the check [check_safe] that an
   operation performs on the values of its arguments, and the library of the
   conditions the operators are made of ([sc_toint], [sc_in_range], ...).
   What is specific to the expression operators — which conditions each of
   them carries, and how the conditions guard the total semantics — is in
   [op_semi.v]. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Export sem_op_total.
Require Import values.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
(* ** Conditions on the arguments of an operation                        *)

(* A boolean expression on the arguments of an operation. [IVar n] refers to
   the n-th argument. *)
Inductive safety_cond :=
  | IBool of bool
  | IConst of Z
  | IVar of nat
  | IOp1 of sop1 & safety_cond
  | IOp2 of sop2 & safety_cond & safety_cond.

(* The interpretation goes through the *total* semantics of the operators, so
   that it does not depend on [sem_sop1_typed]/[sem_sop2_typed] failing. *)
Fixpoint sem_safety_cond (vs : values) (c : safety_cond) : exec value :=
  match c with
  | IBool b => ok (Vbool b)
  | IConst z => ok (Vint z)
  | IVar n => ok (nth undef_b vs n)
  | IOp1 o c =>
    Let v := sem_safety_cond vs c in
    Let x := of_val _ v in
    ok (to_val (sem_sop1_total o x))
  | IOp2 o c1 c2 =>
    Let v1 := sem_safety_cond vs c1 in
    Let v2 := sem_safety_cond vs c2 in
    Let x1 := of_val _ v1 in
    Let x2 := of_val _ v2 in
    ok (to_val (sem_sop2_total o x1 x2))
  end.

(* A condition that is not a boolean (in particular an ill-typed one, whose
   interpretation is an error) counts as false. *)
Definition safety_cond_holds (vs : values) (c : safety_cond) : bool :=
  if sem_safety_cond vs c is Ok (Vbool b) then b else false.

(* -------------------------------------------------------------------- *)
(* ** Typing                                                             *)

(* [safety_cond_type tin c] is the type of [c] when the arguments have types
   [tin]. An operator expecting an argument of type [t] accepts a
   sub-condition of type [t'] as soon as [subctype t t'], which is exactly
   what [of_val] accepts (for words: a word of at least that size). *)
Fixpoint safety_cond_type (tin : seq ctype) (c : safety_cond) : option ctype :=
  match c with
  | IBool _ => Some cbool
  | IConst _ => Some cint
  | IVar n => if (n < size tin)%nat then Some (nth cbool tin n) else None
  | IOp1 o c =>
    let t := type_of_op1 o in
    if safety_cond_type tin c is Some t1 then
      if subctype (eval_atype t.1) t1 then Some (eval_atype t.2) else None
    else None
  | IOp2 o c1 c2 =>
    let t := type_of_op2 o in
    if safety_cond_type tin c1 is Some t1 then
      if safety_cond_type tin c2 is Some t2 then
        if subctype (eval_atype t.1.1) t1 && subctype (eval_atype t.1.2) t2
        then Some (eval_atype t.2) else None
      else None
    else None
  end.

(* A well-typed condition is one that evaluates to a boolean. *)
Definition safety_cond_wt (tin : seq ctype) (c : safety_cond) : bool :=
  safety_cond_type tin c == Some cbool.

(* The variables of a condition are among the first [n] arguments. *)
Fixpoint safety_cond_below (n : nat) (c : safety_cond) : bool :=
  match c with
  | IBool _ | IConst _ => true
  | IVar k => (k < n)%nat
  | IOp1 _ c => safety_cond_below n c
  | IOp2 _ c1 c2 => safety_cond_below n c1 && safety_cond_below n c2
  end.

(* Extra arguments do not change the type of a condition: the descriptors that
   extend the arguments of an instruction ([mk_cond], the shifted variants)
   need this to keep their conditions well typed. *)
Lemma safety_cond_type_cat tin tin' c t :
  safety_cond_type tin c = Some t -> safety_cond_type (tin ++ tin') c = Some t.
Proof.
elim: c t => //=.
+ move=> k t; case: ifP => // hk [<-].
  by rewrite nth_cat hk size_cat (ltn_addr _ hk).
+ move=> o c ih t; case heq: (safety_cond_type tin c) => [t1|] //=; case: ifP => // hsub [<-].
  by rewrite (ih _ heq) /= hsub.
move=> o c1 ih1 c2 ih2 t.
case heq1: (safety_cond_type tin c1) => [t1|] //=; case heq2: (safety_cond_type tin c2) => [t2|] //=.
case: ifP => // hsub [<-].
by rewrite (ih1 _ heq1) (ih2 _ heq2) /= hsub.
Qed.

Lemma safety_cond_wt_cat tin tin' c :
  safety_cond_wt tin c -> safety_cond_wt (tin ++ tin') c.
Proof. by rewrite /safety_cond_wt => /eqP /safety_cond_type_cat ->. Qed.

(* -------------------------------------------------------------------- *)
(* ** Checking the conditions                                            *)

(* The safety check: if one of the conditions fails, the operation raises the
   error it declares. *)
Definition check_safe (vs : values) (safe : seq safety_cond) (err : error) : exec unit :=
  if all (safety_cond_holds vs) safe then ok tt else Error err.

(* The arguments are collected, as values, in [vs] along the [sem_prod], and
   [P] is applied to them and to the result. *)
Fixpoint mk_semi_aux {T T'} (P : values -> T -> exec T') (vs : values) (tin : seq ctype) :
  sem_prod tin T -> sem_prod tin (exec T') :=
  match tin return sem_prod tin T -> sem_prod tin (exec T') with
  | [::] => fun t => P vs t
  | t :: tin => fun o v => @mk_semi_aux T T' P (rcons vs (to_val v)) tin (o v)
  end.
Arguments mk_semi_aux {T T'} P vs tin _ : assert.

(* -------------------------------------------------------------------- *)
(* ** The library of conditions                                          *)

Definition sc_toint sg ws k    := IOp1 (Oint_of_word sg ws) (IVar k).
Definition sc_not c            := IOp1 Onot c.
Definition sc_and c1 c2        := IOp2 Oand c1 c2.
Definition sc_or c1 c2         := IOp2 Oor c1 c2.
Definition sc_eqi c1 c2        := IOp2 (Oeq Op_int) c1 c2.
Definition sc_neqi c1 c2       := IOp2 (Oneq Op_int) c1 c2.
Definition sc_lei c1 c2        := IOp2 (Ole Cmp_int) c1 c2.
Definition sc_addi c1 c2       := IOp2 (Oadd Op_int) c1 c2.
Definition sc_muli c1 c2       := IOp2 (Omul Op_int) c1 c2.

Definition sc_in_range lo hi c := sc_and (sc_lei (IConst lo) c) (sc_lei c (IConst hi)).

Definition sc_not_zero ws k    := sc_neqi (sc_toint Unsigned ws k) (IConst 0).

(* The result of a [wint] operation fits in its type. *)
Definition sc_wi_range sg sz (c : safety_cond) : safety_cond :=
  signed (sc_in_range 0 (wmax_unsigned sz) c)
         (sc_in_range (wmin_signed sz) (wmax_signed sz) c) sg.

(* The divisor is not zero and, in the signed case, the division does not
   overflow. *)
Definition sc_divmod sg sz (k1 k2 : nat) : seq safety_cond :=
  sc_not_zero sz k2 ::
  signed [::]
    [:: sc_not (sc_and (sc_eqi (sc_toint sg sz k1) (IConst (wmin_signed sz)))
                       (sc_eqi (sc_toint sg sz k2) (IConst (-1)))) ] sg.
