(* * The (partial) semantics of the operators [sop1], [sop2] and [opN].

   Each operator is the total semantics of [sem_op_total.v] guarded by the
   conditions of [op_semi.v]: [mk_sem_op] checks the conditions on the
   arguments and, if they hold, returns the total result; otherwise it fails
   with [ErrArith]. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype div ssralg.
From mathcomp Require Import word_ssrZ.
Require Export op_semi.
Require Import values.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
(* ** The definitions                                                    *)

Definition sem_sop1_typed (o : sop1) :
  let t := type_of_op1 o in
  let t := (eval_atype t.1, eval_atype t.2) in
  sem_t t.1 → exec (sem_t t.2) :=
  @mk_sem_op [:: eval_atype (type_of_op1 o).1] (eval_atype (type_of_op1 o).2)
    (op1_safe o) ErrArith (sem_sop1_total o).

Arguments sem_sop1_typed : clear implicits.

Definition sem_sop2_typed (o : sop2) :
  let t := type_of_op2 o in
  let t := (eval_atype t.1.1, eval_atype t.1.2, eval_atype t.2) in
  sem_t t.1.1 → sem_t t.1.2 → exec (sem_t t.2) :=
  @mk_sem_op [:: eval_atype (type_of_op2 o).1.1; eval_atype (type_of_op2 o).1.2]
    (eval_atype (type_of_op2 o).2) (op2_safe o) ErrArith (sem_sop2_total o).

Arguments sem_sop2_typed : clear implicits.

Section WITH_PARAMS.

Context {cfcd : FlagCombinationParams}.

Definition sem_opN_typed (o : opN) :
  let t := type_of_opN o in
  let t := (map eval_atype t.1, eval_atype t.2) in
  sem_prod t.1 (exec (sem_t t.2)) :=
  @mk_sem_op (map eval_atype (type_of_opN o).1) (eval_atype (type_of_opN o).2)
    (opN_safe o) ErrArith (sem_opN_total o).

Arguments sem_opN_typed : clear implicits.

(* [opN] carries no condition: it never fails. *)
Lemma sem_opN_typed_ok (op : opN) :
  sem_forall (@is_ok _ _) _ (sem_opN_typed op).
Proof.
apply: (sem_forall_eq (g := sem_prod_ok _ (sem_opN_total op)));
  first exact: mk_sem_op_nil.
apply: (sem_forall_m (P := fun r => exists t, r = ok t)); last exact: sem_prod_ok_ok.
by move=> r [t ->].
Qed.

End WITH_PARAMS.

(* -------------------------------------------------------------------- *)
(* ** The operators without conditions: the semantics is the total one   *)

Lemma sem_sop1_typed_totalE o :
  op1_total o -> forall x, sem_sop1_typed o x = ok (sem_sop1_total o x).
Proof.
move=> /op1_total_safe h x; rewrite /sem_sop1_typed h.
exact: (mk_sem_op_nil (tin := [:: eval_atype (type_of_op1 o).1])
          (t := eval_atype (type_of_op1 o).2) ErrArith (sem_sop1_total o) x).
Qed.

Lemma sem_sop2_typed_totalE o :
  op2_total o -> forall x1 x2, sem_sop2_typed o x1 x2 = ok (sem_sop2_total o x1 x2).
Proof.
move=> /op2_total_safe h x1 x2; rewrite /sem_sop2_typed h.
exact: (mk_sem_op_nil
          (tin := [:: eval_atype (type_of_op2 o).1.1; eval_atype (type_of_op2 o).1.2])
          (t := eval_atype (type_of_op2 o).2) ErrArith (sem_sop2_total o) x1 x2).
Qed.

(* -------------------------------------------------------------------- *)
(* ** Under the conditions, the semantics is the total one               *)

Lemma sem_sop1_typed_safeE (o : sop1) (v1 : value) x1 :
  of_val (eval_atype (type_of_op1 o).1) v1 = ok x1 ->
  all (acond_b [:: v1]) (op1_safe o) ->
  sem_sop1_typed o x1 = ok (sem_sop1_total o x1).
Proof.
move=> hof hall.
have htr : mapM2 ErrType truncate_val [:: eval_atype (type_of_op1 o).1] [:: v1]
             = ok [:: to_val x1].
+ by rewrite /= /truncate_val hof.
have {}hall : all (acond_b [:: to_val x1]) (op1_safe o).
+ by rewrite (all_acond_b_truncate htr (op1_safe_ok o)).
by rewrite /sem_sop1_typed mk_sem_op1E (check_safe_ok ErrArith hall).
Qed.

Lemma sem_sop2_typed_safeE (o : sop2) (v1 v2 : value) x1 x2 :
  of_val (eval_atype (type_of_op2 o).1.1) v1 = ok x1 ->
  of_val (eval_atype (type_of_op2 o).1.2) v2 = ok x2 ->
  all (acond_b [:: v1; v2]) (op2_safe o) ->
  sem_sop2_typed o x1 x2 = ok (sem_sop2_total o x1 x2).
Proof.
move=> hof1 hof2 hall.
have htr : mapM2 ErrType truncate_val
             [:: eval_atype (type_of_op2 o).1.1; eval_atype (type_of_op2 o).1.2]
             [:: v1; v2] = ok [:: to_val x1; to_val x2].
+ by rewrite /= /truncate_val hof1 /= hof2.
have {}hall : all (acond_b [:: to_val x1; to_val x2]) (op2_safe o).
+ by rewrite (all_acond_b_truncate htr (op2_safe_ok o)).
by rewrite /sem_sop2_typed mk_sem_op2E (check_safe_ok ErrArith hall).
Qed.

(* -------------------------------------------------------------------- *)
(* ** Computing the guarded operators                                    *)

(* The divisions on words. *)
Lemma sem_sop2_typed_divE sg sz (w1 w2 : word sz) :
  sem_sop2_typed (Odiv sg (Op_w sz)) w1 w2 =
  (if ((w2 == 0) || [&& sg == Signed, wsigned w1 == wmin_signed sz & w2 == -1%w])%w
   then Error ErrArith else ok (signed wdiv wdivi sg w1 w2)).
Proof. by rewrite /sem_sop2_typed mk_sem_op2E divmod_eq. Qed.

Lemma sem_sop2_typed_modE sg sz (w1 w2 : word sz) :
  sem_sop2_typed (Omod sg (Op_w sz)) w1 w2 =
  (if ((w2 == 0) || [&& sg == Signed, wsigned w1 == wmin_signed sz & w2 == -1%w])%w
   then Error ErrArith else ok (signed wmod wmodi sg w1 w2)).
Proof. by rewrite /sem_sop2_typed mk_sem_op2E divmod_eq. Qed.
