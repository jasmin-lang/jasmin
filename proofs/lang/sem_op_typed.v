(* * The (partial) semantics of the operators [sop1], [sop2] and [opN].

   Each operator is the total semantics of [sem_op_total.v] guarded by the
   safety conditions of [op_semi.v]: [mk_sem_op] checks the conditions on the
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

Definition sem_sop1_typed {sm : SemMode} (o : sop1) :
  let t := type_of_op1 o in
  let t := (eval_atype t.1, eval_atype t.2) in
  sem_t t.1 → exec (sem_t t.2) :=
  @mk_sem_op sm [:: eval_atype (type_of_op1 o).1] (eval_atype (type_of_op1 o).2)
    (op1_safe o) ErrArith (sem_sop1_total o).

Arguments sem_sop1_typed {sm} o.

Definition sem_sop2_typed {sm : SemMode} (o : sop2) :
  let t := type_of_op2 o in
  let t := (eval_atype t.1.1, eval_atype t.1.2, eval_atype t.2) in
  sem_t t.1.1 → sem_t t.1.2 → exec (sem_t t.2) :=
  @mk_sem_op sm [:: eval_atype (type_of_op2 o).1.1; eval_atype (type_of_op2 o).1.2]
    (eval_atype (type_of_op2 o).2) (op2_safe o) ErrArith (sem_sop2_total o).

Arguments sem_sop2_typed {sm} o.

Section WITH_PARAMS.

Context {cfcd : FlagCombinationParams}.

Definition sem_opN_typed {sm : SemMode} (o : opN) :
  let t := type_of_opN o in
  let t := (map eval_atype t.1, eval_atype t.2) in
  sem_prod t.1 (exec (sem_t t.2)) :=
  @mk_sem_op sm (map eval_atype (type_of_opN o).1) (eval_atype (type_of_opN o).2)
    (opN_safe o) ErrArith (sem_opN_total o).

Arguments sem_opN_typed {sm} o.

End WITH_PARAMS.
