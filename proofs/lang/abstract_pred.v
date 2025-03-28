(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import Sint63 strings utils gen_map tagged.
Require Import Utf8.
Require Import expr.

Module Type CORE_PABSTRACT.
  Parameter iabstract : forall (a: opA), sem_prod (pa_tyin a) (exec (sem_t (pa_tyout a))).
End CORE_PABSTRACT.

Fixpoint mk_sem_prod {T: Type} (tin : seq stype) : sem_prod tin (exec T) :=
  match tin return sem_prod tin (exec T) with
  | [::] => Error ErrAbsOp
  | t :: ts => fun v => @mk_sem_prod T ts
  end.

(* An implementation of CORE_ABSTRACT.
   The extraction overwrite it ... *)
Module Cabstract : CORE_PABSTRACT.
  Definition iabstract := fun a: opA => @mk_sem_prod (sem_t(pa_tyout a)) (pa_tyin a) .
End Cabstract.
