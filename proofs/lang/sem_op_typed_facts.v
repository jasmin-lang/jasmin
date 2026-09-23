(* * Facts about the semantics of the operators [sop1], [sop2] and [opN].

   [sem_op_typed.v] is in the extraction cone and contains definitions only;
   what the compiler proofs need about them is here. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Import sem_op_typed safety_cond_facts values.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
(* ** [mk_sem_op] on the signature of a binary operator                  *)

Lemma mk_sem_op2E {sm : SemMode} t1 t2 t safe err (f : sem_t t1 -> sem_t t2 -> sem_t t) v1 v2 :
  @mk_sem_op sm [:: t1; t2] t safe err f v1 v2 =
  (Let _ := check_safe [:: to_val v1; to_val v2] safe err in ok (f v1 v2)).
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
(* ** The total mode: the semantics is the total one                      *)

Lemma sem_sop1_typed_total o x : sem_sop1_typed (sm := total) o x = ok (sem_sop1_total o x).
Proof. by []. Qed.

Lemma sem_sop2_typed_total o x1 x2 :
  sem_sop2_typed (sm := total) o x1 x2 = ok (sem_sop2_total o x1 x2).
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
(* ** Computing the operators that can fail                              *)

(* [sc_divmod] is the usual guard of the divisions. *)
Lemma divmod_eq sz sg T (r : T) (w1 w2 : word sz) :
  (Let _ := check_safe [:: Vword w1; Vword w2] (sc_divmod sg sz 0 1) ErrArith
   in ok r) =
  (if ((w2 == 0) || [&& sg == Signed, wsigned w1 == wmin_signed sz & w2 == -1%w])%w
   then Error ErrArith else ok r).
Proof.
rewrite /check_safe /sc_divmod /=.
rewrite (safety_cond_holds_not_zero (vs := [:: Vword w1; Vword w2]) (k:=1) erefl).
case: sg => /=; last by rewrite andbT; case: (w2 == 0%w).
rewrite /safety_cond_holds /sc_not /sc_and /sc_eqi /sc_toint /= !truncate_word_u /= andbT.
have -> : (wsigned w1 =? wmin_signed sz)%Z = (wsigned w1 == wmin_signed sz) by [].
have -> : (wsigned w2 =? -1)%Z = (w2 == (-1)%R).
+ by rewrite -{1}(wsignedN1 sz) (int_of_word_eqb Signed w2 (-1)%R).
by case: (w2 == 0%w); case: ((wsigned w1 == wmin_signed sz) && (w2 == (-1)%R)).
Qed.

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

(* -------------------------------------------------------------------- *)
(* ** The n-ary operators                                                *)

Section WITH_PARAMS.

Context {cfcd : FlagCombinationParams}.

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
