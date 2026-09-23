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

Lemma mk_sem_op1E {sm : SemMode} t1 t safe err (f : sem_t t1 -> sem_t t) v1 :
  @mk_sem_op sm [:: t1] t safe err f v1 =
  (Let _ := check_safe [:: to_val v1] safe err in ok (f v1)).
Proof. by []. Qed.

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
(* ** Well-formedness of the conditions of the operators                 *)

Lemma op1_safe_ok (o : sop1) :
  let t := type_of_op1 o in
  all (safety_cond_wf [:: eval_atype t.1]) (op1_safe o).
Proof.
case: o => //= sg o; case: o => //= sz; case: sg => //=.
all: by rewrite /safety_cond_wf /safety_cond_wt /sc_neqi /sc_eqi /sc_toint /= cmp_le_refl.
Qed.

Lemma op2_safe_ok (o : sop2) :
  let t := type_of_op2 o in
  all (safety_cond_wf [:: eval_atype t.1.1; eval_atype t.1.2]) (op2_safe o).
Proof.
case: o => //= [sg [|sz] | sg [|sz] | sg sz o] //=.
1-2: by case: sg => //=;
  rewrite /safety_cond_wf /safety_cond_wt /sc_not_zero /sc_not /sc_and /sc_eqi /sc_neqi /sc_toint /=
          !cmp_le_refl.
case: o => //=; case: sg => //=.
all: by rewrite /safety_cond_wf /safety_cond_wt /sc_in_range /sc_and /sc_lei /sc_addi /sc_muli
                /sc_not_zero /sc_not /sc_eqi /sc_neqi /sc_toint /= !cmp_le_refl.
Qed.

(* -------------------------------------------------------------------- *)
(* ** Under the conditions, the semantics is the total one               *)

Lemma sem_sop1_typed_safeE (o : sop1) (v1 : value) x1 :
  of_val (eval_atype (type_of_op1 o).1) v1 = ok x1 ->
  all (safety_cond_holds [:: v1]) (op1_safe o) ->
  sem_sop1_typed o x1 = ok (sem_sop1_total o x1).
Proof.
move=> hof hall.
have htr : mapM2 ErrType truncate_val [:: eval_atype (type_of_op1 o).1] [:: v1]
             = ok [:: to_val x1].
+ by rewrite /= /truncate_val hof.
have {}hall : all (safety_cond_holds [:: to_val x1]) (op1_safe o).
+ by rewrite (all_safety_cond_holds_truncate htr (op1_safe_ok o)).
by rewrite /sem_sop1_typed mk_sem_op1E (check_safe_ok ErrArith hall).
Qed.

Lemma sem_sop2_typed_safeE (o : sop2) (v1 v2 : value) x1 x2 :
  of_val (eval_atype (type_of_op2 o).1.1) v1 = ok x1 ->
  of_val (eval_atype (type_of_op2 o).1.2) v2 = ok x2 ->
  all (safety_cond_holds [:: v1; v2]) (op2_safe o) ->
  sem_sop2_typed o x1 x2 = ok (sem_sop2_total o x1 x2).
Proof.
move=> hof1 hof2 hall.
have htr : mapM2 ErrType truncate_val
             [:: eval_atype (type_of_op2 o).1.1; eval_atype (type_of_op2 o).1.2]
             [:: v1; v2] = ok [:: to_val x1; to_val x2].
+ by rewrite /= /truncate_val hof1 /= hof2.
have {}hall : all (safety_cond_holds [:: to_val x1; to_val x2]) (op2_safe o).
+ by rewrite (all_safety_cond_holds_truncate htr (op2_safe_ok o)).
by rewrite /sem_sop2_typed mk_sem_op2E (check_safe_ok ErrArith hall).
Qed.

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
