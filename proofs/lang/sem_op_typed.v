(* * The (partial) semantics of the operators [sop1], [sop2] and [opN].

   Each operator is the total semantics of [sem_op_total.v] guarded by the
   conditions of [op_semi.v]: [mk_sem_op] checks the conditions on the
   arguments and, if they hold, returns the total result; otherwise it fails
   with [ErrArith]. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype div ssralg.
From mathcomp Require Import word_ssrZ.
Require Export op_semi.
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

Lemma sem_sop1_typed_total o :
  op1_total o -> forall x, exists y, sem_sop1_typed o x = ok y.
Proof. by move=> h x; exists (sem_sop1_total o x); apply: sem_sop1_typed_totalE. Qed.

Lemma sem_sop2_typed_total o :
  op2_total o -> forall x1 x2, exists y, sem_sop2_typed o x1 x2 = ok y.
Proof.
by move=> h x1 x2; exists (sem_sop2_total o x1 x2); apply: sem_sop2_typed_totalE.
Qed.

(* -------------------------------------------------------------------- *)
(* ** Under the conditions, the semantics succeeds                        *)

Lemma sem_sop1_typed_safe (o : sop1) (v1 : value) x1 :
  of_val (eval_atype (type_of_op1 o).1) v1 = ok x1 ->
  all (acond_b [:: v1]) (op1_safe o) ->
  exists r, sem_sop1_typed o x1 = ok r.
Proof.
move=> hof hall.
have htr : mapM2 ErrType truncate_val [:: eval_atype (type_of_op1 o).1] [:: v1]
             = ok [:: to_val x1].
+ by rewrite /= /truncate_val hof.
have {}hall : all (acond_b [:: to_val x1]) (op1_safe o).
+ by rewrite (all_acond_b_truncate (op1_safe_ok o) htr).
exact: (@mk_sem_op_safe [:: eval_atype (type_of_op1 o).1]
   (eval_atype (type_of_op1 o).2) (op1_safe o) ErrArith (sem_sop1_total o) x1 hall).
Qed.

Lemma sem_sop2_typed_safe (o : sop2) (v1 v2 : value) x1 x2 :
  of_val (eval_atype (type_of_op2 o).1.1) v1 = ok x1 ->
  of_val (eval_atype (type_of_op2 o).1.2) v2 = ok x2 ->
  all (acond_b [:: v1; v2]) (op2_safe o) ->
  exists r, sem_sop2_typed o x1 x2 = ok r.
Proof.
move=> hof1 hof2 hall.
have htr : mapM2 ErrType truncate_val
             [:: eval_atype (type_of_op2 o).1.1; eval_atype (type_of_op2 o).1.2]
             [:: v1; v2] = ok [:: to_val x1; to_val x2].
+ by rewrite /= /truncate_val hof1 /= hof2.
have {}hall : all (acond_b [:: to_val x1; to_val x2]) (op2_safe o).
+ by rewrite (all_acond_b_truncate (op2_safe_ok o) htr).
exact: (@mk_sem_op_safe
   [:: eval_atype (type_of_op2 o).1.1; eval_atype (type_of_op2 o).1.2]
   (eval_atype (type_of_op2 o).2) (op2_safe o) ErrArith (sem_sop2_total o)
   x1 x2 hall).
Qed.

(* Sharper form: under the conditions the semantics is exactly the total
   one. *)
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
+ by rewrite (all_acond_b_truncate (op1_safe_ok o) htr).
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
+ by rewrite (all_acond_b_truncate (op2_safe_ok o) htr).
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

Lemma sem_sop2_typed_widivE sg sz (w1 w2 : word sz) :
  sem_sop2_typed (Owi2 sg sz WIdiv) w1 w2 =
  (if ((w2 == 0) || [&& sg == Signed, wsigned w1 == wmin_signed sz & w2 == -1%w])%w
   then Error ErrArith else ok (signed wdiv wdivi sg w1 w2)).
Proof. by rewrite /sem_sop2_typed mk_sem_op2E divmod_eq. Qed.

Lemma sem_sop2_typed_wimodE sg sz (w1 w2 : word sz) :
  sem_sop2_typed (Owi2 sg sz WImod) w1 w2 =
  (if ((w2 == 0) || [&& sg == Signed, wsigned w1 == wmin_signed sz & w2 == -1%w])%w
   then Error ErrArith else ok (signed wmod wmodi sg w1 w2)).
Proof. by rewrite /sem_sop2_typed mk_sem_op2E divmod_eq. Qed.

(* The [wint] operators: the result is the word operation, provided the
   integer result is in range; that is exactly [wint_of_int]. *)
Lemma sem_sop1_typed_wi_of_intE sg sz (z : Z) :
  sem_sop1_typed (Owi1 sg (WIwint_of_int sz)) z = wint_of_int sg sz z.
Proof.
rewrite /sem_sop1_typed mk_sem_op1E; apply/esym.
exact: (@wint_range_eq [:: Vint z] sg sz (IVar 0) z).
Qed.

Lemma sem_sop1_typed_winegE sg sz (w : word sz) :
  sem_sop1_typed (Owi1 sg (WIneg sz)) w = wint_of_int sg sz (- int_of_word sg w).
Proof.
rewrite /sem_sop1_typed mk_sem_op1E; apply/esym.
rewrite /check_safe; case: sg => /=;
  rewrite /acond_b /sc_eqi /sc_neqi /sc_toint /= truncate_word_u /= andbT.
+ case heq: (wsigned w =? wmin_signed sz)%Z => /=.
  + move/Z.eqb_eq: heq => heq.
    rewrite /wint_of_int /in_wint_range /in_sint_range /assert; case: ifP => //.
    move=> /andP [] _ /ZleP; rewrite heq /wmin_signed /wmax_signed.
    by have := half_modulus_pos sz; Lia.lia.
  move/Z.eqb_neq: heq => heq.
  by rewrite (wsigned_opp heq); apply: (wint_of_int_of_word Signed (- w)%R).
case heq: (wunsigned w =? 0)%Z => /=;
  rewrite /wint_of_int /in_wint_range /signed /in_uint_range /assert.
+ move/Z.eqb_eq: heq => heq; rewrite heq /= opp_wordE.
  have -> : (- w)%R = wrepr sz (- wunsigned w) by rewrite wrepr_opp wrepr_unsigned.
  by rewrite heq.
have hne : wunsigned w <> 0%Z.
+ by move=> h0; move: heq; rewrite h0.
case: ifP => //.
move=> /andP [] /ZleP h _.
by have := wunsigned_range w; Lia.lia.
Qed.

Lemma sem_sop2_typed_wiaddE sg sz (w1 w2 : word sz) :
  sem_sop2_typed (Owi2 sg sz WIadd) w1 w2 =
  wint_of_int sg sz (int_of_word sg w1 + int_of_word sg w2).
Proof.
rewrite /sem_sop2_typed mk_sem_op2E; apply/esym.
apply: wint_range_eq; first by rewrite /= !truncate_word_u.
by rewrite /= add_wordE wrepr_add !wrepr_int_of_word.
Qed.

Lemma sem_sop2_typed_wimulE sg sz (w1 w2 : word sz) :
  sem_sop2_typed (Owi2 sg sz WImul) w1 w2 =
  wint_of_int sg sz (int_of_word sg w1 * int_of_word sg w2).
Proof.
rewrite /sem_sop2_typed mk_sem_op2E; apply/esym.
apply: wint_range_eq; first by rewrite /= !truncate_word_u.
by rewrite /= mul_wordE wrepr_mul !wrepr_int_of_word.
Qed.

Lemma sem_sop2_typed_wisubE sg sz (w1 w2 : word sz) :
  sem_sop2_typed (Owi2 sg sz WIsub) w1 w2 =
  wint_of_int sg sz (int_of_word sg w1 - int_of_word sg w2).
Proof.
rewrite /sem_sop2_typed mk_sem_op2E; apply/esym.
apply: wint_range_eq; first by rewrite /= !truncate_word_u.
by rewrite /= sub_wordE wrepr_sub !wrepr_int_of_word.
Qed.

Lemma sem_sop2_typed_wishlE sg sz (w1 : word sz) (w2 : word U8) :
  sem_sop2_typed (Owi2 sg sz WIshl) w1 w2 =
  wint_of_int sg sz (zlsl (int_of_word sg w1) (int_of_word Unsigned w2)).
Proof.
rewrite /sem_sop2_typed mk_sem_op2E; apply/esym.
apply: wint_range_eq; first by rewrite /= !truncate_word_u.
have h2 : (0 <= int_of_word Unsigned w2)%Z.
+ by rewrite /int_of_word /signed; have := wunsigned_range w2; Lia.lia.
rewrite /= /zlsl; case: ZleP => [_ | hlt];
  last by have := wunsigned_range w2; Lia.lia.
by rewrite /sem_shl /sem_shift wrepr_mul wrepr_int_of_word (wshl_sem _ h2)
           GRing.mulrC.
Qed.

Lemma sem_sop2_typed_wishrE sg sz (w1 : word sz) (w2 : word U8) :
  sem_sop2_typed (Owi2 sg sz WIshr) w1 w2 =
  wint_of_int sg sz (zasr (int_of_word sg w1) (int_of_word Unsigned w2)).
Proof. by rewrite wishr_eq /sem_sop2_typed mk_sem_op2E. Qed.
