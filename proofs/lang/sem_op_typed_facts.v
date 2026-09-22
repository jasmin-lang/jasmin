(* * The two semantics of the operators agree.

   [sem_sop1_eq], [sem_sop2_eq] and [sem_opN_eq] state that the typed
   semantics of [sem_op_typed.v] is exactly [mk_sem_op] of the conditions of
   [op_semi.v] and of the total semantics of [sem_op_total.v], as an
   extensional equality of [sem_prod]. The next commit turns these equalities
   into the definition of the typed semantics. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Import op_semi sem_op_typed safety_cond_facts values.
Import Utf8.

(* -------------------------------------------------------------------- *)
(* ** Bounds and range conditions of the [wint] operators                *)

Lemma half_modulus_pos ws : (0 < half_modulus ws)%Z.
Proof. by case: ws. Qed.

Lemma wmin_signed_neg ws : (wmin_signed ws < 0)%Z.
Proof. rewrite /wmin_signed; have := half_modulus_pos ws; Lia.lia. Qed.

Lemma wmax_signed_pos ws : (0 < wmax_signed ws)%Z.
Proof. by case: ws. Qed.

Lemma wsigned_opp sz (w:word sz) :
  wsigned w <> wmin_signed sz -> (- wsigned w)%Z = wsigned (- w)%R.
Proof.
  rewrite !wsigned_alt !wunsigned_add_if wunsigned_opp_if.
  have h1 := half_modulus_pos sz.
  have h2 := wbase_twice_half sz.
  have -> : wunsigned (wrepr sz (half_modulus sz)) = half_modulus sz.
  + by apply wunsigned_repr_small; Lia.lia.
  case: eqP => [-> | ?].
  + rewrite Z.add_0_l; have -> : (half_modulus sz <? wbase sz)%Z.
    + by apply /ZltP; Lia.lia.
    by move=> _; ring.
  rewrite /wmin_signed; case: ZltP => ?; case: ZltP => ?; Lia.lia.
Qed.

Lemma int_of_word_wrepr sg sz z :
  in_wint_range sg sz z = ok tt ->
  int_of_word sg (wrepr sz z) = z.
Proof.
  case: sg => /assertP /andP [] /ZleP ? /ZleP; rewrite /wmax_unsigned => ?.
  + exact: wsigned_repr.
  apply wunsigned_repr_small; Lia.lia.
Qed.

Lemma wint_of_int_of_word sg sz (w : word sz) :
  wint_of_int sg sz (int_of_word sg w) = ok w.
Proof.
  rewrite /wint_of_int /int_of_word /in_wint_range /signed.
  case: sg.
  + rewrite wrepr_signed /in_sint_range.
    by have [/ZleP -> /ZleP ->] := wsigned_range w.
  rewrite wrepr_unsigned /in_uint_range.
  have [/ZleP -> h] := wunsigned_range w.
  have /ZleP -> // : (wunsigned w <= wmax_unsigned sz)%Z.
  by rewrite /wmax_unsigned; Lia.lia.
Qed.

Lemma int_of_word0 sg sz : int_of_word (sz:=sz) sg 0%R = 0%Z.
Proof. by case: sg => /=; rewrite ?wsigned0 ?wunsigned0. Qed.

(* -------------------------------------------------------------------- *)
(* ** The integer shifts                                                 *)

Lemma zasr_shiftr z n : (0 <= n)%Z -> zasr z n = Z.shiftr z n.
Proof.
move=> hn; rewrite /zasr /zlsl; case: ZleP => h.
+ have -> : n = 0%Z by Lia.lia.
  by rewrite Z.mul_1_r Z.shiftr_0_r.
by rewrite Z.opp_involutive Z.shiftr_div_pow2.
Qed.

(* An arithmetic shift right never leaves the range of the wint. *)
Lemma in_wint_range_zasr sg sz (w1 : word sz) (w2 : u8) :
  in_wint_range sg sz (zasr (int_of_word sg w1) (int_of_word Unsigned w2)) = ok tt.
Proof.
  rewrite /in_wint_range /zasr /zlsl /assert; case: ifPn => // /negP.
  have [h1 h2] := wunsigned_range w2.
  rewrite /int_of_word /=; elim; case: ZleP => ?.
  + have -> /= : wunsigned w2 = 0%Z by Lia.lia.
    rewrite Z.mul_1_r; case: (sg) => /=;
    [have [??] := wsigned_range w1 | have [??] := wunsigned_range w1];
    apply/andP; split; apply /ZleP => //.
    rewrite /wmax_unsigned; Lia.lia.
  have ? : (0 < 2 ^ wunsigned w2)%Z by Lia.nia.
  rewrite Z.opp_involutive; case: (sg) => /=.
  + have ? := wmin_signed_neg sz; have ? := wmax_signed_pos sz.
    have [??] := wsigned_range w1.
    apply/andP; split; apply/ZleP.
    + by apply Z.div_le_lower_bound => //; Lia.nia.
    by apply Z.div_le_upper_bound => //; Lia.nia.
  have ? : (1 <= wmax_unsigned sz)%Z by case sz.
  have [??] := wunsigned_range w1.
  have ? : (0 < 2 ^ wunsigned w1)%Z by Lia.nia.
  apply/andP; split; apply/ZleP.
  + apply Z.div_le_lower_bound => //; Lia.nia.
  apply Z.div_le_upper_bound => //; rewrite /wmax_unsigned; Lia.nia.
Qed.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
(* ** Evaluating the conditions                                          *)

(* [wint_of_int] is exactly the range condition followed by [wrepr]. *)
Lemma wint_range_eq vs sg sz c z (r : word sz) :
  sem_safety_cond vs c = ok (Vint z) -> r = wrepr sz z ->
  wint_of_int sg sz z =
    (Let _ := check_safe vs [:: sc_wi_range sg sz c] ErrArith in ok r).
Proof.
move=> h ->; rewrite /check_safe /= andbT (safety_cond_holds_wi_range sg sz h).
rewrite /wint_of_int /in_wint_range /assert.
by case: ifP.
Qed.

(* The guard of [mk_sem_divmod] is [sc_divmod]. *)
Lemma divmod_eq sz sg (o : word sz -> word sz -> word sz) (w1 w2 : word sz) :
  mk_sem_divmod sg o w1 w2 =
  (Let _ := check_safe [:: Vword w1; Vword w2] (sc_divmod sg sz 0 1) ErrArith
   in ok (o w1 w2)).
Proof.
rewrite /check_safe /sc_divmod /mk_sem_divmod /=.
rewrite (safety_cond_holds_not_zero (vs := [:: Vword w1; Vword w2]) (k:=1) erefl).
case: sg => /=; last by rewrite andbT; case: (w2 == 0%w).
rewrite /safety_cond_holds /sc_not /sc_and /sc_eqi /sc_toint /= !truncate_word_u /= andbT.
have -> : (wsigned w1 =? wmin_signed sz)%Z = (wsigned w1 == wmin_signed sz) by [].
have -> : (wsigned w2 =? -1)%Z = (w2 == (-1)%R).
+ by rewrite -{1}(wsignedN1 sz) (int_of_word_eqb Signed w2 (-1)%R).
by case: (w2 == 0%w); case: ((wsigned w1 == wmin_signed sz) && (w2 == (-1)%R)).
Qed.

(* The arithmetic shift right needs no condition. *)
Lemma wishr_eq sg sz (v1 : word sz) (v2 : word U8) :
  mk_sem_wishift sg zasr v1 v2 = ok (signed (@sem_shr sz) (@sem_sar sz) sg v1 v2).
Proof.
have h2 : (0 <= int_of_word Unsigned v2)%Z.
+ by rewrite /int_of_word /signed; have := wunsigned_range v2; Lia.lia.
rewrite /mk_sem_wishift /wint_of_int in_wint_range_zasr /= (zasr_shiftr _ h2).
case: sg => /=.
+ by rewrite /sem_sar /sem_shift wsar_alt.
by rewrite /sem_shr /sem_shift wshr_alt.
Qed.

(* -------------------------------------------------------------------- *)
(* ** [mk_sem_op] on the signatures of the operators                     *)

Lemma mk_sem_op1E t1 t safe err (f : sem_t t1 -> sem_t t) v1 :
  @mk_sem_op [:: t1] t safe err f v1 =
  (Let _ := check_safe [:: to_val v1] safe err in ok (f v1)).
Proof. by []. Qed.

Lemma mk_sem_op2E t1 t2 t safe err (f : sem_t t1 -> sem_t t2 -> sem_t t) v1 v2 :
  @mk_sem_op [:: t1; t2] t safe err f v1 v2 =
  (Let _ := check_safe [:: to_val v1; to_val v2] safe err in ok (f v1 v2)).
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
(* ** The typed semantics is [mk_sem_op] of the total one                *)

Lemma sem_sop1_eq (o : sop1) :
  let t := type_of_op1 o in
  sem_prod_eq [:: eval_atype t.1]
    (sem_sop1_typed o)
    (@mk_sem_op [:: eval_atype t.1] (eval_atype t.2) (op1_safe o) ErrArith
       (sem_sop1_total o)).
Proof.
case: o => //=; first by case.
move=> sg [sz|sz|sz|sz|szo szi|sz] v //=.
+ by rewrite mk_sem_op1E; apply: (@wint_range_eq [:: Vint v] sg sz (IVar 0) v).
rewrite mk_sem_op1E /check_safe; case: sg => /=;
  rewrite /safety_cond_holds /sc_eqi /sc_neqi /sc_toint /= truncate_word_u /= andbT.
+ case heq: (wsigned v =? wmin_signed sz)%Z => /=.
  + move/Z.eqb_eq: heq => heq.
    rewrite /wint_of_int /in_wint_range /in_sint_range /assert; case: ifP => //.
    move=> /andP [] _ /ZleP; rewrite heq /wmin_signed /wmax_signed.
    by have := half_modulus_pos sz; Lia.lia.
  move/Z.eqb_neq: heq => heq.
  by rewrite (wsigned_opp heq); apply: (wint_of_int_of_word Signed (- v)%R).
case heq: (wunsigned v =? 0)%Z => /=;
  rewrite /wint_of_int /in_wint_range /signed /in_uint_range /assert.
+ move/Z.eqb_eq: heq => heq; rewrite heq /= opp_wordE.
  have -> : (- v)%R = wrepr sz (- wunsigned v) by rewrite wrepr_opp wrepr_unsigned.
  by rewrite heq.
have hne : wunsigned v <> 0%Z.
+ by move=> h0; move: heq; rewrite h0.
case: ifP => //.
move=> /andP [] /ZleP h _.
by have := wunsigned_range v; Lia.lia.
Qed.

Lemma sem_sop2_eq (o : sop2) :
  let t := type_of_op2 o in
  sem_prod_eq [:: eval_atype t.1.1; eval_atype t.1.2]
    (sem_sop2_typed o)
    (@mk_sem_op [:: eval_atype t.1.1; eval_atype t.1.2] (eval_atype t.2)
       (op2_safe o) ErrArith (sem_sop2_total o)).
Proof.
case: o => //=.
all: try by case.
1-2: by move=> s [|sz] v1 v2 //=; rewrite mk_sem_op2E; apply: divmod_eq.
move=> sg sz [] v1 v2 //=; rewrite mk_sem_op2E.
1-3: rewrite /mk_sem_wiop2; apply: wint_range_eq;
     first by rewrite /= !truncate_word_u.
+ by rewrite add_wordE wrepr_add !wrepr_int_of_word.
+ by rewrite mul_wordE wrepr_mul !wrepr_int_of_word.
+ by rewrite sub_wordE wrepr_sub !wrepr_int_of_word.
1-2: by apply: divmod_eq.
+ rewrite /mk_sem_wishift; apply: wint_range_eq;
    first by rewrite /= !truncate_word_u.
  have h2 : (0 <= int_of_word Unsigned v2)%Z.
  + by rewrite /int_of_word /signed; have := wunsigned_range v2; Lia.lia.
  rewrite /zlsl; case: ZleP => [_ | hlt]; last by Lia.lia.
  by rewrite /sem_shl /sem_shift wrepr_mul wrepr_int_of_word (wshl_sem _ h2)
             GRing.mulrC.
by apply: wishr_eq.
Qed.

(* -------------------------------------------------------------------- *)
(* ** [opN]: no condition at all                                         *)

(* [WArray.fill] cannot fail on the number of bytes [Oarray] gives it. *)
Lemma fill_ok_eq (len : Z) :
  sem_prod_eq (nseq (Z.to_nat len) (cword U8))
    (sem_prod_app (collect (A:=cword U8) (Z.to_nat len) [::])
       (fun vs => WArray.fill (arr_size U8 len) vs))
    (sem_prod_ok (nseq (Z.to_nat len) (cword U8))
       (sem_prod_app (collect (A:=cword U8) (Z.to_nat len) [::])
          (fun vs => rdflt (WArray.empty (arr_size U8 len))
                           (WArray.fill (arr_size U8 len) vs)))).
Proof.
apply: (sem_prod_eq_trans (g := sem_prod_app (collect (A:=cword U8) (Z.to_nat len) [::])
          (fun vs => ok (rdflt (WArray.empty (arr_size U8 len))
                               (WArray.fill (arr_size U8 len) vs))))); last first.
+ by apply/sem_prod_eq_sym/sem_prod_ok_app_g.
apply: (sem_prod_eq_prod_app_ext (P := fun vs => size vs = (Z.to_nat len + 0)%nat));
  last by apply: size_collect.
move=> vs; rewrite ssrnat.addn0 => hlen.
rewrite /WArray.fill hlen arr_sizeE wsize8 Z.mul_1_l eqxx /=.
by case/is_okP: (WArray.fill_aux_ok (Nat.eq_le_incl _ _ hlen)) => ? ->.
Qed.

Section OPN.

Context {cfcd : FlagCombinationParams}.

(* [opN] carries no condition: its typed semantics is already the total one
   wrapped in [ok]. *)
Lemma sem_opN_eq_ok (o : opN) :
  let t := type_of_opN o in
  sem_prod_eq (map eval_atype t.1)
    (sem_opN_typed o)
    (sem_prod_ok (map eval_atype t.1) (sem_opN_total o)).
Proof.
case: o => [ws pe | len | cf] /=; last by move=> ????.
all: rewrite -> map_nseq.
+ exact: (@sem_prod_ok_curry cint (word ws) (fun vs => wpack ws pe vs) (div.divn ws pe)).
exact: (fill_ok_eq len).
Qed.

Lemma sem_opN_eq (o : opN) :
  let t := type_of_opN o in
  sem_prod_eq (map eval_atype t.1)
    (sem_opN_typed o)
    (@mk_sem_op (map eval_atype t.1) (eval_atype t.2) (opN_safe o) ErrArith
       (sem_opN_total o)).
Proof.
apply: (sem_prod_eq_trans (g := sem_prod_ok _ (sem_opN_total o))).
+ exact: sem_opN_eq_ok.
by apply/sem_prod_eq_sym/mk_sem_op_nil.
Qed.

End OPN.
