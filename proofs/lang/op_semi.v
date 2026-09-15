(* * Value-level conditions of the operators [sop1], [sop2] and [opN].

   For each operator, [op1_safe] / [op2_safe] / [opN_safe] give the conditions
   on its arguments under which the (partial) semantics of [sem_op_typed.v]
   does not fail; that semantics is defined there as [mk_sem_op] of these
   conditions and of the total semantics.

   This file also holds [divmod_eq], the computation lemma that describes the
   division guards. *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Export sopn_semi.
Require Import values.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
(* ** The conditions of the operators                                    *)

Definition wiop1_safe (sg : signedness) (o : wiop1) : seq acond :=
  match o with
  | WIwint_of_int sz => [:: sc_wi_range sg sz (IVar 0)]
  | WIneg sz =>
      signed [:: sc_eqi (sc_toint sg sz 0) (IConst 0)]
             [:: sc_neqi (sc_toint sg sz 0) (IConst (wmin_signed sz))]
             sg
  | WIint_of_wint _ | WIword_of_wint _ | WIwint_of_word _ | WIwint_ext _ _ => [::]
  end.

Definition op1_safe (o : sop1) : seq acond :=
  match o with
  | Owi1 sg o => wiop1_safe sg o
  | _ => [::]
  end.

Definition wiop2_safe (sg : signedness) (sz : wsize) (o : wiop2) : seq acond :=
  match o with
  | WIadd => [:: sc_wi_range sg sz (sc_addi (sc_toint sg sz 0) (sc_toint sg sz 1))]
  | WImul => [:: sc_wi_range sg sz (sc_muli (sc_toint sg sz 0) (sc_toint sg sz 1))]
  | WIsub =>
      [:: sc_wi_range sg sz
            (IOp2 (Osub Op_int) (sc_toint sg sz 0) (sc_toint sg sz 1))]
  | WIdiv | WImod => sc_divmod sg sz 0 1
  | WIshl =>
      [:: sc_wi_range sg sz
            (IOp2 (Olsl Op_int) (sc_toint sg sz 0) (sc_toint Unsigned U8 1))]
  | WIshr => [::]
  | WIeq | WIneq | WIlt | WIle | WIgt | WIge => [::]
  end.

Definition op2_safe (o : sop2) : seq acond :=
  match o with
  | Odiv sg (Op_w sz) | Omod sg (Op_w sz) => sc_divmod sg sz 0 1
  | Owi2 sg sz o => wiop2_safe sg sz o
  | _ => [::]
  end.

Definition opN_safe (o : opN) : seq acond := [::].

(* -------------------------------------------------------------------- *)
(* ** Well-formedness of the conditions                                  *)

Lemma op1_safe_ok (o : sop1) :
  let t := type_of_op1 o in
  all (ac_ok [:: eval_atype t.1]) (op1_safe o).
Proof.
case: o => //= sg o; case: o => //= sz; case: sg => //=.
all: by rewrite /ac_ok /ac_wt /sc_neqi /sc_eqi /sc_toint /= cmp_le_refl.
Qed.

Lemma op2_safe_ok (o : sop2) :
  let t := type_of_op2 o in
  all (ac_ok [:: eval_atype t.1.1; eval_atype t.1.2]) (op2_safe o).
Proof.
case: o => //= [sg [|sz] | sg [|sz] | sg sz o] //=.
1-2: by case: sg => //=;
  rewrite /ac_ok /ac_wt /sc_not_zero /sc_not /sc_and /sc_eqi /sc_neqi /sc_toint /=
          !cmp_le_refl.
case: o => //=; case: sg => //=.
all: by rewrite /ac_ok /ac_wt /sc_in_range /sc_and /sc_lei /sc_addi /sc_muli
                /sc_not_zero /sc_not /sc_eqi /sc_neqi /sc_toint /= !cmp_le_refl.
Qed.

Lemma opN_safe_ok (o : opN) : all (ac_ok [::]) (opN_safe o).
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
(* ** The operators without conditions                                   *)

Lemma op1_total_safe (o : sop1) : op1_total o -> op1_safe o = [::].
Proof. by case: o. Qed.

Lemma op2_total_safe (o : sop2) : op2_total o -> op2_safe o = [::].
Proof. by case: o => [|||[]|[]|[]|?[]|?[]|?|?|?|?|[]|[]|?|?|[]|[]|[]|[]|[]|[]|??|??|??|??|??|??|???]. Qed.

(* -------------------------------------------------------------------- *)
(* ** Evaluating the conditions                                          *)

(* [sc_divmod] is the usual guard of the divisions. *)
Lemma divmod_eq sz sg T (r : T) (w1 w2 : word sz) :
  (Let _ := check_safe [:: Vword w1; Vword w2] (sc_divmod sg sz 0 1) ErrArith
   in ok r) =
  (if ((w2 == 0) || [&& sg == Signed, wsigned w1 == wmin_signed sz & w2 == -1%w])%w
   then Error ErrArith else ok r).
Proof.
rewrite /check_safe /sc_divmod /=.
rewrite (acond_b_not_zero (vs := [:: Vword w1; Vword w2]) (k:=1) erefl).
case: sg => /=; last by rewrite andbT; case: (w2 == 0%w).
rewrite /acond_b /sc_not /sc_and /sc_eqi /sc_toint /= !truncate_word_u /= andbT.
have -> : (wsigned w1 =? wmin_signed sz)%Z = (wsigned w1 == wmin_signed sz) by [].
have -> : (wsigned w2 =? -1)%Z = (w2 == (-1)%R).
+ by rewrite -{1}(wsignedN1 sz) (int_of_word_eqb Signed w2 (-1)%R).
by case: (w2 == 0%w); case: ((wsigned w1 == wmin_signed sz) && (w2 == (-1)%R)).
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
