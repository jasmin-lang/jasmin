(* * The safety conditions of the operators [sop1], [sop2] and [opN].

   For each operator, [op1_safe] / [op2_safe] / [opN_safe] give the conditions
   on its arguments under which the (partial) semantics of [sem_op_typed.v]
   does not fail; that semantics is defined there as [mk_sem_op] of these
   conditions and of the total semantics of [sem_op_total.v].

   Which operators carry a condition also says which conditions of
   [safety_cond.v] are total, hence well formed ([safety_cond_wf]): that is
   what a descriptor requires of the conditions it declares. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Export safety_cond.
Require Import values.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
(* ** The conditions of the operators                                    *)

Definition wiop1_safe (sg : signedness) (o : wiop1) : seq safety_cond :=
  match o with
  | WIwint_of_int sz => [:: sc_wi_range sg sz (IVar 0)]
  | WIneg sz =>
      signed [:: sc_eqi (sc_toint sg sz 0) (IConst 0)]
             [:: sc_neqi (sc_toint sg sz 0) (IConst (wmin_signed sz))]
             sg
  | WIint_of_wint _ | WIword_of_wint _ | WIwint_of_word _ | WIwint_ext _ _ => [::]
  end.

Definition op1_safe (o : sop1) : seq safety_cond :=
  match o with
  | Owi1 sg o => wiop1_safe sg o
  | _ => [::]
  end.

Definition wiop2_safe (sg : signedness) (sz : wsize) (o : wiop2) : seq safety_cond :=
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

Definition op2_safe (o : sop2) : seq safety_cond :=
  match o with
  | Odiv sg (Op_w sz) | Omod sg (Op_w sz) => sc_divmod sg sz 0 1
  | Owi2 sg sz o => wiop2_safe sg sz o
  | _ => [::]
  end.

Definition opN_safe (o : opN) : seq safety_cond := [::].

(* -------------------------------------------------------------------- *)
(* ** Well-formed conditions                                             *)

(* A condition built from operators that carry no condition of their own: its
   interpretation on arguments of the announced types is always a value. *)
Fixpoint safety_cond_total (c : safety_cond) : bool :=
  match c with
  | IBool _ | IConst _ | IVar _ => true
  | IOp1 o c => nilp (op1_safe o) && safety_cond_total c
  | IOp2 o c1 c2 => [&& nilp (op2_safe o), safety_cond_total c1 & safety_cond_total c2]
  | IOpN_safety _ c1 c2 c3 =>
    [&& safety_cond_total c1, safety_cond_total c2 & safety_cond_total c3]
  end.

(* Well-formedness of a condition: well typed on the arguments of the
   operation, and total. *)
Definition safety_cond_wf (tin : seq ctype) (c : safety_cond) : bool :=
  safety_cond_wt tin c && safety_cond_total c.

Lemma safety_cond_wf_cat tin tin' c :
  safety_cond_wf tin c -> safety_cond_wf (tin ++ tin') c.
Proof. by move=> /andP [h1 h2]; rewrite /safety_cond_wf (safety_cond_wt_cat tin' h1). Qed.

Lemma all_safety_cond_wf_cat tin tin' l :
  all (safety_cond_wf tin) l -> all (safety_cond_wf (tin ++ tin')) l.
Proof. by apply: sub_all => c; apply: safety_cond_wf_cat. Qed.

(* -------------------------------------------------------------------- *)
(* ** Well-formedness of the conditions of the library                   *)

(* Only the lemmas that a descriptor needs for its [id_wf] field are here;
   the others are in [safety_cond_facts.v]. *)

Lemma safety_cond_wf_not_zero tin ws k :
  ssrnat.leq (S k) (size tin) -> nth cbool tin k = cword ws ->
  safety_cond_wf tin (sc_not_zero ws k).
Proof.
by move=> h1 h2;
  rewrite /safety_cond_wf /safety_cond_wt /sc_not_zero /sc_neqi safety_cond_type_op2E
    (safety_cond_type_toint Unsigned h1 h2) /=.
Qed.

Lemma safety_cond_wf_is_zero tin ws k :
  ssrnat.leq (S k) (size tin) -> nth cbool tin k = cword ws ->
  safety_cond_wf tin (sc_is_zero ws k).
Proof.
by move=> h1 h2;
  rewrite /safety_cond_wf /safety_cond_wt /sc_is_zero /sc_eqi safety_cond_type_op2E
    (safety_cond_type_toint Unsigned h1 h2) /=.
Qed.

Lemma safety_cond_wf_all_init tin ws len k :
  ssrnat.leq (S k) (size tin) -> nth cbool tin k = carr (arr_size ws len) ->
  safety_cond_wf tin (sc_all_init ws len k).
Proof.
move=> h1 h2; rewrite /safety_cond_wf /safety_cond_wt /sc_all_init /sc_is_arr_init /= h1 h2.
have -> : arr_size U8 (arr_size ws len) = arr_size ws len.
+ by rewrite arr_sizeE wsize8 Z.mul_1_l.
by rewrite /= !eqxx.
Qed.

Lemma safety_cond_wf_x86_division tin sz sg :
  ssrnat.leq 3 (size tin) ->
  nth cbool tin 0 = cword sz -> nth cbool tin 1 = cword sz -> nth cbool tin 2 = cword sz ->
  safety_cond_wf tin (sc_x86_division sz sg).
Proof.
move=> hs h0 h1 h2.
have l0 : ssrnat.leq 1 (size tin) by apply: ssrnat.leq_trans hs.
have l1 : ssrnat.leq 2 (size tin) by apply: ssrnat.leq_trans hs.
by rewrite /safety_cond_wf /safety_cond_wt /sc_x86_division; case: sg => /=;
  rewrite l0 l1 hs h0 h1 h2 /= !cmp_le_refl.
Qed.

(* -------------------------------------------------------------------- *)
(* ** The semantics of an operator from its conditions                   *)

(* An operator has exactly one output: the conditions are checked on the
   arguments, then the total semantics is returned. *)
Definition mk_sem_op {sm : SemMode} (tin : seq ctype) (t : ctype) (safe : seq safety_cond)
    (err : error) (f : sem_prod tin (sem_t t)) : sem_prod tin (exec (sem_t t)) :=
  mk_semi_aux (fun vs r => Let _ := check_safe vs safe err in ok r) [::] tin f.
Arguments mk_sem_op {sm tin t} safe err f : assert.
