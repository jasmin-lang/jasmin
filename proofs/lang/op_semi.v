(* * The safety conditions of the operators [sop1], [sop2] and [opN].

   For each operator, [op1_safe] / [op2_safe] / [opN_safe] give the conditions
   on its arguments under which the (partial) semantics of [sem_op_typed.v]
   does not fail; that semantics is defined there as [mk_sem_op] of these
   conditions and of the total semantics of [sem_op_total.v]. *)

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
(* ** The semantics of an operator from its conditions                   *)

(* An operator has exactly one output: the conditions are checked on the
   arguments, then the total semantics is returned. *)
Definition mk_sem_op (tin : seq ctype) (t : ctype) (safe : seq safety_cond) (err : error)
    (f : sem_prod tin (sem_t t)) : sem_prod tin (exec (sem_t t)) :=
  mk_semi_aux (fun vs r => Let _ := check_safe vs safe err in ok r) [::] tin f.
Arguments mk_sem_op {tin t} safe err f : assert.
