(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import expr compiler_util gen_map dead_calls.
(* ------- *) (* - *) Import PosSet.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Lemma i_calls_MkI c ii i :
  i_calls c (MkI ii i) = i_calls_r c i.
Proof. by []. Qed.

Lemma i_calls_asgn c lv tg e :
  i_calls_r c (Cassgn lv tg e) = c.
Proof. by []. Qed.

Lemma i_calls_opn c lv op es :
  i_calls_r c (Copn lv op es) = c.
Proof. by []. Qed.

Lemma i_calls_if c e c1 c2 :
  i_calls_r c (Cif e c1 c2) = c_calls (c_calls c c1) c2.
Proof. by []. Qed.

Lemma i_calls_for c v rg c1 :
  i_calls_r c (Cfor v rg c1) = c_calls c c1.
Proof. by []. Qed.

Lemma i_calls_while c c1 e c2 :
  i_calls_r c (Cwhile c1 e c2) = c_calls (c_calls c c1) c2.
Proof. by []. Qed.

Lemma i_calls_call c ii lv f es :
  i_calls_r c (Ccall ii lv f es) = Sp.add f c.
Proof. by []. Qed.

Hint Rewrite i_calls_MkI  i_calls_asgn i_calls_opn   : calls.
Hint Rewrite i_calls_if   i_calls_for  i_calls_while : calls.
Hint Rewrite i_calls_call : calls.
