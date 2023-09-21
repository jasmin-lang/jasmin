From mathcomp Require Import all_ssreflect all_algebra.
Require Import sem_type arch_decl x86_decl x86_instr_decl.
Require values.
Require arch_extra.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition x86_eval_cond
  (get : asm_typed_reg -> values.value) (c : condt) : exec bool :=
  let getf := arch_extra.get_flag get in
  match c with
  | O_ct   => getf OF
  | NO_ct  => Let b := getf OF in ok (~~ b)
  | B_ct   => getf CF
  | NB_ct  => Let b := getf CF in ok (~~ b)
  | E_ct   => getf ZF
  | NE_ct  => Let b := getf ZF in ok (~~ b)
  | S_ct   => getf SF
  | NS_ct  => Let b := getf SF in ok (~~ b)
  | P_ct   => getf PF
  | NP_ct  => Let b := getf PF in ok (~~ b)

  | BE_ct =>
      Let cf := getf CF in
      Let zf := getf ZF in ok (cf || zf)

  | NBE_ct =>
      Let cf := getf CF in
      Let zf := getf ZF in ok (~~ cf && ~~ zf)

  | L_ct =>
      Let sf  := getf SF in
      Let of_ := getf OF in ok (sf != of_)

  | NL_ct =>
      Let sf  := getf SF in
      Let of_ := getf OF in ok (sf == of_)

  | LE_ct =>
      Let zf  := getf ZF in
      Let sf  := getf SF in
      Let of_ := getf OF in ok (zf || (sf != of_))

  | NLE_ct =>
      Let zf  := getf ZF in
      Let sf  := getf SF in
      Let of_ := getf OF in ok (~~ zf && (sf == of_))
  end.

#[global]
Instance x86 : asm register register_ext xmm_register rflag condt x86_op :=
  {| eval_cond := x86_eval_cond |}.
