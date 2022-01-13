From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import compiler_util expr.
Require Import arm_extra arm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ARM_LOWERING.

Context
  {eft : eqType}
  {pT : progT eft}.

Definition fresh_vars := True.
Definition lowering_options := True.

Definition arm_fvars_correct
  (_ : fresh_vars)
  {eft : eqType}
  {pT : progT eft}
  (_ : fun_decls)
  := true.

Definition lower_condition
  (ii : instr_info)
  (cond : pexpr) :
  seq instr_r * pexpr :=
  ([::], cond).

Fixpoint lower_i (i : instr) : cmd :=
  let '(MkI ii ir) := i in
  match ir with
  | Cassgn _ _ _ _ =>
      [:: MkI ii ir ]
  | Copn _ _ _ _ =>
      [:: MkI ii ir ]
  | Cif e c1 c2  =>
      let '(pre, e') := lower_condition xH e in
      let c1' := conc_map lower_i c1 in
      let c2' := conc_map lower_i c2 in
      map (MkI ii) (pre ++ [:: Cif e' c1' c2' ])
  | Cfor v r c =>
      let c' := conc_map lower_i c in
      [:: MkI ii (Cfor v r c') ]
  | Cwhile a c0 e c1 =>
     let '(pre, e') := lower_condition xH e in
     let c0' := conc_map lower_i c0 in
     let c1' := conc_map lower_i c1 in
     [:: MkI ii (Cwhile a (c0' ++ map (MkI xH) pre) e' c1') ]
  | Ccall _ _ _ _ =>
      [:: MkI ii ir ]
  end.

End ARM_LOWERING.
