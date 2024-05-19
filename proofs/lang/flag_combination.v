Require Import expr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* We distinguish 5 different conditions that can potentially be expressed with
   flags, these are [combine_flags_core], but provide the user with these and
   their negations, [combine_flags].
   Their correspondence is specified by [cf_tbl].
   The correspondence between these conditions and flags is
   architecture-specific. *)

Variant combine_flags_core :=
| CFC_B      (* Below (not above or equal). *)
| CFC_E      (* Equal (zero). *)
| CFC_L      (* Less than (not greater than or equal to). *)
| CFC_BE     (* Below or equal (not above). *)
| CFC_LE.    (* Less than or equal to (not greater than). *)

Definition cf_tbl (c : combine_flags) : bool * combine_flags_core :=
  match c with
  | CF_LT Signed => (false, CFC_L)
  | CF_LT Unsigned => (false, CFC_B)
  | CF_LE Signed => (false, CFC_LE)
  | CF_LE Unsigned => (false, CFC_BE)
  | CF_EQ => (false, CFC_E)
  | CF_NEQ => (true, CFC_E)
  | CF_GE Signed => (true, CFC_L)
  | CF_GE Unsigned => (true, CFC_B)
  | CF_GT Signed => (true, CFC_LE)
  | CF_GT Unsigned => (true, CFC_BE)
  end.


(* -------------------------------------------------------------------- *)
(* Flag combinations. *)

Inductive flag_combination : Type :=
| FCVar0 : flag_combination
| FCVar1 : flag_combination
| FCVar2 : flag_combination
| FCVar3 : flag_combination
| FCNot : flag_combination -> flag_combination
| FCAnd : flag_combination -> flag_combination -> flag_combination
| FCOr : flag_combination -> flag_combination -> flag_combination
| FCEq : flag_combination -> flag_combination -> flag_combination.

Class FlagCombinationParams :=
  {
    fc_of_cfc : combine_flags_core -> flag_combination;
  }.

Section SEM.

  Context
    {X : Type}
    {fcp : FlagCombinationParams}
    (xnot : X -> X)
    (xand xor xeq : X -> X -> X)
    (x0 x1 x2 x3 : X).

  Fixpoint fc_sem (fc : flag_combination) : X :=
    match fc with
    | FCVar0 => x0
    | FCVar1 => x1
    | FCVar2 => x2
    | FCVar3 => x3
    | FCNot fc0 => xnot (fc_sem fc0)
    | FCAnd fc0 fc1 => xand (fc_sem fc0) (fc_sem fc1)
    | FCOr fc0 fc1 => xor (fc_sem fc0) (fc_sem fc1)
    | FCEq fc0 fc1 => xeq (fc_sem fc0) (fc_sem fc1)
    end.

  Definition cf_xsem (cf : combine_flags) : X :=
    let '(n, cfc) := cf_tbl cf in
    let x := fc_sem (fc_of_cfc cfc) in
    if n then xnot x else x.

End SEM.
