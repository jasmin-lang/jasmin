From mathcomp Require Import all_ssreflect.
Require Import expr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Expressions without memory accesses *)
Inductive fexpr :=
| Fconst of Z
| Fvar of var_i
| Fapp1 of sop1 & fexpr
| Fapp2 of sop2 & fexpr & fexpr
| Fif of fexpr & fexpr & fexpr.

(* --------------------------------------------------------------------------- *)
Definition fconst (ws: wsize) (z: Z) : fexpr :=
  Fapp1 (Oword_of_int ws) (Fconst z).

(* --------------------------------------------------------------------------- *)
(* Right-expressions *)
Variant rexpr :=
  | Load of wsize & var_i & fexpr
  | Rexpr of fexpr.

(* Left-expressions *)
Variant lexpr :=
  | Store of wsize & var_i & fexpr
  | LLvar of var_i.

Notation rexprs := (seq rexpr).
Notation lexprs := (seq lexpr).
