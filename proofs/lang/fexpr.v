From mathcomp Require Import ssreflect ssrfun ssrbool.
From Coq Require Import Utf8.
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
  | Load of aligned & wsize & var_i & fexpr
  | Rexpr of fexpr.

(* Left-expressions *)
Variant lexpr :=
  | Store of aligned & wsize & var_i & fexpr
  | LLvar of var_i.

Notation rexprs := (seq rexpr).
Notation lexprs := (seq lexpr).

(* -------------------------------------------------------------------------- *)
Fixpoint fexpr_of_pexpr (e: pexpr) : option fexpr :=
  match e with
  | Pconst z => Some (Fconst z)
  | Pvar {| gs := Slocal ; gv := x |} => Some (Fvar x)
  | Papp1 op a => omap (Fapp1 op) (fexpr_of_pexpr a)
  | Papp2 op a b =>
      obind (λ a,
          omap (Fapp2 op a) (fexpr_of_pexpr b)
        ) (fexpr_of_pexpr a)
  | Pif sbool a b c =>
      obind (λ a,
      obind (λ b,
        omap (Fif a b) (fexpr_of_pexpr c))
        (fexpr_of_pexpr b))
        (fexpr_of_pexpr a)
  | _ => None
  end.

Definition rexpr_of_pexpr (e: pexpr) : option rexpr :=
  if e is Pload al ws p e then omap (Load al ws p) (fexpr_of_pexpr e) else omap Rexpr (fexpr_of_pexpr e).

Definition lexpr_of_lval (e: lval) : option lexpr :=
  match e with
  | Lvar x => Some (LLvar x)
  | Lmem al ws p e =>
      omap (Store al ws p) (fexpr_of_pexpr e)
  | _ => None
  end.

(* -------------------------------------------------------------------------- *)
Fixpoint free_vars_rec (s: Sv.t) (e: fexpr) : Sv.t :=
  match e with
  | Fconst _ => s
  | Fvar x => Sv.add x s
  | Fapp1 _ f => free_vars_rec s f
  | Fapp2 _ f1 f2 => free_vars_rec (free_vars_rec s f1) f2
  | Fif f1 f2 f3 => free_vars_rec (free_vars_rec (free_vars_rec s f1) f2) f3
  end.

Definition free_vars (e: fexpr) : Sv.t :=
  free_vars_rec Sv.empty e.

Definition free_vars_r (r:rexpr) : Sv.t :=
  match r with
  | Load _ _ x e => free_vars_rec (Sv.singleton x) e
  | Rexpr e    => free_vars e
  end.

Definition rvar (x : var_i) : rexpr := Rexpr (Fvar x).
Definition rconst (ws : wsize) (z : Z) : rexpr := Rexpr (fconst ws z).
Definition lstore {_ : PointerData} al ws x z := Store al ws x (fconst Uptr z).
