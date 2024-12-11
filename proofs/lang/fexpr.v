From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import Utf8.
Require Import expr.

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

Definition is_fconst (e : fexpr) : option Z :=
  if e is Fconst z then Some z else None.

Definition is_fwconst (ws : wsize) (e : fexpr) : option (word ws) :=
  match e with
  | Fapp1 (Oword_of_int ws') e =>
      if (ws <= ws')%CMP
      then
        let%opt n := is_fconst e in
        Some (wrepr ws n)
      else None
  | _ => None
  end.

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

Definition free_vars_rs : seq rexpr -> Sv.t :=
  foldr (fun e acc => Sv.union (free_vars_r e) acc) Sv.empty.

Definition rvar (x : var_i) : rexpr := Rexpr (Fvar x).
Definition rconst (ws : wsize) (z : Z) : rexpr := Rexpr (fconst ws z).
Definition lstore {_ : PointerData} al ws x z := Store al ws x (fconst Uptr z).

Fixpoint eq_fexpr (e0 e1 : fexpr) : bool :=
  match e0, e1 with
  | Fconst n0, Fconst n1 => n0 == n1
  | Fvar x0, Fvar x1 => v_var x0 == v_var x1
  | Fapp1 op0 e0, Fapp1 op1 e1 => [&& op0 == op1 & eq_fexpr e0 e1 ]
  | Fapp2 op0 e00 e01, Fapp2 op1 e10 e11 =>
      [&& op0 == op1, eq_fexpr e00 e10 & eq_fexpr e01 e11 ]
  | Fif e00 e01 e02, Fif e10 e11 e12 =>
      [&& eq_fexpr e00 e10, eq_fexpr e01 e11 & eq_fexpr e02 e12 ]
  | _, _ => false
  end.
