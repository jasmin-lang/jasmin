(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import finmap strings  dmasm_utils dmasm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope fmap.
Local Open Scope fset.

(* ** Variable renaming
 * -------------------------------------------------------------------- *)

Notation renaming := (ident -> ident).

Definition rn_var st (pi : renaming) (v : var st) :=
  let: Var _ n := v in Var st (pi n).

Fixpoint rn_pexpr st (pi : renaming) (pe : pexpr st) :=
  match pe with
  | Pvar   st v           => Pvar (rn_var pi v)
  | Pconst st c           => Pconst c
  | Papp sta ste op pe    => Papp op (rn_pexpr pi pe)
  | Ppair st1 st2 pe1 pe2 => Ppair (rn_pexpr pi pe1) (rn_pexpr pi pe2)
  end.

Fixpoint rn_rval st (pi : renaming) (rv : rval st) :=
  match rv with
  | Rvar  st v            => Rvar (rn_var pi v)
  | Rpair st1 st2 rv1 rv2 => Rpair (rn_rval pi rv1) (rn_rval pi rv2)
  end.

Definition rn_bcmd (pi : renaming) (bc : bcmd) :=
  match bc with
  | Assgn st rv pe       => Assgn (rn_rval pi rv) (rn_pexpr pi pe)
  | Load rv pe_addr      => Load (rn_rval pi rv) (rn_pexpr pi pe_addr)
  | Store pe_addr pe_val => Store (rn_pexpr pi pe_addr) (rn_pexpr pi pe_val)
  end.

Definition rn_range (pi : renaming) (r : range) :=
  let: (dir,pe1,pe2) := r in (dir,rn_pexpr pi pe1,rn_pexpr pi pe2).

Fixpoint rn_cmd (pi : renaming) (c : cmd) :=
  match c with
  | Cskip        => Cskip
  | Cbcmd bc     => Cbcmd (rn_bcmd pi bc)
  | Cseq c1 c2   => Cseq (rn_cmd pi c1) (rn_cmd pi c2)
  | Cif pe c1 c2 => Cif (rn_pexpr pi pe) (rn_cmd pi c1) (rn_cmd pi c2)
  | Cfor v rng c => Cfor (rn_var pi v) (rn_range pi rng) (rn_cmd pi c)
  | Ccall starg stres rv_farg pe_ret c_body rv_res pe_arg =>
      Ccall (rn_rval pi rv_farg) (rn_pexpr pi pe_ret)
        (rn_cmd pi c_body) (rn_rval pi rv_res) (rn_pexpr pi pe_arg)
  end.

(* ** Variable substitution
 * -------------------------------------------------------------------- *)

Notation subst := (forall st, var st -> pexpr st).

Fixpoint subst_pexpr st (s : subst) (pe : pexpr st) :=
  match pe with
  | Pvar   st v           => s st v
  | Pconst st c           => Pconst c
  | Papp sta ste op pe    => Papp op (subst_pexpr s pe)
  | Ppair st1 st2 pe1 pe2 => Ppair (subst_pexpr s pe1) (subst_pexpr s pe2)
  end.

Definition subst_bcmd (s : subst) (bc : bcmd) :=
  match bc with
  | Assgn st rv pe       => Assgn rv (subst_pexpr s pe)
  | Load rv pe_addr      => Load rv (subst_pexpr s pe_addr)
  | Store pe_addr pe_val => Store (subst_pexpr s pe_addr) (subst_pexpr s pe_val)
  end.

Definition subst_range (s : subst) (r : range) :=
  let: (dir,pe1,pe2) := r in (dir,subst_pexpr s pe1,subst_pexpr s pe2).

Fixpoint subst_cmd (s : subst) (c : cmd) :=
  match c with
  | Cskip        => Cskip
  | Cbcmd bc     => Cbcmd (subst_bcmd s bc)
  | Cseq c1 c2   => Cseq (subst_cmd s c1) (subst_cmd s c2)
  | Cif pe c1 c2 => Cif (subst_pexpr s pe) (subst_cmd s c1) (subst_cmd s c2)
  | Cfor v rng c => Cfor v (subst_range s rng) (subst_cmd s c)
  | Ccall _ _ rv_farg pe_ret c_body rv_res pe_arg =>
      Ccall rv_farg (subst_pexpr s pe_ret)
        (subst_cmd s c_body) rv_res (subst_pexpr s pe_arg)
  end.

(* ** Inlining calls
 * -------------------------------------------------------------------- *)

(* Assumes that variables in different scopes all disjoint *)
Fixpoint inline_calls (pos : seq nat) (p : seq nat -> bool) (c : cmd) : cmd :=
  match c with
  | Cskip =>
      Cskip
  | Cbcmd bc =>
      Cbcmd bc
  | Cseq c1 c2 =>
      Cseq (inline_calls (0%N :: pos) p c1) (inline_calls (1%N :: pos) p c2)
  | Cif pe c1 c2 =>
      Cif pe (inline_calls (0%N :: pos) p c1) (inline_calls (1%N :: pos) p c2)
  | Cfor v rng c =>
      Cfor v rng (inline_calls (0%N :: pos) p c)
  | Ccall starg stres rv_farg pe_ret c_body rv_res pe_arg =>
      let c_body := inline_calls (0%N :: pos) p c_body in
      if p pos
      then Cseq (assgn rv_farg pe_arg) (Cseq c_body (assgn rv_res pe_ret))
      else Ccall rv_farg pe_ret c_body rv_res pe_arg
  end.

(* ** Useful definitions and basic properties
 * -------------------------------------------------------------------- *)

Notation assn := (estate -> Prop).

Definition post (c : cmd) (Pre: assn) : assn :=
  fun est' => exists est, Pre est /\ sem est c est'.

Notation "c <^> sts" := (post c sts) (at level 40, left associativity).

Parameter rn_pred : renaming -> assn -> assn.

Lemma rn_commutes (pi : renaming) (sts : assn) (c : cmd):
  bijective pi ->
    (rn_cmd pi c) <^> (rn_pred pi sts)
  = rn_pred pi (c <^> sts).
Proof. admit. Admitted.