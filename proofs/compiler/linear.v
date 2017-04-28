(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* * Syntax and semantics of the linear language *)

(* ** Imports and settings *)

From mathcomp Require Import all_ssreflect.
Require Import ZArith.
Require Import Utf8.
Import Relations.

Require Import expr compiler_util stack_alloc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
(* --------------------------------------------------------------------------- *)
(* Syntax                                                                      *)

Definition label := positive.

Variant linstr_r :=
  | Lassgn : lval -> assgn_tag -> pexpr -> linstr_r
  | Lopn   : lvals -> sopn -> pexprs -> linstr_r
  | Llabel : label -> linstr_r
  | Lgoto  : label -> linstr_r
  | Lcond  : pexpr -> label -> linstr_r
.

Record linstr : Type := MkLI { li_ii : instr_info; li_i : linstr_r }.

Definition lcmd := seq linstr.

Definition is_label (lbl: label) (i:linstr) : bool :=
  match i.(li_i) with
  | Llabel lbl' => lbl == lbl'
  | _ => false
  end.

Fixpoint find_label (lbl: label) (c: lcmd) {struct c} : option lcmd :=
  match c with
  | nil => None
  | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
  end.

Record lfundef := LFundef {
 lfd_stk_size : Z;
 lfd_nstk : Ident.ident;
 lfd_arg  : seq var_i;
 lfd_body : lcmd;
 lfd_res  : seq var_i;  (* /!\ did we really want to have "seq var_i" here *)
}.

Definition lprog := seq (funname * lfundef).

(* --------------------------------------------------------------------------- *)
(* Translation                                                                 *)

Notation "c1 ';;' c2" :=  (c2 >>= (fun p => c1 p.1 p.2))
   (at level 26, right associativity).

Notation "c1 '>;' c2" :=  (c2 >>= (fun p => ok (p.1, c1 :: p.2)))
   (at level 26, right associativity).

Section LINEAR_C.

  Variable linear_i : instr -> label -> lcmd -> ciexec (label * lcmd).

  Fixpoint linear_c (c:cmd) (lbl:label) (lc:lcmd) :=
    match c with
    | [::] => ciok (lbl, lc)
    | i::c =>
      linear_i i ;; linear_c c lbl lc
    end.

End LINEAR_C.

Definition next_lbl lbl := (lbl + 1)%positive.

Fixpoint linear_i (i:instr) (lbl:label) (lc:lcmd) :=
  let (ii, ir) := i in
  match ir with
  | Cassgn x tag e => ok (lbl, MkLI ii (Lassgn x tag e) :: lc)
  | Copn xs o es => ok (lbl, MkLI ii (Lopn xs o es) :: lc)

  | Cif e [::] c2 =>
    let L1 := lbl in
    let lbl := next_lbl L1 in
    MkLI ii (Lcond e L1) >; linear_c linear_i c2 lbl (MkLI ii (Llabel L1) :: lc)

  | Cif e c1 [::] =>
    let L1 := lbl in
    let lbl := next_lbl L1 in
    MkLI ii (Lcond (Pnot e) L1) >; linear_c linear_i c1 lbl (MkLI ii (Llabel L1) :: lc)

  | Cif e c1 c2 =>
    let L1 := lbl in
    let L2 := next_lbl L1 in
    let lbl := next_lbl L2 in
    MkLI ii (Lcond e L1) >; linear_c linear_i c2 ;; MkLI ii (Lgoto L2) >;
    MkLI ii (Llabel L1) >; linear_c linear_i c1 lbl (MkLI ii (Llabel L2) :: lc)

  | Cwhile c e c' =>
    let L1 := lbl in
    let L2 := next_lbl L1 in
    let lbl := next_lbl L2 in
    MkLI ii (Lgoto L1) >;
    MkLI ii (Llabel L2) >;
    linear_c linear_i c' ;; MkLI ii (Llabel L1) >; linear_c linear_i c lbl
    (MkLI ii (Lcond e L2) :: lc)

  | Cfor _ _ _ => cierror ii (Cerr_linear "for found in linear")

  | Ccall _ _ _ _ => cierror ii (Cerr_linear "call found in linear")

  end.

Definition linear_fd (fd: sfundef) :=
  Let fd' := linear_c linear_i (sf_body fd) 1%positive [::] in
  ok (LFundef (sf_stk_sz fd) (sf_stk_id fd) (sf_params fd) fd'.2 (sf_res fd)).

Definition linear_prog (p: sprog) : cfexec lprog :=
  map_cfprog linear_fd p.


