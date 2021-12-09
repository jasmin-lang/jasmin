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

From mathcomp Require Import all_ssreflect all_algebra.
Require Import expr linearization.
Require Import x86_decl x86_instr_decl x86_extra x86_linear_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Linear parameters specific to x86. *)
(* Read the definition in linear.v for more information. *)

Definition x86_allocate_stack_frame (rspi: var_i) (sz: Z) :=
  let rspg := Gvar rspi Slocal in
  let p := Papp2 (Oadd (Op_w Uptr)) (Pvar rspg) (cast_const sz) in
  ([:: Lvar rspi ], Ox86 (LEA Uptr), [:: p ]).

Definition x86_free_stack_frame (rspi: var_i) (sz: Z) :=
  let rspg := Gvar rspi Slocal in
  let p := Papp2 (Osub (Op_w Uptr)) (Pvar rspg) (cast_const sz) in
  ([:: Lvar rspi ], Ox86 (LEA Uptr), [:: p ]).

Definition x86_ensure_rsp_alignment (rspi: var_i) (al: wsize) :=
  let to_lvar x := Lvar (VarI (to_var x) xH) in
  let eflags := List.map to_lvar [:: OF ; CF ; SF ; PF ; ZF ] in
  let p0 := Pvar (Gvar rspi Slocal) in
  let p1 := Papp1 (Oword_of_int Uptr) (Pconst (- wsize_size al)) in
  (eflags ++ [:: Lvar rspi ], Ox86 (AND Uptr), [:: p0; p1 ]).

Definition x86_lassign (x: lval) (ws: wsize) (e: pexpr) :=
  let op := if (ws <= U64)%CMP
            then MOV ws
            else VMOVDQU ws
  in ([:: x ], Ox86 op, [:: e ]).

Definition x86_linearization_params : linearization_params :=
  {|
    lp_tmp                  := "RAX"%string;
    lp_allocate_stack_frame := x86_allocate_stack_frame;
    lp_free_stack_frame     := x86_free_stack_frame;
    lp_ensure_rsp_alignment := x86_ensure_rsp_alignment;
    lp_lassign              := x86_lassign;
  |}.
