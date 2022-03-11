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

From mathcomp Require Import
  all_ssreflect
  all_algebra.
Require Import ZArith.

Require Import
  compiler_util
  expr
  label
  sopn
  utils
  word
  wsize.

Require Import linearization.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Context
  {asm_op : Type}
  {asmOp : asmOp asm_op}
  {pd : PointerData}
  {eft : eqType}
  {pT : progT eft}.

(* Architecture-specific functions. *)
Context
  (max_ws : wsize)
  (addz set0 : asm_op)
  (rsp r off vlr zf : gvar)
  (lower_cmd : cmd -> cmd)
  (linearize_cmd : cmd -> lcmd).

Definition clear_stack_loop : cmd :=
  let ri := gv r in
  let offi := gv off in
  let vlri := gv vlr in
  let zfi := gv zf in

 (* r = rsp; *)
  let i0 := Cassgn (Lvar ri) AT_none (sword Uptr) (Pvar rsp) in

  (* ymm = #set0_256(); *)
  let i1 := Copn [:: Lvar vlri ] AT_none (Oasm set0) [::] in

  let al_const :=
    Papp1 (Oword_of_int Uptr) (Pconst (wsize_size max_ws))
  in

  let aligned_r :=
    Papp2 (Oland Uptr) (Pvar r) (Papp1 (Oneg (Op_w Uptr)) al_const)
  in

  (* r &= -32; *)
  let i2 := Cassgn (Lvar ri) AT_none (sword Uptr) aligned_r in

  let c :=
    Papp1 (Oword_of_int Uptr) (wsize_size max_ws)
  in

  (* off = -max_size; *)
  let i3 :=
    Cassgn (Lvar offi) AT_none (sword Uptr) (Papp1 (Oneg (Op_w Uptr)) c)
  in

  (* (u256)[r + off] = ymm; *)
  let i4a :=
    Cassgn (Lmem U256 ri (Pvar off)) AT_none (sword max_ws) (Pvar vlr)
  in

  (* ?{zf}, off = #ADD(off, 32); *)
  let i4b :=
    Copn [:: Lvar zfi; Lvar offi ] AT_none (Oasm addz) [:: Pvar off; Pconst 32 ]
  in

  let i4 :=
    Cwhile NoAlign (map (MkI xH) [:: i4a; i4b ]) (Papp1 Onot (Pvar zf)) [::]
  in

  map (MkI xH) [:: i0; i1; i2; i3; i4 ].

Definition fd_clear_stack (lfd : lfundef) : lfundef :=
  let c := linearize_cmd (lower_cmd clear_stack_loop) in
  {|
    lfd_info := lfd_info lfd;
    lfd_align := lfd_align lfd;
    lfd_tyin := lfd_tyin lfd;
    lfd_arg := lfd_arg lfd;
    lfd_tyout := lfd_tyout lfd;
    lfd_total_stack := lfd_total_stack lfd;
    lfd_res := lfd_res lfd;
    lfd_export := lfd_export lfd;
    lfd_callee_saved := lfd_callee_saved lfd;
    lfd_body := lfd_body lfd ++ c;
  |}.

Definition prog_clear_stack (lp : lprog) : lprog :=
  map_lprog fd_clear_stack lp.
