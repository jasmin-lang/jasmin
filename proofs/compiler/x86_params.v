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
Require Import
  compiler
  label
  linear
  psem
  sopn.
Require Import clear_stack.
Require Import
  x86_decl
  x86_instr_decl
  x86_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition x86_is_move_op (o : sopn.asm_op_t) :=
  match o with
  | BaseOp (None, MOV _) | BaseOp (None, VMOVDQU _) => true
  | _ => false
  end.


Section CLEAR_STACK.

Let vlocal {t T} {_ : ToString t T} (x : T) : gvar :=
  {|
    gv := {| v_info := xH; v_var := to_var x; |};
    gs := Slocal;
  |}.

(* Architecture parameters. *)
Let max_sz : wsize := U256.
Let tmp : gvar := vlocal RSI.
Let off : gvar := vlocal RDI.
Let vlr : gvar := vlocal XMM0.

Let rsp : gvar := vlocal RSP.
Let zf : gvar := vlocal ZF.
Let tmpi : var_i := gv tmp.
Let offi : var_i := gv off.
Let vlri : var_i := gv vlr.
Let zfi : var_i := gv zf.

Let flags_lv :=
  map
    (fun f => Lvar {| v_info := xH; v_var := to_var f; |})
    [:: OF; CF; SF; PF; ZF ].

Definition x86_clear_stack_loop (lbl : label) (max_stk_size : Z) : lcmd :=
  (* tmp = rsp; *)
  let i0 := Lopn [:: Lvar tmpi ] (Ox86 (MOV U64)) [:: Pvar rsp ] in

  (* ymm = #set0_256(); *)
  let i1 := Lopn [:: Lvar vlri ] (Oasm (ExtOp (Oset0 U256))) [::] in

  (* r &= - (wsize_size max_sz); *)
  let i2 :=
    Lopn
      (flags_lv ++ [:: Lvar tmpi ])
      (Ox86 (AND U64))
      [:: Pvar tmp; pword_of_int U64 (- wsize_size max_sz)%Z ]
  in

  (* off = -max_stk_size; *)
  let i3 :=
    Lopn
      [:: Lvar offi ]
      (Ox86 (MOV U64))
      [:: pword_of_int U64 (- max_stk_size)%Z ]
  in

  (* l1: *)
  let i4 := Llabel lbl in

  (* (u256)[tmp + off] = ymm; *)
  let i5 :=
    Lopn [:: Lmem U256 tmpi (Pvar off) ] (Ox86 (VMOVDQU U256)) [:: Pvar vlr ]
  in

  (* ?{zf}, off = #ADD(off, wsize_size max_sz); *)
  let i6 :=
    Lopn
      (flags_lv ++ [:: Lvar offi ])
      (Ox86 (ADD U64))
      [:: Pvar off; pword_of_int U64 (wsize_size max_sz) ]
  in

  (* if (!zf) goto l1 *)
  let i7 := Lcond (Papp1 Onot (Pvar zf)) lbl in

  map (MkLI xH) [:: i0; i1; i2; i3; i4; i5; i6; i7 ].

End CLEAR_STACK.

Definition x86_csp : clear_stack_params :=
  {|
    cs_max_ws := U256;
    cs_clear_stack_loop := x86_clear_stack_loop;
  |}.

Definition aparams :=
  {|
    is_move_op := x86_is_move_op;
    ap_csp := x86_csp;
  |}.
