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
Require Import sopn psem compiler.
Require Import arch_decl arch_extra expr x86_decl x86_instr_decl x86_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition is_move_op (o : sopn.asm_op_t) :=
  match o with
  | BaseOp (None, MOV _) | BaseOp (None, VMOVDQU _) => true
  | _ => false
  end.

Definition aparams := mk_aparams is_move_op.

Definition all_vars := 
  let r  := set_of_var_seq Sv.empty (List.map to_var registers) in
  let xr := set_of_var_seq Sv.empty (List.map to_var xmm_registers) in
  let f  := set_of_var_seq Sv.empty (List.map to_var rflags) in
  Sv.union (Sv.union r xr) f.

(* FIXME: this is defined in x86_sem *)
Definition x86_callee_saved : seq register :=
  [:: RBX; RBP; RSP; R12; R13; R14; R15 ].

Definition callee_saved := set_of_var_seq Sv.empty (List.map to_var x86_callee_saved).

Definition caller_saved := Sv.diff all_vars callee_saved.

Definition write_syscall : Sv.t := caller_saved.

Definition x86_arguments := [:: RDI; RSI; RDX; RCX; R8; R9].

Definition x86_ret := [:: RAX; RDX].

Definition syscall_vsig (o : syscall_t) := 
  match o with
  | GetRandom _ => (List.map to_var [:: RDI; RSI], List.map to_var [::RAX])
  end.

Definition sparams := mk_sparams write_syscall syscall_vsig callee_saved.
  
