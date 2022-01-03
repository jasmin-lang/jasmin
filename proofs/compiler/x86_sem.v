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


(* -------------------------------------------------------------------- *)
Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import ZArith utils strings low_memory word global oseq.
Import Utf8 Relation_Operators.
Import Memory.
Require Import sem_type arch_decl x86_decl x86_instr_decl.
Require Export arch_sem.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition eval_cond (get : rflag -> result error bool) (c : condt) :=
  match c with
  | O_ct   => get OF
  | NO_ct  => Let b := get OF in ok (~~ b)
  | B_ct   => get CF
  | NB_ct  => Let b := get CF in ok (~~ b)
  | E_ct   => get ZF
  | NE_ct  => Let b := get ZF in ok (~~ b)
  | S_ct   => get SF
  | NS_ct  => Let b := get SF in ok (~~ b)
  | P_ct   => get PF
  | NP_ct  => Let b := get PF in ok (~~ b)

  | BE_ct =>
      Let cf := get CF in
      Let zf := get ZF in ok (cf || zf)

  | NBE_ct =>
      Let cf := get CF in
      Let zf := get ZF in ok (~~ cf && ~~ zf)

  | L_ct =>
      Let sf  := get SF in
      Let of_ := get OF in ok (sf != of_)

  | NL_ct =>
      Let sf  := get SF in
      Let of_ := get OF in ok (sf == of_)

  | LE_ct =>
      Let zf  := get ZF in
      Let sf  := get SF in
      Let of_ := get OF in ok (zf || (sf != of_))

  | NLE_ct =>
      Let zf  := get ZF in
      Let sf  := get SF in
      Let of_ := get OF in ok (~~ zf && (sf == of_))
  end.

Instance x86 : asm register xmm_register rflag condt x86_op :=
  { eval_cond := eval_cond }.

Definition x86_mem := @asmmem _ _ _ _ _ x86.
Definition x86_prog := @asm_prog register _ _ _ _ _ x86_op_decl.
Definition x86_state := @asm_state _ _ _ _ _ x86.
Definition x86sem := @asmsem _ _ _ _ _ x86.
Definition x86_fundef := @asm_fundef _ _ _ _ _ _ x86_op_decl.

(* Semantics of an export function
FIXME: this is mostly independent of the architecture and may be partially moved to arch_sem

  - The function exists and is “export”
  - Execution runs from the initial state to the final state
  - Callee-saved registers are preserved

TODO: arguments / results are well-typed
 *)

Definition x86_callee_saved : seq register :=
  [:: RBX; RBP; RDI; RSI; RSP; R12; R13; R14; R15 ].

Definition preserved_register (r: register) : relation x86_mem :=
  λ s1 s2,
    s1.(asm_reg) r = s2.(asm_reg) r.

Variant x86sem_exportcall (p: asm_prog) (fn: funname) (m m': asmmem) : Prop :=
  | X86sem_exportcall (fd: x86_fundef) of
      get_fundef p.(asm_funcs) fn = Some fd
    & fd.(asm_fd_export)
    & x86sem p
             {| asm_m := m ; asm_f := fn ; asm_c := asm_fd_body fd ; asm_ip := 0 |}
             {| asm_m := m' ; asm_f := fn ; asm_c := asm_fd_body fd ; asm_ip := size fd.(asm_fd_body) |}
    (* TODO: & {in x86_callee_saved, ∀ r, preserved_register r m m'}
    question: how to state this at the linear level?
     *)
.

(* TODO: not sure there needs to be a file [x86_sem], [arch_sem] seems enough. *)
