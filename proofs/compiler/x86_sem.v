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

Definition x86_eval_cond (get : rflag -> result error bool) (c : condt) :=
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

Instance x86 : asm register register_ext xmm_register rflag condt x86_op :=
  {| eval_cond := x86_eval_cond
   ; stack_pointer_register := RSP |}.

Definition x86_mem := @asmmem _ _ _ _ _ _ x86.
Definition x86_prog := @asm_prog register _ _ _ _ _ _ x86_op_decl.
Definition x86_state := @asm_state _ _ _ _ _ _ x86.
Definition x86sem := @asmsem _ _ _ _ _ _ x86.
Definition x86_fundef := @asm_fundef _ _ _ _ _ _ _ x86_op_decl.

(* Semantics of an export function
FIXME: this is mostly independent of the architecture and may be partially moved to arch_sem

  - The function exists and is “export”
  - Execution runs from the initial state to the final state
  - Callee-saved registers are preserved

TODO: arguments / results are well-typed
 *)

Definition x86_callee_saved : seq register :=
  [:: RBX; RBP; RSP; R12; R13; R14; R15 ].

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
    & {in x86_callee_saved, ∀ r, preserved_register r m m'}
.

(* TODO: not sure there needs to be a file [x86_sem], [arch_sem] seems enough. *)
