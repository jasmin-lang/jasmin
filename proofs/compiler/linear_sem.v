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
Require Import ZArith Utf8.
        Import Relations.
Require oseq.
Require Import psem compiler_util stack_alloc stack_sem linear.

Import Memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Section SEM.

Variable P: lprog.

(* --------------------------------------------------------------------------- *)
(* Semantic                                                                    *)

Record lstate := Lstate
  { lmem : mem;
    lvm  : vmap;
    lc : lcmd;
    lpc  : nat; }.

Definition to_estate (s:lstate) := Estate s.(lmem) s.(lvm).
Definition of_estate (s:estate) c pc := Lstate s.(emem) s.(evm) c pc.
Definition setpc (s:lstate) pc :=  Lstate s.(lmem) s.(lvm) s.(lc) pc.
Definition setc (s:lstate) c := Lstate s.(lmem) s.(lvm) c s.(lpc).

Lemma to_estate_of_estate es c pc:
  to_estate (of_estate es c pc) = es.
Proof. by case: es. Qed.

(* The [lsem] relation defines the semantics of a linear command
as the reflexive transitive closure of the [lsem1] relation that
describes the execution of the first instruction.

Therefore, [lsem s] represents all states reachable from [s].
A maximal execution (i.e., terminated without error) is caracterized by the fact that
the reached state has no instruction left to execute.
*)
Section LSEM.

Context (gd: glob_decls).

Definition eval_instr (i : linstr) (s1: lstate) : exec lstate :=
  match li_i i with
  | Lopn xs o es =>
    Let s2 := sem_sopn gd o (to_estate s1) xs es in
    ok (of_estate s2 s1.(lc) s1.(lpc).+1)
  | Llabel _ => ok (setpc s1 s1.(lpc).+1)
  | Lgoto lbl =>
    Let pc := find_label lbl s1.(lc) in
    ok (setpc s1 pc.+1)
  | Lcond e lbl =>
    Let b := sem_pexpr gd (to_estate s1) e >>= to_bool in
    if b then
      Let pc := find_label lbl s1.(lc) in
      ok (setpc s1 pc.+1)
    else ok (setpc s1 s1.(lpc).+1)
  end.

Definition find_instr (s:lstate) := oseq.onth s.(lc) s.(lpc).

Definition step (s: lstate) : exec lstate :=
  if find_instr s is Some i then
    eval_instr i s
  else type_error.

Definition lsem1 (s1 s2: lstate) : Prop :=
  step s1 = ok s2.

Definition lsem : relation lstate := clos_refl_trans lstate lsem1.

Lemma lsem_ind (Q: lstate → lstate → Prop) :
  (∀ s, Q s s) →
  (∀ s1 s2 s3, lsem1 s1 s2 → lsem s2 s3 → Q s2 s3 → Q s1 s3) →
  ∀ s1 s2, lsem s1 s2 → Q s1 s2.
Proof.
  move=> R S s1 s2 H; apply clos_rt_rt1n in H.
  specialize (λ s1 s2 s3 X Y, S s1 s2 s3 X (clos_rt1n_rt _ _ _ _ Y)).
  by elim: H.
Qed.

Lemma lsem_step s2 s1 s3 :
  lsem1 s1 s2 →
  lsem s2 s3 →
  lsem s1 s3.
Proof.
  by move=> H; apply: rt_trans; apply: rt_step.
Qed.

End LSEM.

Variant lsem_fd gd m1 fn va' m2 vr' : Prop :=
| LSem_fd : forall m1' fd va vm2 m2' s1 s2 vr,
    get_fundef P fn = Some fd ->
    alloc_stack m1 fd.(lfd_stk_size) = ok m1' ->
    let c := fd.(lfd_body) in
    write_var  (S.vstk fd.(lfd_nstk)) (Vword (top_stack m1')) (Estate m1' vmap0) = ok s1 ->
    mapM2 ErrType truncate_val fd.(lfd_tyin) va' = ok va ->
    write_vars fd.(lfd_arg) va s1 = ok s2 ->
    lsem gd (of_estate s2 c 0)
           {| lmem := m2'; lvm := vm2; lc := c; lpc := size c |} ->
    mapM (fun (x:var_i) => get_var vm2 x) fd.(lfd_res) = ok vr ->
    mapM2 ErrType truncate_val fd.(lfd_tyout) vr = ok vr' ->
    m2 = free_stack m2' fd.(lfd_stk_size) ->
    lsem_fd gd m1 fn va' m2 vr'.

Definition lsem_trans gd s2 s1 s3 :
  lsem gd s1 s2 -> lsem gd s2 s3 -> lsem gd s1 s3 :=
  rt_trans _ _ s1 s2 s3.

End SEM.
