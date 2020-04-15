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

From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith Utf8.
        Import Relations.
Require oseq.
Require Import psem compiler_util linear.

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
    lfn : funname;
    lc : lcmd;
    lpc  : nat; }.

Definition to_estate (s:lstate) : estate := Estate s.(lmem) s.(lvm).
Definition of_estate (s:estate) c pc := Lstate s.(emem) s.(evm) c pc.
Definition setpc (s:lstate) pc :=  Lstate s.(lmem) s.(lvm) s.(lfn) s.(lc) pc.
Definition setc (s:lstate) fn c := Lstate s.(lmem) s.(lvm) fn c s.(lpc).
Definition setcpc (s:lstate) fn c pc := Lstate s.(lmem) s.(lvm) fn c pc.

Lemma to_estate_of_estate es fn c pc:
  to_estate (of_estate es fn c pc) = es.
Proof. by case: es. Qed.

(* The [lsem] relation defines the semantics of a linear command
as the reflexive transitive closure of the [lsem1] relation that
describes the execution of the first instruction.

Therefore, [lsem s] represents all states reachable from [s].
A maximal execution (i.e., terminated without error) is caracterized by the fact that
the reached state has no instruction left to execute.
*)
Section LSEM.

Definition eval_jump d s :=
  let: (fn, lbl) := d in
  if get_fundef (lp_funcs P) fn is Some fd then
    let body := lfd_body fd in
    Let pc := find_label lbl body in
    ok (setcpc s fn body pc.+1)
  else type_error.

Definition eval_instr (i : linstr) (s1: lstate) : exec lstate :=
  match li_i i with
  | Lopn xs o es =>
    Let s2 := sem_sopn [::] o (to_estate s1) xs es in
    ok (of_estate s2 s1.(lfn) s1.(lc) s1.(lpc).+1)
  | Lalign   => ok (setpc s1 s1.(lpc).+1)
  | Llabel _ => ok (setpc s1 s1.(lpc).+1)
  | Lgoto d => eval_jump d s1
  | Ligoto e =>
    Let p := sem_pexpr [::] (to_estate s1) e >>= to_pointer in
    if decode_label p is Some d then
      eval_jump d s1
    else type_error
  | LstoreLabel x lbl =>
    if encode_label (lfn s1, lbl) is Some p then
      Let s2 := sem_sopn [::]  (Ox86 (LEA Uptr)) (to_estate s1) [:: x ] [:: wconst p ] in
      ok (of_estate s2 s1.(lfn) s1.(lc) s1.(lpc).+1)
    else type_error
  | Lcond e lbl =>
    Let b := sem_pexpr [::] (to_estate s1) e >>= to_bool in
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

Definition lsem_trans s2 s1 s3 :
  lsem s1 s2 -> lsem s2 s3 -> lsem s1 s3 :=
  rt_trans _ _ s1 s2 s3.

End LSEM.

(*
Variant lsem_fd (wrip: pointer) m1 fn va' m2 vr' : Prop :=
| LSem_fd : forall m1' fd va vm2 m2' s1 s2 vr,
    get_fundef P.(lp_funcs) fn = Some fd ->
    alloc_stack m1 fd.(lfd_align) fd.(lfd_stk_size) = ok m1' ->
    let c := fd.(lfd_body) in
    write_vars [:: vid P.(lp_stk_id)   ; vid P.(lp_rip)]
               [:: Vword (top_stack m1'); Vword wrip] (Estate m1' vmap0) = ok s1 ->
    mapM2 ErrType truncate_val fd.(lfd_tyin) va' = ok va ->
    write_vars fd.(lfd_arg) va s1 = ok s2 ->
    lsem (of_estate s2 fn c 0)
           {| lmem := m2'; lvm := vm2; lfn := fn ; lc := c; lpc := size c |} ->
    mapM (fun (x:var_i) => get_var vm2 x) fd.(lfd_res) = ok vr ->
    mapM2 ErrType truncate_val fd.(lfd_tyout) vr = ok vr' ->
    m2 = free_stack m2' fd.(lfd_stk_size) ->
    lsem_fd wrip m1 fn va' m2 vr'.
*)

End SEM.
