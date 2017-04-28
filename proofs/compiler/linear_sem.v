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
Require Import sem compiler_util stack_alloc stack_sem linear.

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
    lc   : lcmd; }.

Definition to_estate (s:lstate) := Estate s.(lmem) s.(lvm).
Definition of_estate (s:estate) c := Lstate s.(emem) s.(evm) c.
Definition setc (s:lstate) c :=  Lstate s.(lmem) s.(lvm) c.

(* The [lsem c] relation defines the semantics of a linear command c
as the reflexive transitive closure of the [lsem1 c] relation that
describes the execution of the first instruction.

Therefore, [lsem c s] represents all states reachable from [s] by partial executions of [c].
A maximal execution (i.e., terminated without error) is caracterized by the fact that
the reached state has no instruction left to execute.
*)
Section LSEM.

Context (c: lcmd).

Variant lsem1 : lstate -> lstate -> Prop:=
| LSem_assgn : forall s1 s2 ii x tag e cs,
    s1.(lc) = MkLI ii (Lassgn x tag e) :: cs ->
    (Let v := sem_pexpr (to_estate s1) e in write_lval x v (to_estate s1)) = ok s2 ->
    lsem1 s1 (of_estate s2 cs)
| LSem_opn : forall s1 s2 ii xs o es cs,
    s1.(lc) = MkLI ii (Lopn xs o es) :: cs ->
    sem_pexprs (to_estate s1) es >>= sem_sopn o >>= (write_lvals (to_estate s1) xs) = ok s2 ->
    lsem1 s1 (of_estate s2 cs)
| LSem_lbl : forall s1 ii lbl cs,
    s1.(lc) = MkLI ii (Llabel lbl) :: cs ->
    lsem1 s1 (setc s1 cs)
| LSem_goto : forall s1 ii lbl cs cs',
    s1.(lc) = MkLI ii (Lgoto lbl) :: cs ->
    find_label lbl c = Some cs' ->
    lsem1 s1 (setc s1 cs')
| LSem_condTrue : forall ii s1 e lbl cs cs',
    s1.(lc) = MkLI ii (Lcond e lbl) :: cs ->
    sem_pexpr (to_estate s1) e >>= to_bool = ok true ->
    find_label lbl c = Some cs' ->
    lsem1 s1 (setc s1 cs')
| LSem_condFalse : forall ii s1 e lbl cs,
    s1.(lc) = MkLI ii (Lcond e lbl) :: cs ->
    sem_pexpr (to_estate s1) e >>= to_bool = ok false ->
    lsem1 s1 (setc s1 cs).

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

Inductive lsem_fd m1 fn va m2 vr : Prop :=
| LSem_fd : forall p fd vm2 m2' s1 s2,
    get_fundef P fn = Some fd ->
    alloc_stack m1 fd.(lfd_stk_size) = ok p ->
    let c := fd.(lfd_body) in
    write_var  (S.vstk fd.(lfd_nstk)) p.1 (Estate p.2 vmap0) = ok s1 ->
    write_vars fd.(lfd_arg) va s1 = ok s2 ->
    lsem c (of_estate s2 c)
           {| lmem := m2'; lvm := vm2; lc := [::] |} ->
    mapM (fun (x:var_i) => get_var vm2 x) fd.(lfd_res) = ok vr ->
    m2 = free_stack m2' p.1 fd.(lfd_stk_size) ->
    List.Forall is_full_array vr ->
    lsem_fd m1 fn va m2 vr.

Definition lsem_trans s2 s1 s3 c :
  lsem c s1 s2 -> lsem c s2 s3 -> lsem c s1 s3 :=
  rt_trans _ _ s1 s2 s3.

End SEM.