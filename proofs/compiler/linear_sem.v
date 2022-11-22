(* * Syntax and semantics of the linear language *)

(* ** Imports and settings *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith Utf8.
        Import Relations.
Require oseq.
Require Import trelation.
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
A maximal execution (i.e., terminated without error) is characterized by the fact that
the reached state has no instruction left to execute.
*)
Section LSEM.

Context {LO: LeakOp}.

Context (gd: glob_decls).

Definition eval_instr (i : linstr) (s1: lstate) : exec (lstate * leak_il) :=
  match li_i i with
  | Liopn xs o es =>
    Let s2 := sem_sopn gd o (to_estate s1) xs es in
    ok (of_estate s2.1 s1.(lc) s1.(lpc).+1, Lopnl s2.2)
  | Lialign   => ok (setpc s1 s1.(lpc).+1, Lempty0)
  | Lilabel _ => ok (setpc s1 s1.(lpc).+1, Lempty0)
  | Ligoto lbl =>
    let cpc := s1.(lpc) in 
    Let pc := find_label lbl s1.(lc) in
    ok (setpc s1 pc.+1, Lempty (Posz pc.+1 - Posz cpc))
   (* Depending on the evaluation of e in the state s1, the pc is set *)
  | Licond e lbl =>
    Let re := sem_pexpr gd (to_estate s1) e in 
    Let b :=  to_bool re.1 in
    if b then
      let cpc := s1.(lpc) in 
      Let pc := find_label lbl s1.(lc) in
      ok (setpc s1 pc.+1, (Lcondl (Posz pc.+1 - Posz cpc) re.2 b))
    else ok (setpc s1 s1.(lpc).+1, (Lcondl 1 re.2 b))
  end.

Definition find_instr (s:lstate) := oseq.onth s.(lc) s.(lpc).

Definition step (s: lstate) : exec (lstate * leak_il) :=
  if find_instr s is Some i then
    eval_instr i s
  else type_error.

Definition lsem1 (s1: lstate) (li : leak_il) (s2: lstate): Prop :=
  step s1 = ok (s2, li).

Definition leak_relation (A L: Type) : Type :=
  A -> L -> A -> Prop.

Definition lsem : leak_relation lstate (seq leak_il) :=
  trace_closure lsem1.

Lemma lsemE a tr z :
  lsem a tr z →
  if tr is t :: tr then exists2 b, lsem1 a t b & lsem b tr z else a = z.
Proof. by case: tr. Qed.

Lemma lsem_ind (Q: lstate → seq leak_il -> lstate → Prop) :
  (∀ s, Q s [::] s) →
  (∀ s1 l1 s2 l2 s3, lsem1 s1 l1 s2 → lsem s2 l2 s3 → Q s2 l2 s3 → Q s1 (l1 :: l2) s3) →
  ∀ s1 s2 l1, lsem s1 l1 s2 → Q s1 l1 s2.
Proof.
  move => R S a z tr; elim: tr a => [ | t tr ih ] a /lsemE; first by move ->.
  case => b hab hbz.
  exact: (S a t b tr z hab hbz (ih _ hbz)).
Qed.

Lemma lsem_step s2 s1 s3 l1 l2:
  lsem1 s1 l1 s2 →
  lsem s2 l2 s3 →
  lsem s1 ([::l1] ++ l2) s3.
Proof.
  exact: tc_left.
Qed.

End LSEM.

Variant lsem_fd {LO: LeakOp} gd m1 fn va' (fnlc: funname * seq leak_il) m2 vr': Prop :=
| LSem_fd : forall m1' fd va vm2 m2' s1 s2 vr,
    get_fundef P fn = Some fd ->
    alloc_stack m1 fd.(lfd_stk_size) = ok m1' ->
    let c := fd.(lfd_body) in
    write_var  (S.vstk fd.(lfd_nstk)) (Vword (top_stack m1')) (Estate m1' vmap0) = ok s1 ->
    mapM2 ErrType truncate_val fd.(lfd_tyin) va' = ok va ->
    write_vars fd.(lfd_arg) va s1 = ok s2 ->
    lsem gd (of_estate s2 c 0) fnlc.2
           {| lmem := m2'; lvm := vm2; lc := c; lpc := size c |} ->
    mapM (fun (x:var_i) => get_var vm2 x) fd.(lfd_res) = ok vr ->
    mapM2 ErrType truncate_val fd.(lfd_tyout) vr = ok vr' ->
    m2 = free_stack m2' fd.(lfd_stk_size) ->
    lsem_fd gd m1 fn va' fnlc m2 vr'.

End SEM.