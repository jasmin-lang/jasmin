(* * Semantics of the linear language *)

(* ** Imports and settings *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg.
Require Import ZArith Utf8.
        Import Relations.
Require oseq.
Require Import psem fexpr_sem compiler_util label one_varmap linear sem_one_varmap.

Import Memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

#[local] Existing Instance withsubword.

Section SEM.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}
  (P : lprog).

Definition get_label (i : linstr) : option label :=
  if li_i i is Llabel ExternalLabel lbl then Some lbl else None.

Definition label_in_lcmd (body: lcmd) : seq label :=
  pmap get_label body.

Definition label_in_lprog : seq remote_label :=
  [seq (f.1, lbl) | f <- lp_funcs P, lbl <- label_in_lcmd (lfd_body f.2) ].

Notation labels := label_in_lprog.

(* --------------------------------------------------------------------------- *)
(* Semantic                                                                    *)

Record lstate := Lstate
  { lscs : syscall_state_t;
    lmem : mem;
    lvm  : Vm.t;
    lfn : funname;
    lpc  : nat; }.

Definition to_estate (s:lstate) : estate := Estate s.(lscs) s.(lmem) s.(lvm).
Definition of_estate (s:estate) fn pc := Lstate s.(escs) s.(emem) s.(evm) fn pc.
Definition setpc (s:lstate) pc :=  Lstate s.(lscs) s.(lmem) s.(lvm) s.(lfn) pc.
Definition setc (s:lstate) fn := Lstate s.(lscs) s.(lmem) s.(lvm) fn s.(lpc).
Definition setcpc (s:lstate) fn pc := Lstate s.(lscs) s.(lmem) s.(lvm) fn pc.
Definition lset_estate' (ls : lstate) (s : estate) : lstate :=
  Eval hnf in of_estate s ls.(lfn) ls.(lpc).
Definition lset_estate
  (ls : lstate) (scs : syscall_state) (m : mem) (vm : Vm.t) : lstate :=
  Eval hnf in lset_estate' ls {| escs := scs; emem := m; evm := vm; |}.
Definition lset_mem_vm (ls : lstate) (m : mem) (vm : Vm.t) : lstate :=
  Eval hnf in lset_estate ls (lscs ls) m vm.
Definition lset_mem (ls : lstate) (m : mem) : lstate :=
  Eval hnf in lset_mem_vm ls m (lvm ls).
Definition lset_vm (ls : lstate) (vm : Vm.t) : lstate :=
  Eval hnf in lset_mem_vm ls (lmem ls) vm.
Definition lnext_pc (ls : lstate) : lstate :=
  Eval hnf in setpc ls (lpc ls).+1.

Lemma to_estate_of_estate es fn pc:
  to_estate (of_estate es fn pc) = es.
Proof. by case: es. Qed.

Lemma of_estate_to_estate ls :
  of_estate (to_estate ls) (lfn ls) (lpc ls) = ls.
Proof. by case: ls. Qed.


(* The [lsem] relation defines the semantics of a linear command
as the reflexive transitive closure of the [lsem1] relation that
describes the execution of the first instruction.

Therefore, [lsem s] represents all states reachable from [s].
A maximal execution (i.e., terminated without error) is caracterized by the fact that
the reached state has no instruction left to execute.
*)
Definition eval_jump d s :=
  let: (fn, lbl) := d in
  Let body :=
    if get_fundef (lp_funcs P) fn is Some fd then
      ok (lfd_body fd)
    else type_error
  in
  Let pc := find_label lbl body in
  ok (setcpc s fn pc.+1).

Definition find_instr (s:lstate) :=
  let%opt fd := get_fundef (lp_funcs P) s.(lfn) in
  oseq.onth (lfd_body fd) s.(lpc).

Definition get_label_after_pc (s:lstate) :=
  if find_instr (lnext_pc s) is Some i then
    if li_i i is Llabel ExternalLabel l then ok l
    else type_error
  else type_error.

Definition sem_fopn_args (p : fopn_args) (s: estate) :=
  let: (xs,o,es) := p in
  Let args := sem_rexprs s es in
  Let res := exec_sopn o args in
  write_lexprs xs res s.

Definition sem_fopns_args := foldM sem_fopn_args.

Definition eval_instr (i : linstr) (s1: lstate) : exec lstate :=
  match li_i i with
  | Lopn xs o es =>
    let s := to_estate s1 in
    Let args := sem_rexprs s es in
    Let res := exec_sopn o args in
    Let s' := write_lexprs xs res s in
    ok (lnext_pc (lset_estate' s1 s'))
  | Lsyscall o =>
    let sig := syscall_sig o in
    Let ves := get_vars true s1.(lvm) sig.(scs_vin) in
    Let: (scs, m, vs) :=
      exec_syscall (semCallParams := sCP_stack) s1.(lscs) s1.(lmem) o ves
    in
    let s :=
      {|
        escs := scs;
        emem := m;
        evm := vm_after_syscall s1.(lvm);
      |}
    in
    Let s' := write_lvals true [::] s (to_lvals sig.(scs_vout)) vs in
    ok (lnext_pc (lset_estate' s1 s'))
  | Lcall None d =>
    let vrsp := v_var (vid (lp_rsp P)) in
    Let sp := get_var true s1.(lvm) vrsp >>= to_pointer in
    let nsp := (sp - wrepr Uptr (wsize_size Uptr))%R in
    Let vm := set_var true s1.(lvm) vrsp (Vword nsp) in
    Let lbl := get_label_after_pc s1 in
    Let p := rencode_label labels (lfn s1, lbl) in
    Let m := write s1.(lmem) Aligned nsp p in
    eval_jump d (lset_mem_vm s1 m vm)
  | Lcall (Some r) d =>
    Let lbl := get_label_after_pc s1 in
    Let p := rencode_label labels (lfn s1, lbl) in
    Let vm := set_var true s1.(lvm) r (Vword p) in
    eval_jump d (lset_vm s1 vm)
  | Lret =>
    let vrsp := v_var (vid (lp_rsp P)) in
    Let sp := get_var true s1.(lvm) vrsp >>= to_pointer in
    let nsp := (sp + wrepr Uptr (wsize_size Uptr))%R in
    Let p  := read s1.(lmem) Aligned sp Uptr in
    Let vm := set_var true s1.(lvm) vrsp (Vword nsp) in
    Let d := rdecode_label labels p in
    eval_jump d (lset_vm s1 vm)
  | Lalign   => ok (lnext_pc s1)
  | Llabel _ _ => ok (lnext_pc s1)
  | Lgoto d => eval_jump d s1
  | Ligoto e =>
    Let p := sem_rexpr s1.(lmem) s1.(lvm) e >>= to_pointer in
    Let d := rdecode_label labels p in
    eval_jump d s1
  | LstoreLabel x lbl =>
    Let p := rencode_label labels (lfn s1, lbl) in
    Let vm := set_var true s1.(lvm) x (Vword p) in
    ok (lnext_pc (lset_vm s1 vm))
  | Lcond e lbl =>
    Let b := sem_fexpr s1.(lvm) e >>= to_bool in
    if b then
      eval_jump (s1.(lfn),lbl) s1
    else ok (lnext_pc s1)
  end.

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

Lemma lsem_step_end s2 s1 s3 :
  lsem s1 s2 →
  lsem1 s2 s3 →
  lsem s1 s3.
Proof.
  move => h12 h23; apply: rt_trans; first exact: h12.
  exact: rt_step.
Qed.

Definition lsem_trans s2 s1 s3 :
  lsem s1 s2 -> lsem s2 s3 -> lsem s1 s3 :=
  rt_trans _ _ s1 s2 s3.

Lemma lsem_ind_r (Q: lstate → lstate → Prop) :
  (∀ s, Q s s) →
  (∀ s1 s2 s3, lsem s1 s2 → lsem1 s2 s3 → Q s1 s2 → Q s1 s3) →
  ∀ s1 s2, lsem s1 s2 → Q s1 s2.
Proof.
  move=> R S s1 s2 H; apply clos_rt_rtn1 in H.
  specialize (λ s1 s2 s3 X Y, S s1 s2 s3 (clos_rtn1_rt _ _ _ _ X) Y).
  by elim: H => // s2' s3' H12 H23 Q12; apply: (S s1 s2' s3' H23 H12 Q12).
Qed.

Lemma lsem1_fun s1 s2 s3 :
  lsem1 s1 s2 ->
  lsem1 s1 s3 ->
  s2 = s3.
Proof.
  by rewrite /lsem1 => ->; t_xrbindP.
Qed.

Lemma lsem_disj1 s1 s2 s3 :
  lsem1 s1 s2 ->
  lsem s1 s3 ->
  (s1 = s3) \/ lsem s2 s3.
Proof.
  move => H12 H13; move: s1 s3 H13 s2 H12.
  apply: lsem_ind; first by left.
  move => s1 s2 s3 H12 H23 _ s2' H12'.
  by right; rewrite (lsem1_fun H12' H12).
Qed.

Lemma lsem_disj s1 s2 s3 :
  lsem s1 s2 ->
  lsem s1 s3 ->
  lsem s2 s3 \/ lsem s3 s2.
Proof.
  move => Hp12; move: s1 s2 Hp12 s3.
  apply: lsem_ind; first by left.
  move => s1 s2 s2' H1p12 Hp22' IHdisj s3 Hp13.
  have:= (lsem_disj1 H1p12 Hp13).
  case; last by apply: IHdisj.
  by move => <-; right; apply: (lsem_trans _ Hp22'); apply: rt_step.
Qed.

Lemma lsem_split_start a z :
  lsem a z →
  a = z ∨ exists2 b, lsem1 a b & lsem b z.
Proof.
  case/clos_rt_rt1n_iff; first by left.
  by move => b{}z ab /clos_rt_rt1n_iff bz; right; exists b.
Qed.

(* Linear execution state is final when it reaches the point after the last instruction. *)
Definition lsem_final (s: lstate) : Prop :=
  exists2 fd, get_fundef (lp_funcs P) (lfn s) = Some fd & lpc s = size fd.(lfd_body).

Lemma lsem_final_nostep (s s': lstate) :
  lsem_final s →
  ¬ lsem1 s s'.
Proof.
  rewrite /lsem1 /step /find_instr => - [] fd -> h.
  by rewrite oseq.onth_default // -h.
Qed.

Lemma lsem_final_stutter (s s': lstate) :
  lsem s s' →
  lsem_final s →
  s' = s.
Proof.
  elim/lsem_ind; first by [].
  by clear => s s' ? k _ _ /lsem_final_nostep /(_ k).
Qed.

Definition ls_export_initial scs m vm fn :=
  {|
    lscs := scs;
    lmem := m;
    lvm := vm;
    lfn := fn;
    lpc := 0;
  |}.

Definition ls_export_final scs m vm fn fd :=
  {|
    lscs := scs;
    lmem := m;
    lvm := vm;
    lfn := fn;
    lpc := size (lfd_body fd);
  |}.

Variant lsem_exportcall (scs:syscall_state_t) (m: mem) (fn: funname) (vm: Vm.t) (scs':syscall_state_t) (m': mem) (vm': Vm.t) : Prop :=
| Lsem_exportcall (fd: lfundef) of
    get_fundef P.(lp_funcs) fn = Some fd
  & lfd_export fd
  & lsem (ls_export_initial scs m vm fn) (ls_export_final scs' m' vm' fn fd)
  & vm =[ callee_saved ] vm'
.

End SEM.

Arguments lsem_split_start {_ _ _ _ _ _}.
