(** Semantics of the “one-varmap” intermediate language.
*)
Require psem one_varmap.
Import Utf8.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Export one_varmap.
Import psem var.
Import low_memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.

(** Semantics of programs in which there is a single scope for local variables.
Function arguments and returns are passed by name:
the caller puts the arguments in the right variables and read them from the right variables.

Also the instructions may be annotated with variables that are known to be free:
this semantics explicitly kills these variables before executing the corresponding instruction.

The semantics also ensures some properties:

 - No for loop
 - Calls to “rastack” functions are annotated with free variables
 - The sp_rsp local variable always hold the pointer to the top of the stack
 - The sp_rip local variable is assumed to hold the pointer to the static global data
 - The var_tmp a set of local variables free at the beginning of export functions

The semantic predicates are indexed by a set of variables which is *precisely* the set of variables that are written during the execution.
 *)

#[local] Existing Instance withsubword.

Definition kill_var (x: var) (vm: Vm.t) : Vm.t :=
  vm.[x <- undef_addr (vtype x)].

Notation kill_vars := (Sv.fold kill_var).

Definition vm_after_syscall {ovm_i : one_varmap_info} (vm:Vm.t) :=
  kill_vars syscall_kill vm.

Lemma kill_varE vm y x :
  (kill_var x vm).[y] = if x == y then undef_addr (vtype y) else vm.[y].
Proof.
  rewrite /kill_var Vm.setP; case: eqP => // ?; subst y.
  by rewrite vm_truncate_val_undef.
Qed.

Lemma kill_varsE vm xs x :
  (kill_vars xs vm).[x] = if Sv.mem x xs then undef_addr (vtype x) else vm.[x].
Proof.
  rewrite Sv_elems_eq Sv.fold_spec.
  elim: (Sv.elements xs) vm => // {xs} f xs ih vm /=.
  rewrite ih {ih} inE kill_varE eq_sym.
  by case: eqP => //= ->; case: ifP => // _; case: vm.[_] => // _; case: pundef_addr.
Qed.

Section SEM.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}
  (p : sprog)
  (var_tmp : Sv.t).

Local Notation gd := (p_globs p).

Let vgd : var := vid p.(p_extra).(sp_rip).
Let vrsp : var := vid p.(p_extra).(sp_rsp).

#[local] Notation magic_variables := (magic_variables p).

Definition ra_valid fd (ii:instr_info) (k: Sv.t) : bool :=
  match fd.(f_extra).(sf_return_address) with
  | RAstack ra _ _ =>
    if ra is Some ra then (ra != vgd) && (ra != vrsp)
    else true
  | RAreg ra _ =>
    [&& (ra != vgd), (ra != vrsp) & (~~ Sv.mem ra k) ]
  | RAnone => true
  end.

Definition ra_undef_none (ss: saved_stack) (tmp: Sv.t) :=
  Sv.union (Sv.union tmp vflags) (savedstackreg ss).

Definition ra_undef_vm_none (ss: saved_stack) (tmp: Sv.t) vm : Vm.t :=
  kill_vars (ra_undef_none ss tmp) vm.

Definition ra_undef_vm fd vm (tmp: Sv.t) : Vm.t :=
  kill_vars (ra_undef fd tmp) vm.

Definition saved_stack_valid fd (k: Sv.t) : bool :=
  if fd.(f_extra).(sf_save_stack) is SavedStackReg r
  then [&& (r != vgd), (r != vrsp) & (~~ Sv.mem r k) ]
  else true.

Definition top_stack_aligned fd m : bool :=
  is_RAnone (fd.(f_extra).(sf_return_address))
  || is_align (top_stack m) fd.(f_extra).(sf_align).

Definition set_RSP m vm : Vm.t :=
  vm.[vrsp <- Vword (top_stack m)].
#[global] Arguments set_RSP _ _%vm_scope.

Definition valid_RSP m (vm: Vm.t) : Prop :=
  vm.[vrsp] = Vword (top_stack m).

Remark valid_set_RSP m vm :
  valid_RSP m (set_RSP m vm).
Proof. by rewrite /valid_RSP Vm.setP_eq vm_truncate_val_eq. Qed.

Definition kill_tmp_call f s :=
  with_vm s (kill_vars (fd_tmp_call p f) (evm s)).

Inductive sem : Sv.t → estate → cmd → estate → Prop :=
| Eskip s :
    sem Sv.empty s [::] s

| Eseq ki kc s1 s2 s3 i c :
    sem_I ki s1 i s2 →
    sem kc s2 c s3 →
    sem (Sv.union ki kc) s1 (i :: c) s3

with sem_I : Sv.t → estate → instr → estate → Prop :=
| EmkI ii k i s1 s2:
    sem_i ii k s1 i s2 →
    disjoint k magic_variables →
    sem_I k s1 (MkI ii i) s2

with sem_i : instr_info → Sv.t → estate → instr_r → estate → Prop :=
| Eassgn ii s1 s2 (x:lval) tag ty e v v' :
    sem_pexpr true gd s1 e = ok v →
    truncate_val ty v = ok v' →
    write_lval true gd x v' s1 = ok s2 →
    sem_i ii (vrv x) s1 (Cassgn x tag ty e) s2

| Eopn ii s1 s2 t o xs es:
    sem_sopn gd o s1 xs es = ok s2 →
    sem_i ii (vrvs xs) s1 (Copn xs t o es) s2

| Esyscall ii s1 scs m s2 o xs es ves vs:
    get_vars true s1.(evm) (syscall_sig o).(scs_vin) = ok ves ->
    exec_syscall (semCallParams:= sCP_stack) s1.(escs) s1.(emem) o ves = ok (scs, m, vs) →
    write_lvals true gd {| escs := scs; emem := m; evm := vm_after_syscall s1.(evm) |}
       (to_lvals (syscall_sig o).(scs_vout)) vs = ok s2 →
    sem_i ii (Sv.union syscall_kill (vrvs (to_lvals (syscall_sig o).(scs_vout)))) s1 (Csyscall xs o es) s2

| Eif_true ii k s1 s2 e c1 c2 :
    sem_pexpr true gd s1 e = ok (Vbool true) →
    sem k s1 c1 s2 →
    sem_i ii k s1 (Cif e c1 c2) s2

| Eif_false ii k s1 s2 e c1 c2 :
    sem_pexpr true gd s1 e = ok (Vbool false) →
    sem k s1 c2 s2 →
    sem_i ii k s1 (Cif e c1 c2) s2

| Ewhile_true ii k k' krec s1 s2 s3 s4 a c e c' :
    sem k s1 c s2 →
    sem_pexpr true gd s2 e = ok (Vbool true) →
    sem k' s2 c' s3 →
    sem_I krec s3 (MkI ii (Cwhile a c e c')) s4 →
    sem_i ii (Sv.union (Sv.union k k') krec) s1 (Cwhile a c e c') s4

| Ewhile_false ii k s1 s2 a c e c' :
    sem k s1 c s2 →
    sem_pexpr true gd s2 e = ok (Vbool false) →
    sem_i ii k s1 (Cwhile a c e c') s2

| Ecall ii k s1 s2 s2' res f args xargs xres :
    mapM get_pvar args = ok xargs →
    mapM get_lvar res = ok xres →
    sem_call ii k (kill_tmp_call f s1) f s2 →
    s2' = kill_tmp_call f s2 ->
    sem_i ii (Sv.union k (fd_tmp_call p f)) s1 (Ccall res f args) s2'

with sem_call : instr_info → Sv.t → estate → funname → estate → Prop :=
| EcallRun ii k s1 s2 fn f m1 s2' :
    get_fundef (p_funcs p) fn = Some f →
    ra_valid f ii k →
    saved_stack_valid f k →
    top_stack_aligned f s1.(emem) →
    valid_RSP s1.(emem) s1.(evm) →
    alloc_stack
      s1.(emem)
      f.(f_extra).(sf_align)
      f.(f_extra).(sf_stk_sz)
      f.(f_extra).(sf_stk_ioff)
      f.(f_extra).(sf_stk_extra_sz)
      = ok m1 →
    let vm1 := ra_undef_vm f s1.(evm) var_tmp in
    sem k {| escs := s1.(escs); emem := m1; evm := set_RSP m1 vm1; |} f.(f_body) s2' →
    valid_RSP s2'.(emem) s2'.(evm) →
    let m2 := free_stack s2'.(emem) in
    s2 = {| escs := s2'.(escs); emem := m2 ; evm := set_RSP m2 s2'.(evm) |} →
    let vm := Sv.union (ra_vm f.(f_extra) var_tmp) (saved_stack_vm f) in
    sem_call ii (Sv.union k vm) s1 fn s2.

Variant sem_export_call_conclusion (scs: syscall_state_t) (m: mem) (fd: sfundef) (args: values) (vm: Vm.t) (scs': syscall_state_t) (m': mem) (res: values) : Prop :=
  | SemExportCallConclusion (m1: mem) (k: Sv.t) (m2: mem) (vm2: Vm.t) (res':values) of
    saved_stack_valid fd k &
    Sv.Subset (Sv.inter callee_saved (Sv.union k (Sv.union (ra_vm fd.(f_extra) var_tmp) (saved_stack_vm fd)))) (sv_of_list fst fd.(f_extra).(sf_to_save)) &
    alloc_stack m fd.(f_extra).(sf_align) fd.(f_extra).(sf_stk_sz) fd.(f_extra).(sf_stk_ioff) fd.(f_extra).(sf_stk_extra_sz) = ok m1 &
(*    all2 check_ty_val fd.(f_tyin) args & *)
    sem k {| escs := scs; emem := m1 ; evm := set_RSP m1 (ra_undef_vm_none fd.(f_extra).(sf_save_stack) var_tmp vm) |} fd.(f_body) {| escs:= scs'; emem := m2 ; evm := vm2 |} &
    get_var_is false vm2 fd.(f_res) = ok res' &
    List.Forall2 value_uincl res res' &
 (*   all2 check_ty_val fd.(f_tyout) res' & *)
    valid_RSP m2 vm2 &
    m' = free_stack m2.

Variant sem_export_call (gd: @extra_val_t progStack)  (scs: syscall_state_t) (m: mem) (fn: funname) (args: values)  (scs': syscall_state_t) (m': mem) (res: values) : Prop :=
  | SemExportCall (fd: sfundef) of
                  get_fundef p.(p_funcs) fn = Some fd &
      is_RAnone fd.(f_extra).(sf_return_address) &
      disjoint (sv_of_list fst fd.(f_extra).(sf_to_save)) (sv_of_list v_var fd.(f_res)) &
      ~~ Sv.mem vrsp (sv_of_list v_var fd.(f_res)) &
    ∀ vm args',
      get_var_is false vm fd.(f_params) = ok args' →
      List.Forall2 value_uincl args args' →
      valid_RSP m vm →
      vm.[vgd] = Vword gd →
      sem_export_call_conclusion scs m fd args' vm scs' m' res.

(*---------------------------------------------------*)
Variant ex3_3 (A B C : Type) (P1 P2 P3: A → B → C → Prop) : Prop :=
  Ex3_3 a b c of P1 a b c & P2 a b c & P3 a b c.

Variant ex4_10 (A B C D : Type) (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 : A → B → C → D → Prop) : Prop :=
| Ex6_14 a b c d of P1 a b c d & P2 a b c d & P3 a b c d & P4 a b c d & P5 a b c d & P6 a b c d & P7 a b c d & P8 a b c d & P9 a b c d & P10 a b c d.

(*---------------------------------------------------*)
(* Small inversion principles *)
Lemma semE k s c s' :
  sem k s c s' →
  match c with
  | [::] => k = Sv.empty ∧ s = s'
  | i :: c => ex3_3
                (λ ki kc _, k = Sv.union ki kc)
                (λ ki _ si, sem_I ki s i si)
                (λ _ kc si, sem kc si c s')
  end.
Proof. by case => // {k s c s'} ki kc s si s' i c; exists ki kc si. Qed.

Lemma sem_IE k s i s' :
  sem_I k s i s' →
  let: MkI ii r := i in
  sem_i ii k s r s' ∧ disjoint k magic_variables.
Proof. by case => {k s i s'} ii k i s1 s2 ??. Qed.

Lemma sem_iE ii k s i s' :
  sem_i ii k s i s' →
  match i with
  | Cassgn x tag ty e =>
    k = vrv x ∧
    exists2 v', sem_pexpr true gd s e >>= truncate_val ty = ok v' & write_lval true gd x v' s = ok s'
  | Copn xs t o es => k = vrvs xs ∧ sem_sopn gd o s xs es = ok s'
  | Csyscall xs o es => 
    k = Sv.union syscall_kill (vrvs (to_lvals (syscall_sig o).(scs_vout))) /\  
    ∃ scs m ves vs,
     [/\ get_vars true s.(evm) (syscall_sig o).(scs_vin) = ok ves,
         exec_syscall (semCallParams:= sCP_stack) s.(escs) s.(emem) o ves = ok (scs, m, vs) &
         write_lvals true gd {| escs := scs; emem := m; evm := vm_after_syscall s.(evm) |}
           (to_lvals (syscall_sig o).(scs_vout)) vs = ok s']
  | Cif e c1 c2 =>
    exists2 b, sem_pexpr true gd s e = ok (Vbool b) & sem k s (if b then c1 else c2) s'
  | Cwhile a c e c' =>
    ∃ kc si b,
       [/\ sem kc s c si, sem_pexpr true gd si e = ok (Vbool b) &
                       if b then ex3_3 (λ k' krec _, k = Sv.union (Sv.union kc k') krec) (λ k' _ sj, sem k' si c' sj) (λ _ krec sj, sem_I krec sj (MkI ii (Cwhile a c e c')) s') else si = s' ∧ kc = k ]
  | Ccall res f args =>
    exists2 xargs,
    mapM get_pvar args = ok xargs &
    exists2 xres,
    mapM get_lvar res = ok xres &
    exists2 s2,
    s' = (kill_tmp_call f s2) &
    exists2 k',
    k = Sv.union k' (fd_tmp_call p f) &
    sem_call ii k' (kill_tmp_call f s) f s2
  | Cfor _ _ _ => false
  end.
Proof.
  case => { ii k s i s' }; eauto.
  - by move => _ s s' x _ ty e v v' -> /= ->; eauto.
  - by move=> _ s1 scs m s2 o xs es ves vs h1 h2 h3; split => //; exists scs, m, ves, vs.
  - by move => ii k k' krec s1 s2 s3 s4 a c e c' exec_c eval_e exec_c' rec; exists k, s2, true; split; try eexists; eauto.
  by move => ii k s1 s2 a c e c' exec_c eval_e; exists k, s2, false.
Qed.

Lemma sem_callE ii k s fn s' :
  sem_call ii k s fn s' →
  ex4_10
    (λ f _ _ _, get_fundef (p_funcs p) fn = Some f)
    (λ f _ _ k', ra_valid f ii k')
    (λ f _ _ k', saved_stack_valid f k')
    (λ f _ _ _, top_stack_aligned f s.(emem))
    (λ _ _ _ _, valid_RSP s.(emem) s.(evm))
    (λ f m1 _ _, alloc_stack s.(emem) f.(f_extra).(sf_align) f.(f_extra).(sf_stk_sz) f.(f_extra).(sf_stk_ioff) f.(f_extra).(sf_stk_extra_sz) = ok m1)
    (λ f m1 s2' k',
     let vm := ra_undef_vm f s.(evm) var_tmp in
     sem k' {| escs := s.(escs); emem := m1 ; evm := set_RSP m1 vm; |} f.(f_body) s2')
    (λ _ _ s2' _, valid_RSP s2'.(emem) s2'.(evm))
    (λ f _ s2' _,
      let m2 := free_stack s2'.(emem) in
      s' = {| escs := s2'.(escs); emem := m2 ; evm := set_RSP m2 (evm s2') |})
    (λ f _ _ k',
     k = Sv.union k' (Sv.union (ra_vm f.(f_extra) var_tmp) (saved_stack_vm f))).
Proof.
  case => { ii k s fn s' } /= ii k s s' fn f m1 s2' ok_f ok_ra ok_ss ok_sp ok_RSP ok_alloc exec_body ok_RSP' /= ->.
  by exists f m1 s2' k.
Qed.

(*---------------------------------------------------*)
(* Induction principle *)
Section SEM_IND.
  Variables
    (Pc   : Sv.t → estate → cmd → estate → Prop)
    (Pi : Sv.t → estate → instr → estate → Prop)
    (Pi_r : instr_info → Sv.t → estate → instr_r → estate → Prop)
    (Pfun : instr_info → Sv.t → estate → funname → estate → Prop).

  Definition sem_Ind_nil : Prop :=
    ∀ (s : estate), Pc Sv.empty s [::] s.

  Definition sem_Ind_cons : Prop :=
    ∀ (ki kc: Sv.t) (s1 s2 s3 : estate) (i : instr) (c : cmd),
      sem_I ki s1 i s2 → Pi ki s1 i s2 →
      sem kc s2 c s3 → Pc kc s2 c s3 →
      Pc (Sv.union ki kc) s1 (i :: c) s3.

  Hypotheses
    (Hnil: sem_Ind_nil)
    (Hcons: sem_Ind_cons)
  .

  Definition sem_Ind_mkI : Prop :=
    ∀ (ii : instr_info) (k: Sv.t) (i : instr_r) (s1 s2 : estate),
      sem_i ii k s1 i s2 →
      Pi_r ii k s1 i s2 →
      disjoint k magic_variables →
      Pi k s1 (MkI ii i) s2.

  Hypothesis HmkI : sem_Ind_mkI.

  Definition sem_Ind_assgn : Prop :=
    ∀ (ii: instr_info) (s1 s2 : estate) (x : lval) (tag : assgn_tag) ty (e : pexpr) v v',
      sem_pexpr true gd s1 e = ok v →
      truncate_val ty v = ok v' →
      write_lval true gd x v' s1 = ok s2 →
      Pi_r ii (vrv x) s1 (Cassgn x tag ty e) s2.

  Definition sem_Ind_opn : Prop :=
    ∀ (ii: instr_info) (s1 s2 : estate) t (o : sopn) (xs : lvals) (es : pexprs),
      sem_sopn gd o s1 xs es = ok s2 →
      Pi_r ii (vrvs xs) s1 (Copn xs t o es) s2.

  Definition sem_Ind_syscall : Prop :=
    ∀ (ii: instr_info) (s1 s2 : estate) (o : syscall_t) (xs : lvals) (es : pexprs) scs m ves vs,
      get_vars true s1.(evm) (syscall_sig o).(scs_vin) = ok ves ->
      exec_syscall (semCallParams:= sCP_stack) s1.(escs) s1.(emem) o ves = ok (scs, m, vs) →
      write_lvals true gd {| escs := scs; emem := m; evm := vm_after_syscall s1.(evm) |}
        (to_lvals (syscall_sig o).(scs_vout)) vs = ok s2 →
      Pi_r ii (Sv.union syscall_kill (vrvs (to_lvals (syscall_sig o).(scs_vout)))) s1 (Csyscall xs o es) s2.

  Definition sem_Ind_if_true : Prop :=
    ∀ (ii: instr_info) (k: Sv.t) (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    sem_pexpr true gd s1 e = ok (Vbool true) →
    sem k s1 c1 s2 → Pc k s1 c1 s2 → Pi_r ii k s1 (Cif e c1 c2) s2.

  Definition sem_Ind_if_false : Prop :=
    ∀ (ii: instr_info) (k: Sv.t) (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    sem_pexpr true gd s1 e = ok (Vbool false) →
    sem k s1 c2 s2 → Pc k s1 c2 s2 → Pi_r ii k s1 (Cif e c1 c2) s2.

  Definition sem_Ind_while_true : Prop :=
    ∀ (ii: instr_info) (k k' krec: Sv.t) (s1 s2 s3 s4 : estate) a (c : cmd) (e : pexpr) (c' : cmd),
    sem k s1 c s2 → Pc k s1 c s2 →
    sem_pexpr true gd s2 e = ok (Vbool true) →
    sem k' s2 c' s3 → Pc k' s2 c' s3 →
    sem_I krec s3 (MkI ii (Cwhile a c e c')) s4 →
    Pi krec s3 (MkI ii (Cwhile a c e c')) s4 →
    Pi_r ii (Sv.union (Sv.union k k') krec) s1 (Cwhile a c e c') s4.

  Definition sem_Ind_while_false : Prop :=
    ∀ (ii: instr_info) (k: Sv.t) (s1 s2 : estate) a (c : cmd) (e : pexpr) (c' : cmd),
    sem k s1 c s2 →
    Pc k s1 c s2 →
    sem_pexpr true gd s2 e = ok (Vbool false) →
    Pi_r ii k s1 (Cwhile a c e c') s2.

  Hypotheses
    (Hasgn: sem_Ind_assgn)
    (Hopn: sem_Ind_opn)
    (Hsyscall: sem_Ind_syscall)
    (Hif_true: sem_Ind_if_true)
    (Hif_false: sem_Ind_if_false)
    (Hwhile_true: sem_Ind_while_true)
    (Hwhile_false: sem_Ind_while_false)
  .

  Definition sem_Ind_call : Prop :=
    ∀ (ii: instr_info) (k: Sv.t) (s1 s2: estate) res fn args xargs xres,
      mapM get_pvar args = ok xargs →
      mapM get_lvar res = ok xres →
      sem_call ii k (kill_tmp_call fn s1) fn s2 →
      Pfun ii k (kill_tmp_call fn s1) fn s2 →
      Pi_r ii (Sv.union k (fd_tmp_call p fn)) s1 (Ccall res fn args) (kill_tmp_call fn s2).

  Definition sem_Ind_proc : Prop :=
    ∀ (ii: instr_info) (k: Sv.t) (s1 s2: estate) (fn: funname) fd m1 s2',
      get_fundef (p_funcs p) fn = Some fd →
      ra_valid fd ii k →
      saved_stack_valid fd k →
      top_stack_aligned fd s1.(emem) →
      valid_RSP s1.(emem) s1.(evm) →
      alloc_stack s1.(emem) fd.(f_extra).(sf_align) fd.(f_extra).(sf_stk_sz) fd.(f_extra).(sf_stk_ioff) fd.(f_extra).(sf_stk_extra_sz) = ok m1 →
      let vm1 := ra_undef_vm fd s1.(evm) var_tmp in
      sem k {| escs := s1.(escs); emem := m1; evm := set_RSP m1 vm1; |} fd.(f_body) s2' →
      Pc  k {| escs := s1.(escs); emem := m1; evm := set_RSP m1 vm1; |} fd.(f_body) s2' →
      valid_RSP s2'.(emem) s2'.(evm) →
      let m2 := free_stack s2'.(emem) in
      s2 = {| escs := s2'.(escs); emem := m2 ; evm := set_RSP m2 (evm s2') |} →
      let vm := Sv.union k (Sv.union (ra_vm fd.(f_extra) var_tmp) (saved_stack_vm fd)) in
      Pfun ii vm s1 fn s2.

  Hypotheses
    (Hcall: sem_Ind_call)
    (Hproc: sem_Ind_proc).

  #[local] Lemma sem_Ind_call' (ii: instr_info) (k: Sv.t) (s1 s2 s2': estate) res fn args xargs xres :
      mapM get_pvar args = ok xargs →
      mapM get_lvar res = ok xres →
      sem_call ii k (kill_tmp_call fn s1) fn s2 →
      s2' = kill_tmp_call fn s2 ->
      Pfun ii k (kill_tmp_call fn s1) fn s2 →
      Pi_r ii (Sv.union k (fd_tmp_call p fn)) s1 (Ccall res fn args) s2'.
  Proof. move=> h1 h2 h3 -> h4; apply: Hcall h1 h2 h3 h4. Qed.

  Fixpoint sem_Ind (k: Sv.t) (s1 : estate) (c : cmd) (s2 : estate) (s: sem k s1 c s2) {struct s} :
    Pc k s1 c s2 :=
    match s in sem k s1 c s2 return Pc k s1 c s2 with
    | Eskip s0 => Hnil s0
    | @Eseq ki kc s1 s2 s3 i c s0 s4 =>
        @Hcons ki kc s1 s2 s3 i c s0 (@sem_I_Ind ki s1 i s2 s0) s4 (@sem_Ind kc s2 c s3 s4)
    end

  with sem_i_Ind (ii: instr_info) (k: Sv.t) (e : estate) (i : instr_r) (e0 : estate) (s : sem_i ii k e i e0) {struct s} :
    Pi_r ii k e i e0 :=
    match s in sem_i ii k s1 i s2 return Pi_r ii k s1 i s2 with
    | @Eassgn ii s1 s2 x tag ty e1 v v' h1 h2 h3 => @Hasgn ii s1 s2 x tag ty e1 v v' h1 h2 h3
    | @Eopn ii s1 s2 t o xs es e1 => @Hopn ii s1 s2 t o xs es e1
    | @Esyscall ii s1 scs m s2 o xs es ves vs h1 h2 h3 => @Hsyscall ii s1 s2 o xs es scs m ves vs h1 h2 h3
    | @Eif_true ii k s1 s2 e1 c1 c2 e2 s0 =>
      @Hif_true ii k s1 s2 e1 c1 c2 e2 s0 (@sem_Ind k s1 c1 s2 s0)
    | @Eif_false ii k s1 s2 e1 c1 c2 e2 s0 =>
      @Hif_false ii k s1 s2 e1 c1 c2 e2 s0 (@sem_Ind k s1 c2 s2 s0)
    | @Ewhile_true ii k k' krec s1 s2 s3 s4 a c e1 c' s0 e2 s5 s6 =>
      @Hwhile_true ii k k' krec s1 s2 s3 s4 a c e1 c' s0 (@sem_Ind k s1 c s2 s0) e2 s5 (@sem_Ind k' s2 c' s3 s5) s6
          (@sem_I_Ind krec s3 (MkI ii (Cwhile a c e1 c')) s4 s6)
    | @Ewhile_false ii k s1 s2 a c e1 c' s0 e2 =>
      @Hwhile_false ii k s1 s2 a c e1 c' s0 (@sem_Ind k s1 c s2 s0) e2
    | @Ecall ii k s1 s2 s2' res fn args xargs xres hargs hres exec heq =>
      @sem_Ind_call' ii k s1 s2 s2' res fn args xargs xres hargs hres exec heq
         (@sem_call_Ind ii k (kill_tmp_call fn s1) fn s2 exec)
    end

  with sem_I_Ind (k: Sv.t) (s1 : estate) (i : instr) (s2 : estate) (s : sem_I k s1 i s2) {struct s} : Pi k s1 i s2 :=
    match s in sem_I k e1 i0 e2 return Pi k e1 i0 e2 with
    | @EmkI ii k i s1 s2 exec pm => @HmkI ii k i s1 s2 exec (@sem_i_Ind ii k _ i s2 exec) pm
    end

  with sem_call_Ind (ii: instr_info) (k: Sv.t) (s1: estate) (fn: funname) (s2: estate) (s: sem_call ii k s1 fn s2) {struct s} : Pfun ii k s1 fn s2 :=
    match s with
    | @EcallRun ii k s1 s2 fn fd m1 s2' ok_fd ok_ra ok_ss ok_sp ok_rsp ok_m1 exec ok_rsp' ok_s2 =>

      @Hproc ii k s1 s2 fn fd m1 s2' ok_fd ok_ra ok_ss ok_sp ok_rsp ok_m1 exec (@sem_Ind k _ _ _ exec) ok_rsp' ok_s2
    end.

End SEM_IND.

End SEM.
