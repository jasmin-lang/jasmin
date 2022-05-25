(** Semantics of the “one-varmap” intermediate language.
*)
Require psem one_varmap.
Import Utf8.
Import all_ssreflect.
Export one_varmap.
Import psem var.
Import low_memory.
Require Import arch_decl arch_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.

Local Open Scope vmap_scope.

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
 - The var_tmp local variable is free at the beginning of export functions

The semantic predicates are indexed by a set of variables which is *precisely* the set of variables that are written during the execution.
 *)

Section ASM_EXTRA.

Context {reg regx xreg rflag cond asm_op extra_op} {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}.

Definition get_pvar (e: pexpr) : exec var :=
  if e is Pvar {| gv := x ; gs := Slocal |} then ok (v_var x) else type_error.

Definition get_lvar (x: lval) : exec var :=
  if x is Lvar x then ok (v_var x) else type_error.

Definition kill_var (x: var) (vm: vmap) : vmap :=
  vm.[x <- pundef_addr (vtype x)].

End ASM_EXTRA.

Notation kill_vars := (Sv.fold kill_var).

Section ASM_EXTRA.

Context {reg regx xreg rflag cond asm_op extra_op} {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}.

Lemma kill_varE vm y x :
  ((kill_var x vm).[y] = if x == y then pundef_addr (vtype y) else vm.[y])%vmap.
Proof.
  by rewrite /kill_var Fv.setP; case: eqP => // ?; subst y.
Qed.

Lemma kill_varsE vm xs x :
  ((kill_vars xs vm).[x] = if Sv.mem x xs then pundef_addr (vtype x) else vm.[x])%vmap.
Proof.
  rewrite Sv_elems_eq Sv.fold_spec.
  elim: (Sv.elements xs) vm => // {xs} f xs ih vm /=.
  rewrite ih {ih} inE kill_varE eq_sym.
  by case: eqP => //= ->; case: ifP => // _; case: vm.[_] => // _; case: pundef_addr.
Qed.

Lemma kill_vars_uincl vm xs :
  wf_vm vm ->
  vm_uincl (kill_vars xs vm) vm.
Proof.
  move => hwf x; rewrite kill_varsE.
  case: ifP => // _.
  case: vm.[x] (hwf x)=> // [v | e].
  + by move=> _; apply eval_uincl_undef.
  case: e => //; case: (vtype x) => //.
Qed.

Section SEM.

Context
  (p: sprog)
  (extra_free_registers: instr_info -> option var)
  (var_tmp: var)
  (callee_saved: Sv.t).

Local Notation gd := (p_globs p).

Definition kill_extra_register_vmap ii (vm: vmap) : vmap :=
  if extra_free_registers ii is Some x
  then if vm.[x] is Ok _ then vm.[x <- pundef_addr (vtype x) ] else vm
  else vm.

Definition kill_extra_register ii (s: estate) : estate :=
  with_vm s (kill_extra_register_vmap ii s.(evm)).

Remark kill_extra_register_vm_uincl ii s :
  vm_uincl (kill_extra_register ii s).(evm) (evm s).
Proof.
  rewrite /= /kill_extra_register_vmap.
  case: extra_free_registers => // x y.
  case hx: (evm s).[x] => [ v | ] //; case: (x =P y).
  + move => <- {y}; rewrite hx Fv.setP_eq; apply: eval_uincl_undef; exact: subtype_refl.
  by move => /eqP x_ne_y; rewrite Fv.setP_neq.
Qed.

Let vgd : var := vid p.(p_extra).(sp_rip).
Let vrsp : var := vid p.(p_extra).(sp_rsp).

#[local] Notation magic_variables := (magic_variables p).
#[local] Notation extra_free_registers_at := (extra_free_registers_at extra_free_registers).

Definition ra_valid fd ii (k: Sv.t) (x: var) : bool :=
  match fd.(f_extra).(sf_return_address) with
  | RAstack _ =>
    extra_free_registers ii != None
  | RAreg ra =>
    [&& (ra != vgd), (ra != vrsp) & (~~ Sv.mem ra k) ]
  | RAnone => true
  end.

Definition ra_undef_none (ss: saved_stack) (x: var) :=
  Sv.union (Sv.add x (sv_of_flags rflags)) (savedstackreg ss).

Definition ra_undef_vm_none (ss: saved_stack) (x: var) vm : vmap :=
  kill_vars (ra_undef_none ss x) vm.

Definition ra_undef_vm fd vm (x: var) : vmap :=
  kill_vars (ra_undef fd x) vm.

Definition saved_stack_valid fd (k: Sv.t) : bool :=
  if fd.(f_extra).(sf_save_stack) is SavedStackReg r
  then [&& (r != vgd), (r != vrsp) & (~~ Sv.mem r k) ]
  else true.

Definition efr_valid ii i : bool :=
  if extra_free_registers ii is Some r
  then [&& r != vgd, r != vrsp, vtype r == sword Uptr &
           if i is Cwhile _ _ _ _ then false else true]
  else true.

Definition top_stack_aligned fd st : bool :=
  (fd.(f_extra).(sf_return_address) == RAnone)
  || is_align (top_stack st.(emem)) fd.(f_extra).(sf_align).

Definition set_RSP m vm : vmap :=
  vm.[vrsp <- ok (pword_of_word (top_stack m))].
#[global] Arguments set_RSP _ _%vmap_scope.

Definition valid_RSP m (vm: vmap) : Prop :=
  vm.[vrsp] = ok (pword_of_word (top_stack m)).

Remark valid_set_RSP m vm :
  valid_RSP m (set_RSP m vm).
Proof. by rewrite /valid_RSP Fv.setP_eq. Qed.

Inductive sem : Sv.t → estate → cmd → estate → Prop :=
| Eskip s :
    sem Sv.empty s [::] s

| Eseq ki kc s1 s2 s3 i c :
    sem_I ki s1 i s2 →
    sem kc s2 c s3 →
    sem (Sv.union ki kc) s1 (i :: c) s3

with sem_I : Sv.t → estate → instr → estate → Prop :=
| EmkI ii k i s1 s2:
    efr_valid ii i →
    sem_i ii k (kill_extra_register ii s1) i s2 →
    disjoint k magic_variables →
    sem_I (Sv.union (extra_free_registers_at ii) k) s1 (MkI ii i) s2

with sem_i : instr_info → Sv.t → estate → instr_r → estate → Prop :=
| Eassgn ii s1 s2 (x:lval) tag ty e v v' :
    sem_pexpr gd s1 e = ok v →
    truncate_val ty v = ok v' →
    write_lval gd x v' s1 = ok s2 →
    sem_i ii (vrv x) s1 (Cassgn x tag ty e) s2

| Eopn ii s1 s2 t o xs es:
    sem_sopn gd o s1 xs es = ok s2 →
    sem_i ii (vrvs xs) s1 (Copn xs t o es) s2

| Eif_true ii k s1 s2 e c1 c2 :
    sem_pexpr gd s1 e = ok (Vbool true) →
    sem k s1 c1 s2 →
    sem_i ii k s1 (Cif e c1 c2) s2

| Eif_false ii k s1 s2 e c1 c2 :
    sem_pexpr gd s1 e = ok (Vbool false) →
    sem k s1 c2 s2 →
    sem_i ii k s1 (Cif e c1 c2) s2

| Ewhile_true ii k k' krec s1 s2 s3 s4 a c e c' :
    sem k s1 c s2 →
    sem_pexpr gd s2 e = ok (Vbool true) →
    sem k' s2 c' s3 →
    sem_I krec s3 (MkI ii (Cwhile a c e c')) s4 →
    sem_i ii (Sv.union (Sv.union k k') krec) s1 (Cwhile a c e c') s4

| Ewhile_false ii k s1 s2 a c e c' :
    sem k s1 c s2 →
    sem_pexpr gd s2 e = ok (Vbool false) →
    sem_i ii k s1 (Cwhile a c e c') s2

| Ecall ii k s1 s2 ini res f args xargs xres :
    mapM get_pvar args = ok xargs →
    mapM get_lvar res = ok xres →
    sem_call ii k s1 f s2 →
    sem_i ii k s1 (Ccall ini res f args) s2

with sem_call : instr_info → Sv.t → estate → funname → estate → Prop :=
| EcallRun ii k s1 s2 fn f args m1 s2' res :
    get_fundef (p_funcs p) fn = Some f →
    ra_valid f ii k var_tmp →
    saved_stack_valid f k →
    top_stack_aligned f s1 →
    valid_RSP s1.(emem) s1.(evm) →
    alloc_stack
      s1.(emem)
      f.(f_extra).(sf_align)
      f.(f_extra).(sf_stk_sz)
      f.(f_extra).(sf_stk_extra_sz)
      = ok m1 →
    mapM (λ x : var_i, get_var s1.(evm) x) f.(f_params) = ok args →
    all2 check_ty_val f.(f_tyin) args →
    let vm1 := ra_undef_vm f s1.(evm) var_tmp in
    sem k {| emem := m1; evm := set_RSP m1 vm1; |} f.(f_body) s2' →
    mapM (λ x : var_i, get_var s2'.(evm) x) f.(f_res) = ok res →
    all2 check_ty_val f.(f_tyout) res →
    valid_RSP s2'.(emem) s2'.(evm) →
    let m2 := free_stack s2'.(emem) in
    s2 = {| emem := m2 ; evm := set_RSP m2 s2'.(evm) |} →
    let vm := Sv.union (ra_vm f.(f_extra) var_tmp) (saved_stack_vm f) in
    sem_call ii (Sv.union k vm) s1 fn s2.

Variant sem_export_call_conclusion (m: mem) (fd: sfundef) (args: values) (vm: vmap) (m': mem) (res: values) : Prop :=
  | SemExportCallConclusion (m1: mem) (k: Sv.t) (m2: mem) (vm2: vmap) (res': values) of
    saved_stack_valid fd k &
    Sv.Subset (Sv.inter callee_saved (Sv.union k (Sv.union (ra_vm fd.(f_extra) var_tmp) (saved_stack_vm fd)))) (sv_of_list fst fd.(f_extra).(sf_to_save)) &
    alloc_stack m fd.(f_extra).(sf_align) fd.(f_extra).(sf_stk_sz) fd.(f_extra).(sf_stk_extra_sz) = ok m1 &
    all2 check_ty_val fd.(f_tyin) args &
    sem k {| emem := m1 ; evm := set_RSP m1 (ra_undef_vm_none fd.(f_extra).(sf_save_stack) var_tmp vm) |} fd.(f_body) {| emem := m2 ; evm := vm2 |} &
    mapM (λ x : var_i, get_var vm2 x) fd.(f_res) = ok res' &
    List.Forall2 value_uincl res res' &
    all2 check_ty_val fd.(f_tyout) res' &
    valid_RSP m2 vm2 &
    m' = free_stack m2.

Variant sem_export_call (gd: @extra_val_t _ progStack) (m: mem) (fn: funname) (args: values) (m': mem) (res: values) : Prop :=
  | SemExportCall (fd: sfundef) of
                  get_fundef p.(p_funcs) fn = Some fd &
      fd.(f_extra).(sf_return_address) == RAnone &
      disjoint (sv_of_list fst fd.(f_extra).(sf_to_save)) (sv_of_list v_var fd.(f_res)) &
      ~~ Sv.mem vrsp (sv_of_list v_var fd.(f_res)) &
    ∀ vm args',
      wf_vm vm →
      mapM (λ x : var_i, get_var vm x) fd.(f_params) = ok args' →
      List.Forall2 value_uincl args args' →
      valid_RSP m vm →
      vm.[vgd] = ok (pword_of_word gd) →
      sem_export_call_conclusion m fd args' vm m' res.

(*---------------------------------------------------*)
Variant ex3_3 (A B C : Type) (P1 P2 P3: A → B → C → Prop) : Prop :=
  Ex3_3 a b c of P1 a b c & P2 a b c & P3 a b c.

Variant ex6_14 (A B C D E F : Type) (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 : A → B → C → D → E → F → Prop) : Prop :=
| Ex6_14 a b c d e f of P1 a b c d e f & P2 a b c d e f & P3 a b c d e f & P4 a b c d e f & P5 a b c d e f & P6 a b c d e f & P7 a b c d e f & P8 a b c d e f & P9 a b c d e f & P10 a b c d e f & P11 a b c d e f & P12 a b c d e f & P13 a b c d e f & P14 a b c d e f.

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
  ∃ k',
  [/\
  efr_valid ii r,
  sem_i ii k' (kill_extra_register ii s) r s',
  disjoint k' magic_variables &
  k = Sv.union (extra_free_registers_at ii) k' ].
Proof. by case => {k s i s'} ii k i s1 s2 ???; exists k. Qed.

Lemma sem_iE ii k s i s' :
  sem_i ii k s i s' →
  match i with
  | Cassgn x tag ty e =>
    k = vrv x ∧
    exists2 v', sem_pexpr gd s e >>= truncate_val ty = ok v' & write_lval gd x v' s = ok s'
  | Copn xs t o es => k = vrvs xs ∧ sem_sopn gd o s xs es = ok s'
  | Cif e c1 c2 =>
    exists2 b, sem_pexpr gd s e = ok (Vbool b) & sem k s (if b then c1 else c2) s'
  | Cwhile a c e c' =>
    ∃ kc si b,
       [/\ sem kc s c si, sem_pexpr gd si e = ok (Vbool b) &
                       if b then ex3_3 (λ k' krec _, k = Sv.union (Sv.union kc k') krec) (λ k' _ sj, sem k' si c' sj) (λ _ krec sj, sem_I krec sj (MkI ii (Cwhile a c e c')) s') else si = s' ∧ kc = k ]
  | Ccall ini res f args =>
    exists2 xargs,
    mapM get_pvar args = ok xargs &
    exists2 xres,
    mapM get_lvar res = ok xres &
    sem_call ii k s f s'
  | Cfor _ _ _ => false
  end.
Proof.
  case => { ii k s i s' }; eauto.
  - move => _ s s' x _ ty e v v' -> /= ->; eauto.
  - move => ii k k' krec s1 s2 s3 s4 a c e c' exec_c eval_e exec_c' rec; exists k, s2, true; split; try eexists; eauto.
  by move => ii k s1 s2 a c e c' exec_c eval_e; exists k, s2, false.
Qed.

Lemma sem_callE ii k s fn s' :
  sem_call ii k s fn s' →
  ex6_14
    (λ f _ _ _ _ _, get_fundef (p_funcs p) fn = Some f)
    (λ f _ _ k' _ _, ra_valid f ii k' var_tmp)
    (λ f _ _ k' _ _, saved_stack_valid f k')
    (λ f _ _ _ _ _, top_stack_aligned f s)
    (λ _ _ _ _ _ _, valid_RSP s.(emem) s.(evm))
    (λ f m1 _ _ _ _, alloc_stack s.(emem) f.(f_extra).(sf_align) f.(f_extra).(sf_stk_sz) f.(f_extra).(sf_stk_extra_sz) = ok m1)
    (λ f _ _ _ args _, mapM (λ x : var_i, get_var s.(evm) x) f.(f_params) = ok args)
    (λ f _ _ _ args _, all2 check_ty_val f.(f_tyin) args)
    (λ f m1 s2' k' _ _,
     let vm := ra_undef_vm f s.(evm) var_tmp in
     sem k' {| emem := m1 ; evm := set_RSP m1 vm; |} f.(f_body) s2')
    (λ f _ s2' _ _ res, mapM (λ x : var_i, get_var s2'.(evm) x) f.(f_res) = ok res)
    (λ f _ _ _ _ res, all2 check_ty_val f.(f_tyout) res)
    (λ _ _ s2' _ _ _, valid_RSP s2'.(emem) s2'.(evm))
    (λ f _ s2' _ _ _,
      let m2 := free_stack s2'.(emem) in
      s' = {| emem := m2 ; evm := set_RSP m2 s2'.(evm) |})
    (λ f _ _ k' _ _,
     k = Sv.union k' (Sv.union (ra_vm f.(f_extra) var_tmp) (saved_stack_vm f))).
Proof.
  case => { ii k s fn s' } /= ii k s s' fn f args m1 s2' res => ok_f ok_ra ok_ss ok_sp ok_RSP ok_alloc ok_args wt_args exec_body ok_RSP' ok_res wt_res /= ->.
  by exists f m1 s2' k args res.
Qed.

(*---------------------------------------------------*)
Lemma sv_of_flagsE x l : Sv.mem x (sv_of_flags l) = (x \in map (fun r => to_var r) l).
Proof. exact: sv_of_listE. Qed.

Lemma sv_of_flagsP x l : reflect (Sv.In x (sv_of_flags l)) (x \in map (fun r => to_var r) l).
Proof. exact: sv_of_listP. Qed.

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
      efr_valid ii i →
      sem_i ii k (kill_extra_register ii s1) i s2 →
      Pi_r ii k (kill_extra_register ii s1) i s2 →
      disjoint k magic_variables →
      Pi (Sv.union (extra_free_registers_at ii) k) s1 (MkI ii i) s2.

  Hypothesis HmkI : sem_Ind_mkI.

  Definition sem_Ind_assgn : Prop :=
    ∀ (ii: instr_info) (s1 s2 : estate) (x : lval) (tag : assgn_tag) ty (e : pexpr) v v',
      sem_pexpr gd s1 e = ok v →
      truncate_val ty v = ok v' →
      write_lval gd x v' s1 = ok s2 →
      Pi_r ii (vrv x) s1 (Cassgn x tag ty e) s2.

  Definition sem_Ind_opn : Prop :=
    ∀ (ii: instr_info) (s1 s2 : estate) t (o : sopn) (xs : lvals) (es : pexprs),
      sem_sopn gd o s1 xs es = ok s2 →
      Pi_r ii (vrvs xs) s1 (Copn xs t o es) s2.

  Definition sem_Ind_if_true : Prop :=
    ∀ (ii: instr_info) (k: Sv.t) (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    sem_pexpr gd s1 e = ok (Vbool true) →
    sem k s1 c1 s2 → Pc k s1 c1 s2 → Pi_r ii k s1 (Cif e c1 c2) s2.

  Definition sem_Ind_if_false : Prop :=
    ∀ (ii: instr_info) (k: Sv.t) (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    sem_pexpr gd s1 e = ok (Vbool false) →
    sem k s1 c2 s2 → Pc k s1 c2 s2 → Pi_r ii k s1 (Cif e c1 c2) s2.

  Definition sem_Ind_while_true : Prop :=
    ∀ (ii: instr_info) (k k' krec: Sv.t) (s1 s2 s3 s4 : estate) a (c : cmd) (e : pexpr) (c' : cmd),
    sem k s1 c s2 → Pc k s1 c s2 →
    sem_pexpr gd s2 e = ok (Vbool true) →
    sem k' s2 c' s3 → Pc k' s2 c' s3 →
    sem_I krec s3 (MkI ii (Cwhile a c e c')) s4 →
    Pi krec s3 (MkI ii (Cwhile a c e c')) s4 →
    Pi_r ii (Sv.union (Sv.union k k') krec) s1 (Cwhile a c e c') s4.

  Definition sem_Ind_while_false : Prop :=
    ∀ (ii: instr_info) (k: Sv.t) (s1 s2 : estate) a (c : cmd) (e : pexpr) (c' : cmd),
    sem k s1 c s2 →
    Pc k s1 c s2 →
    sem_pexpr gd s2 e = ok (Vbool false) →
    Pi_r ii k s1 (Cwhile a c e c') s2.

  Hypotheses
    (Hasgn: sem_Ind_assgn)
    (Hopn: sem_Ind_opn)
    (Hif_true: sem_Ind_if_true)
    (Hif_false: sem_Ind_if_false)
    (Hwhile_true: sem_Ind_while_true)
    (Hwhile_false: sem_Ind_while_false)
  .

  Definition sem_Ind_call : Prop :=
    ∀ (ii: instr_info) (k: Sv.t) (s1 s2: estate) ini res fn args xargs xres,
      mapM get_pvar args = ok xargs →
      mapM get_lvar res = ok xres →
      sem_call ii k s1 fn s2 →
      Pfun ii k s1 fn s2 →
      Pi_r ii k s1 (Ccall ini res fn args) s2.

  Definition sem_Ind_proc : Prop :=
    ∀ (ii: instr_info) (k: Sv.t) (s1 s2: estate) (fn: funname) fd args m1 s2' res,
      get_fundef (p_funcs p) fn = Some fd →
      ra_valid fd ii k var_tmp →
      saved_stack_valid fd k →
      top_stack_aligned fd s1 →
      valid_RSP s1.(emem) s1.(evm) →
      alloc_stack s1.(emem) fd.(f_extra).(sf_align) fd.(f_extra).(sf_stk_sz) fd.(f_extra).(sf_stk_extra_sz) = ok m1 →
      mapM (λ x : var_i, get_var s1.(evm) x) fd.(f_params) = ok args →
      all2 check_ty_val fd.(f_tyin) args →
      let vm1 := ra_undef_vm fd s1.(evm) var_tmp in
      sem k {| emem := m1; evm := set_RSP m1 vm1; |} fd.(f_body) s2' →
      Pc  k {| emem := m1; evm := set_RSP m1 vm1; |} fd.(f_body) s2' →
      mapM (λ x : var_i, get_var s2'.(evm) x) fd.(f_res) = ok res →
      all2 check_ty_val fd.(f_tyout) res →
      valid_RSP s2'.(emem) s2'.(evm) →
      let m2 := free_stack s2'.(emem) in
      s2 = {| emem := m2 ; evm := set_RSP m2 s2'.(evm) |} →
      let vm := Sv.union k (Sv.union (ra_vm fd.(f_extra) var_tmp) (saved_stack_vm fd)) in
      Pfun ii vm s1 fn s2.

  Hypotheses
    (Hcall: sem_Ind_call)
    (Hproc: sem_Ind_proc)
  .

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
    | @Eif_true ii k s1 s2 e1 c1 c2 e2 s0 =>
      @Hif_true ii k s1 s2 e1 c1 c2 e2 s0 (@sem_Ind k s1 c1 s2 s0)
    | @Eif_false ii k s1 s2 e1 c1 c2 e2 s0 =>
      @Hif_false ii k s1 s2 e1 c1 c2 e2 s0 (@sem_Ind k s1 c2 s2 s0)
    | @Ewhile_true ii k k' krec s1 s2 s3 s4 a c e1 c' s0 e2 s5 s6 =>
      @Hwhile_true ii k k' krec s1 s2 s3 s4 a c e1 c' s0 (@sem_Ind k s1 c s2 s0) e2 s5 (@sem_Ind k' s2 c' s3 s5) s6
          (@sem_I_Ind krec s3 (MkI ii (Cwhile a c e1 c')) s4 s6)
    | @Ewhile_false ii k s1 s2 a c e1 c' s0 e2 =>
      @Hwhile_false ii k s1 s2 a c e1 c' s0 (@sem_Ind k s1 c s2 s0) e2
    | @Ecall ii k s1 s2 ini res fn args xargs xres hargs hres exec =>
      @Hcall ii k s1 s2 ini res fn args xargs xres hargs hres exec (@sem_call_Ind ii k s1 fn s2 exec)
    end

  with sem_I_Ind (k: Sv.t) (s1 : estate) (i : instr) (s2 : estate) (s : sem_I k s1 i s2) {struct s} : Pi k s1 i s2 :=
    match s in sem_I k e1 i0 e2 return Pi k e1 i0 e2 with
    | @EmkI ii k i s1 s2 nom exec pm => @HmkI ii k i s1 s2 nom exec (@sem_i_Ind ii k _ i s2 exec) pm
    end

  with sem_call_Ind (ii: instr_info) (k: Sv.t) (s1: estate) (fn: funname) (s2: estate) (s: sem_call ii k s1 fn s2) {struct s} : Pfun ii k s1 fn s2 :=
    match s with
    | @EcallRun ii k s1 s2 fn fd args m1 s2' res ok_fd ok_ra ok_ss ok_sp ok_rsp ok_args wt_args ok_m1 exec ok_res wt_res ok_rsp' ok_s2 =>
      @Hproc ii k s1 s2 fn fd args m1 s2' res ok_fd ok_ra ok_ss ok_sp ok_rsp ok_args wt_args ok_m1 exec (@sem_Ind k _ _ _ exec) ok_res wt_res ok_rsp' ok_s2
    end.

End SEM_IND.

End SEM.

End ASM_EXTRA.
