(*
*)
Require Import psem.
Import Utf8.
Import all_ssreflect.
Import var.
Import low_memory.
Import x86_variables.

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
 - The RSP local variable always hold the pointer to the top of the stack
 - The sp_rip local variable is assumed to hold the pointer to the static global data
 *)

Definition get_pvar (e: pexpr) : exec var :=
  if e is Pvar {| gv := x ; gs := Slocal |} then ok (v_var x) else type_error.

Definition get_lvar (x: lval) : exec var :=
  if x is Lvar x then ok (v_var x) else type_error.

Definition kill_flag (vm: vmap) (r: rflag) : vmap :=
  let: x := var_of_flag r in
  if vm.[x] is Ok _ then vm.[var_of_flag r <- undef_error] else vm.

Notation kill_flags := (foldl kill_flag).

Lemma kill_flagsE vm fs x :
  ((kill_flags vm fs).[x] = if x \in map var_of_flag fs then if vm.[x] is Ok _ then undef_error else vm.[x] else vm.[x])%vmap.
Proof.
  elim: fs vm => // f fs ih vm /=.
  rewrite ih {ih} inE /kill_flag; case: eqP.
  - move => -> /=; case: ifP => _; case h: vm.[_].
    1, 3: by rewrite Fv.setP_eq.
    1, 2: by rewrite h.
  move => /= x_neq_f; case: ifP => // _; case h: vm.[_] => //.
  all: rewrite Fv.setP_neq //; apply/eqP.
  all: exact: not_eq_sym.
Qed.

Lemma kill_flags_uincl vm fs :
  vm_uincl (kill_flags vm fs) vm.
Proof.
  move => x; rewrite kill_flagsE.
  case: ifP => // _.
  by case: vm.[x].
Qed.

Section SEM.

Context (p: sprog) (extra_free_registers: instr_info → option var).

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
Let vrsp : var := vid (string_of_register RSP).

Definition magic_variables : Sv.t :=
  Sv.add vgd (Sv.singleton vrsp).

Definition extra_free_registers_at ii : Sv.t :=
  if extra_free_registers ii is Some r then Sv.singleton r else Sv.empty.

Definition sv_of_flags : seq rflag → Sv.t :=
  foldl (λ s r, Sv.add (var_of_flag r) s) Sv.empty.

Definition set_RSP m vm : vmap :=
  vm.[vrsp <- ok (pword_of_word (top_stack m))].

Definition valid_RSP m (vm: vmap) : Prop :=
  vm.[vrsp] = ok (pword_of_word (top_stack m)).

Inductive sem : Sv.t → estate → cmd → estate → Prop :=
| Eskip s :
    sem Sv.empty s [::] s

| Eseq ki kc s1 s2 s3 i c :
    sem_I ki s1 i s2 →
    sem kc s2 c s3 →
    sem (Sv.union ki kc) s1 (i :: c) s3

with sem_I : Sv.t → estate → instr → estate → Prop :=
| EmkI ii k i s1 s2:
    (if extra_free_registers ii is Some r then [&& r != vgd, r != vrsp & vtype r == sword Uptr] else true) →
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
    sem_i ii krec s3 (Cwhile a c e c') s4 →
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
| EcallRun ii k s1 s2 fn f m1 s2' :
    get_fundef (p_funcs p) fn = Some f →
    match f.(f_extra).(sf_return_address) with
    | RAstack _ => extra_free_registers ii != None
    | RAreg ra => (ra != vid p.(p_extra).(sp_rip)) && (ra != var_of_register RSP) && (~~ Sv.mem ra k)
    | RAnone => true
    end →
    match f.(f_extra).(sf_save_stack) with
    | SavedStackReg r => (r != vid p.(p_extra).(sp_rip)) && (r != var_of_register RSP) && (~~ Sv.mem r k)
    | _ => true
    end →
    (f.(f_extra).(sf_return_address) == RAnone) || is_align (top_stack s1.(emem)) f.(f_extra).(sf_align) →
    valid_RSP s1.(emem) s1.(evm) →
    alloc_stack s1.(emem) f.(f_extra).(sf_align) f.(f_extra).(sf_stk_sz) f.(f_extra).(sf_stk_extra_sz) = ok m1 →
    sem k {| emem := m1 ; evm := set_RSP m1 match f.(f_extra).(sf_return_address) with RAreg x => s1.(evm).[x <- undef_error] | RAstack _ => s1.(evm) | RAnone => kill_flags (if f.(f_extra).(sf_save_stack) is SavedStackReg r then s1.(evm).[r <- undef_error] else s1.(evm)) rflags end |} f.(f_body) s2' →
    valid_RSP s2'.(emem) s2'.(evm) →
    let m2 := free_stack s2'.(emem) in
    s2 = {| emem := m2 ; evm := set_RSP m2 s2'.(evm) |}  →
    sem_call ii (Sv.union k (Sv.union
                               match f.(f_extra).(sf_return_address) with
                               | RAreg ra => Sv.singleton ra
                               | RAstack _ => Sv.empty
                               | RAnone => sv_of_flags rflags
                               end
                               (if f.(f_extra).(sf_save_stack) is SavedStackReg r then Sv.singleton r else Sv.empty))) s1 fn s2.

(*---------------------------------------------------*)
Variant ex3_3 (A B C : Type) (P1 P2 P3: A → B → C → Prop) : Prop :=
  Ex3_3 a b c of P1 a b c & P2 a b c & P3 a b c.

Variant ex4_10 (A B C D : Type) (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 : A → B → C → D → Prop) : Prop :=
| Ex3_8 a b c d of P1 a b c d & P2 a b c d & P3 a b c d & P4 a b c d & P5 a b c d & P6 a b c d & P7 a b c d & P8 a b c d & P9 a b c d & P10 a b c d.

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
  ((if extra_free_registers ii is Some r then [&& r != vgd, r != vrsp & vtype r == sword Uptr] else true) : bool),
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
                       if b then ex3_3 (λ k' krec _, k = Sv.union (Sv.union kc k') krec) (λ k' _ sj, sem k' si c' sj) (λ _ krec sj, sem_i ii krec sj (Cwhile a c e c') s') else si = s' ∧ kc = k ]
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
  ex4_10
    (λ f _ _ _, get_fundef (p_funcs p) fn = Some f)
    (λ f _ _ k', match f.(f_extra).(sf_return_address) with
              | RAstack _ => extra_free_registers ii != None
              | RAreg ra => (ra != vid p.(p_extra).(sp_rip)) && (ra != var_of_register RSP) && (~~ Sv.mem ra k')
              | RAnone => true
              end : bool)
    (λ f _ _ k', match f.(f_extra).(sf_save_stack) with
                | SavedStackReg r => (r != vid p.(p_extra).(sp_rip)) && (r != var_of_register RSP) && (~~ Sv.mem r k')
                | _ => true
                end : bool)
    (λ f _ _ _, (f.(f_extra).(sf_return_address) == RAnone) || is_align (top_stack s.(emem)) f.(f_extra).(sf_align))
    (λ _ _ _ _, valid_RSP s.(emem) s.(evm))
    (λ f m1 _ _, alloc_stack s.(emem) f.(f_extra).(sf_align) f.(f_extra).(sf_stk_sz) f.(f_extra).(sf_stk_extra_sz) = ok m1)
    (λ f m1 s2' k', sem k' {| emem := m1 ; evm := set_RSP m1 match f.(f_extra).(sf_return_address) with RAreg x => s.(evm).[x <- undef_error] | RAstack _ => s.(evm) | RAnone => kill_flags (if f.(f_extra).(sf_save_stack) is SavedStackReg r then s.(evm).[r <- undef_error] else s.(evm)) rflags end |} f.(f_body) s2')
    (λ _ _ s2' _, valid_RSP s2'.(emem) s2'.(evm))
    (λ f _ s2' _,
      let m2 := free_stack s2'.(emem) in
      s' = {| emem := m2 ; evm := set_RSP m2 s2'.(evm) |})
    (λ f _ _ k', k = Sv.union k' (Sv.union match f.(f_extra).(sf_return_address) with RAreg ra => Sv.singleton ra | RAstack _ => Sv.empty | RAnone => sv_of_flags rflags end (if f.(f_extra).(sf_save_stack) is SavedStackReg r then Sv.singleton r else Sv.empty))).
Proof.
  case => { ii k s fn s' } ii k s s' fn f m1 s2' => ok_f ok_ra ok_ss ok_sp ok_RSP ok_alloc exec_body ok_RSP' /= ->.
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
      (if extra_free_registers ii is Some r then [&& r != vgd, r != vrsp & vtype r == sword Uptr] else true) →
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
    sem_i ii krec s3 (Cwhile a c e c') s4 → Pi_r ii krec s3 (Cwhile a c e c') s4 → Pi_r ii (Sv.union (Sv.union k k') krec) s1 (Cwhile a c e c') s4.

  Definition sem_Ind_while_false : Prop :=
    ∀ (ii: instr_info) (k: Sv.t) (s1 s2 : estate) a (c : cmd) (e : pexpr) (c' : cmd),
    sem k s1 c s2 -> Pc k s1 c s2 →
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
    ∀ (ii: instr_info) (k: Sv.t) (s1 s2: estate) (fn: funname) fd m1 s2',
      get_fundef (p_funcs p) fn = Some fd →
      match fd.(f_extra).(sf_return_address) with
      | RAstack _ => extra_free_registers ii != None
      | RAreg ra => (ra != vid p.(p_extra).(sp_rip)) && (ra != var_of_register RSP) && (~~ Sv.mem ra k)
      | RAnone => true
      end →
      match fd.(f_extra).(sf_save_stack) with
      | SavedStackReg r => (r != vid p.(p_extra).(sp_rip)) && (r != var_of_register RSP) && (~~ Sv.mem r k)
      | _ => true
      end →
      (fd.(f_extra).(sf_return_address) == RAnone) || is_align (top_stack s1.(emem)) fd.(f_extra).(sf_align) →
      valid_RSP s1.(emem) s1.(evm) →
      alloc_stack s1.(emem) fd.(f_extra).(sf_align) fd.(f_extra).(sf_stk_sz) fd.(f_extra).(sf_stk_extra_sz) = ok m1 →
      sem k {| emem := m1 ; evm := set_RSP m1 match fd.(f_extra).(sf_return_address) with RAreg x => s1.(evm).[x <- undef_error] | RAstack _ => s1.(evm) | RAnone => kill_flags (if fd.(f_extra).(sf_save_stack) is SavedStackReg r then s1.(evm).[r <- undef_error] else s1.(evm)) rflags end |} fd.(f_body) s2' →
      Pc k {| emem := m1 ; evm := set_RSP m1 match fd.(f_extra).(sf_return_address) with RAreg x => s1.(evm).[x <- undef_error] | RAstack _ => s1.(evm) | RAnone => kill_flags (if fd.(f_extra).(sf_save_stack) is SavedStackReg r then s1.(evm).[r <- undef_error] else s1.(evm)) rflags end |} fd.(f_body) s2' →
      valid_RSP s2'.(emem) s2'.(evm) →
      let m2 := free_stack s2'.(emem) in
      s2 = {| emem := m2 ; evm := set_RSP m2 s2'.(evm) |}  →
      Pfun ii (Sv.union k (Sv.union match fd.(f_extra).(sf_return_address) with RAreg ra => Sv.singleton ra | RAstack _ => Sv.empty | RAnone => sv_of_flags rflags end (if fd.(f_extra).(sf_save_stack) is SavedStackReg r then Sv.singleton r else Sv.empty))) s1 fn s2.

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
          (@sem_i_Ind ii krec s3 (Cwhile a c e1 c') s4 s6)
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
    | @EcallRun ii k s1 s2 fn fd m1 s2' ok_fd ok_ra ok_ss ok_sp ok_rsp ok_m1 exec ok_rsp' ok_s2 =>
      @Hproc ii k s1 s2 fn fd m1 s2' ok_fd ok_ra ok_ss ok_sp ok_rsp ok_m1 exec (@sem_Ind k _ _ _ exec) ok_rsp' ok_s2
    end.

End SEM_IND.

End SEM.

Arguments set_RSP _ _%vmap_scope.
