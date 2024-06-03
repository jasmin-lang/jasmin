(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
Require Import xseq.
Require Export array type expr gen_map warray_ sem_type sem_op_typed values varmap expr_facts low_memory syscall_sem psem_defs.
Require Export
  flag_combination
  sem_params.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.
Local Open Scope seq_scope.
Open Scope vm_scope.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Lemma sem_sop1I y x f:
  sem_sop1 f x = ok y →
  exists2 w : sem_t (type_of_op1 f).1,
    of_val _ x = ok w &
    y = to_val (sem_sop1_typed f w).
Proof. by rewrite /sem_sop1; t_xrbindP => w ok_w <-; eauto. Qed.

Lemma sem_sop2I v v1 v2 f:
  sem_sop2 f v1 v2 = ok v →
  ∃ (w1 : sem_t (type_of_op2 f).1.1) (w2 : sem_t (type_of_op2 f).1.2)
    (w3: sem_t (type_of_op2 f).2),
    [/\ of_val _ v1 = ok w1,
        of_val _ v2 = ok w2,
        sem_sop2_typed f w1 w2 = ok w3 &
        v = to_val w3].
Proof.
  by rewrite /sem_sop2; t_xrbindP => w1 ok_w1 w2 ok_w2 w3 ok_w3 <- {v}; exists w1, w2, w3.
Qed.

(* ** Global access
 * -------------------------------------------------------------------- *)

Lemma get_globalI gd g v :
  get_global gd g = ok v →
  exists gv : glob_value, [/\ get_global_value gd g = Some gv, v = gv2val gv & type_of_val v = vtype g].
Proof.
  rewrite /get_global; case: get_global_value => // gv.
  by case:eqP => // <- [<-];exists gv.
Qed.

Section WSW.
Context {wsw:WithSubWord}.

(* ** State
 * ------------------------------------------------------------------------- *)

Section ESTATE_UTILS.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}.

Lemma surj_estate s : s = {| escs := escs s; emem := emem s; evm := evm s |}.
Proof. by case:s. Qed.

Lemma with_vm_same s : with_vm s (evm s) = s.
Proof. by case: s. Qed.

Lemma with_vm_idem s vm1 vm2 : with_vm (with_vm s vm1) vm2 = with_vm s vm2.
Proof. by case: s. Qed.

Lemma with_mem_same s : with_mem s (emem s) = s.
Proof. by case: s. Qed.

Lemma with_mem_idem s m1 m2 : with_mem (with_mem s m1) m2 = with_mem s m2.
Proof. by case: s. Qed.

Lemma with_scs_same s : with_scs s (escs s) = s.
Proof. by case: s. Qed.

Lemma with_scs_idem s scs1 scs2 : with_scs (with_scs s scs1) scs2 = with_scs s scs2.
Proof. by case: s. Qed.

Lemma evm_with_vm s vm : evm (with_vm s vm) = vm.
Proof. by case: s. Qed.

Lemma emem_with_vm s vm : emem (with_vm s vm) = emem s.
Proof. by case: s. Qed.

Lemma escs_with_vm s vm : escs (with_vm s vm) = escs s.
Proof. by case: s. Qed.

End ESTATE_UTILS.

(* ** Instructions
 * -------------------------------------------------------------------- *)

Class semCallParams
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {scs : syscall_sem syscall_state}
  {pT : progT}
  := SemCallParams
  {
  init_state : extra_fun_t -> extra_prog_t -> extra_val_t -> estate -> exec estate;
  finalize   : extra_fun_t -> mem -> mem;
  exec_syscall : syscall_state_t -> mem -> syscall_t -> values -> exec (syscall_state_t * mem * values);
  exec_syscallP: forall scs m o vargs vargs' rscs rm vres,
     exec_syscall scs m o vargs = ok (rscs, rm, vres) ->
     List.Forall2 value_uincl vargs vargs' ->
     exists2 vres', exec_syscall scs m o vargs' = ok (rscs, rm, vres') & List.Forall2 value_uincl vres vres';
  exec_syscallS: forall scs m o vargs rscs rm vres,
     exec_syscall scs m o vargs = ok (rscs, rm, vres) ->
     mem_equiv m rm;
}.

(** Switch for the semantics of function calls:
  - when false, arguments and returned values are truncated to the declared type of the called function;
  - when true, arguments and returned values are allowed to be undefined.

Informally, “direct call” means that passing arguments and returned value does not go through an assignment;
indeed, assignments truncate and fail on undefined values.
*)
Class DirectCall := {
  direct_call : bool;
}.

Definition indirect_c : DirectCall := {| direct_call := false |}.
Definition direct_c : DirectCall := {| direct_call := true |}.

Section SEM.

Context
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {scP : semCallParams}
  (P : prog)
  (ev : extra_val_t).

Notation gd := (p_globs P).

Definition get_lvar_i (x: lval) : exec var_i :=
  if x is Lvar x then ok x else type_error.

Definition dc_truncate_val t v :=
  if direct_call then ok v
  else truncate_val t v.

Inductive sem : estate -> cmd -> estate -> Prop :=
| Eskip s :
    sem s [::] s

| Eseq s1 s2 s3 i c :
    sem_I s1 i s2 -> sem s2 c s3 -> sem s1 (i::c) s3

with sem_I : estate -> instr -> estate -> Prop :=
| EmkI ii i s1 s2:
    sem_i s1 i s2 ->
    sem_I s1 (MkI ii i) s2

with sem_i : estate -> instr_r -> estate -> Prop :=
| Eassgn s1 s2 (x:lval) tag ty e v v' :
    sem_pexpr true gd s1 e = ok v ->
    truncate_val ty v = ok v' →
    write_lval true gd x v' s1 = ok s2 ->
    sem_i s1 (Cassgn x tag ty e) s2

| Eopn s1 s2 t o xs es:
    sem_sopn gd o s1 xs es = ok s2 ->
    sem_i s1 (Copn xs t o es) s2

| Esyscall s1 scs m s2 o xs es ves vs:
    sem_pexprs true gd s1 es = ok ves →
    exec_syscall s1.(escs) s1.(emem) o ves = ok (scs, m, vs) →
    write_lvals true gd (with_scs (with_mem s1 m) scs) xs vs = ok s2 →
    sem_i s1 (Csyscall xs o es) s2

| Eif_true s1 s2 e c1 c2 :
    sem_pexpr true gd s1 e = ok (Vbool true) ->
    sem s1 c1 s2 ->
    sem_i s1 (Cif e c1 c2) s2

| Eif_false s1 s2 e c1 c2 :
    sem_pexpr true gd s1 e = ok (Vbool false) ->
    sem s1 c2 s2 ->
    sem_i s1 (Cif e c1 c2) s2

| Ewhile_true s1 s2 s3 s4 a c e c' :
    sem s1 c s2 ->
    sem_pexpr true gd s2 e = ok (Vbool true) ->
    sem s2 c' s3 ->
    sem_i s3 (Cwhile a c e c') s4 ->
    sem_i s1 (Cwhile a c e c') s4

| Ewhile_false s1 s2 a c e c' :
    sem s1 c s2 ->
    sem_pexpr true gd s2 e = ok (Vbool false) ->
    sem_i s1 (Cwhile a c e c') s2

| Efor s1 s2 (i:var_i) d lo hi c vlo vhi :
    sem_pexpr true gd s1 lo = ok (Vint vlo) ->
    sem_pexpr true gd s1 hi = ok (Vint vhi) ->
    sem_for i (wrange d vlo vhi) s1 c s2 ->
    sem_i s1 (Cfor i (d, lo, hi) c) s2

| Ecall s1 scs2 m2 s2 xs f args vargs vs :
    sem_pexprs (~~direct_call) gd s1 args = ok vargs ->
    sem_call s1.(escs) s1.(emem) f vargs scs2 m2 vs ->
    write_lvals (~~direct_call) gd (with_scs (with_mem s1 m2) scs2) xs vs = ok s2 ->
    sem_i s1 (Ccall xs f args) s2

with sem_for : var_i -> seq Z -> estate -> cmd -> estate -> Prop :=
| EForDone s i c :
    sem_for i [::] s c s

| EForOne s1 s1' s2 s3 i w ws c :
    write_var true i (Vint w) s1 = ok s1' ->
    sem s1' c s2 ->
    sem_for i ws s2 c s3 ->
    sem_for i (w :: ws) s1 c s3

with sem_call : syscall_state_t -> mem -> funname -> seq value -> syscall_state_t -> mem -> seq value -> Prop :=
| EcallRun scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' :
    get_fundef (p_funcs P) fn = Some f ->
    mapM2 ErrType dc_truncate_val f.(f_tyin) vargs' = ok vargs ->
    init_state f.(f_extra) (p_extra P) ev (Estate scs1 m1 Vm.init) = ok s0 ->
    write_vars (~~direct_call) f.(f_params) vargs s0 = ok s1 ->
    sem s1 f.(f_body) s2 ->
    get_var_is (~~ direct_call) s2.(evm) f.(f_res) = ok vres ->
    mapM2 ErrType dc_truncate_val f.(f_tyout) vres = ok vres' ->
    scs2 = s2.(escs) ->
    m2 = finalize f.(f_extra) s2.(emem)  ->
    sem_call scs1 m1 fn vargs' scs2 m2 vres'.

Section SEM_IND.
  Variables
    (Pc   : estate -> cmd -> estate -> Prop)
    (Pi_r : estate -> instr_r -> estate -> Prop)
    (Pi   : estate -> instr -> estate -> Prop)
    (Pfor : var_i -> seq Z -> estate -> cmd -> estate -> Prop)
    (Pfun : syscall_state_t -> mem -> funname -> seq value -> syscall_state_t -> mem -> seq value -> Prop).

  Definition sem_Ind_nil : Prop :=
    forall s : estate, Pc s [::] s.

  Definition sem_Ind_cons : Prop :=
    forall (s1 s2 s3 : estate) (i : instr) (c : cmd),
      sem_I s1 i s2 -> Pi s1 i s2 -> sem s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.

  Hypotheses
    (Hnil: sem_Ind_nil)
    (Hcons: sem_Ind_cons)
  .

  Definition sem_Ind_mkI : Prop :=
    forall (ii : instr_info) (i : instr_r) (s1 s2 : estate),
      sem_i s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.

  Hypothesis HmkI : sem_Ind_mkI.

  Definition sem_Ind_assgn : Prop :=
    forall (s1 s2 : estate) (x : lval) (tag : assgn_tag) ty (e : pexpr) v v',
      sem_pexpr true gd s1 e = ok v →
      truncate_val ty v = ok v' →
      write_lval true gd x v' s1 = ok s2 →
      Pi_r s1 (Cassgn x tag ty e) s2.

  Definition sem_Ind_opn : Prop :=
    forall (s1 s2 : estate) t (o : sopn) (xs : lvals) (es : pexprs),
      sem_sopn gd o s1 xs es = ok s2 →
      Pi_r s1 (Copn xs t o es) s2.

  Definition sem_Ind_syscall : Prop :=
    forall  s1 scs m s2 o xs es ves vs,
      sem_pexprs true gd s1 es = ok ves →
      exec_syscall s1.(escs) s1.(emem) o ves = ok (scs, m, vs) →
      write_lvals true gd (with_scs (with_mem s1 m) scs) xs vs = ok s2 →
      Pi_r s1 (Csyscall xs o es) s2.

  Definition sem_Ind_if_true : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    sem_pexpr true gd s1 e = ok (Vbool true) ->
    sem s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.

  Definition sem_Ind_if_false : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    sem_pexpr true gd s1 e = ok (Vbool false) ->
    sem s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.

  Definition sem_Ind_while_true : Prop :=
    forall (s1 s2 s3 s4 : estate) a (c : cmd) (e : pexpr) (c' : cmd),
    sem s1 c s2 -> Pc s1 c s2 ->
    sem_pexpr true gd s2 e = ok (Vbool true) ->
    sem s2 c' s3 -> Pc s2 c' s3 ->
    sem_i s3 (Cwhile a c e c') s4 -> Pi_r s3 (Cwhile a c e c') s4 -> Pi_r s1 (Cwhile a c e c') s4.

  Definition sem_Ind_while_false : Prop :=
    forall (s1 s2 : estate) a (c : cmd) (e : pexpr) (c' : cmd),
    sem s1 c s2 -> Pc s1 c s2 ->
    sem_pexpr true gd s2 e = ok (Vbool false) ->
    Pi_r s1 (Cwhile a c e c') s2.

  Hypotheses
    (Hasgn: sem_Ind_assgn)
    (Hopn: sem_Ind_opn)
    (Hsyscall: sem_Ind_syscall)
    (Hif_true: sem_Ind_if_true)
    (Hif_false: sem_Ind_if_false)
    (Hwhile_true: sem_Ind_while_true)
    (Hwhile_false: sem_Ind_while_false)
  .

  Definition sem_Ind_for : Prop :=
    forall (s1 s2 : estate) (i : var_i) (d : dir)
           (lo hi : pexpr) (c : cmd) (vlo vhi : Z),
      sem_pexpr true gd s1 lo = ok (Vint vlo) ->
      sem_pexpr true gd s1 hi = ok (Vint vhi) ->
      sem_for i (wrange d vlo vhi) s1 c s2 ->
      Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.

  Definition sem_Ind_for_nil : Prop :=
    forall (s : estate) (i : var_i) (c : cmd), Pfor i [::] s c s.

  Definition sem_Ind_for_cons : Prop :=
    forall (s1 s1' s2 s3 : estate) (i : var_i)
           (w : Z) (ws : seq Z) (c : cmd),
      write_var true i w s1 = Ok error s1' ->
      sem s1' c s2 -> Pc s1' c s2 ->
      sem_for i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.

  Hypotheses
    (Hfor: sem_Ind_for)
    (Hfor_nil: sem_Ind_for_nil)
    (Hfor_cons: sem_Ind_for_cons)
  .

  Definition sem_Ind_call : Prop :=
    forall (s1 : estate) (scs2 : syscall_state_t) (m2 : mem) (s2 : estate)
           (xs : lvals) (fn : funname) (args : pexprs) (vargs vs : seq value),
      sem_pexprs (~~direct_call) gd s1 args = ok vargs →
      sem_call (escs s1) (emem s1) fn vargs scs2 m2 vs →
      Pfun (escs s1) (emem s1) fn vargs scs2 m2 vs →
      write_lvals (~~direct_call) gd (with_scs (with_mem s1 m2) scs2) xs vs = ok s2 →
      Pi_r s1 (Ccall xs fn args) s2.

  Definition sem_Ind_proc : Prop :=
    forall (scs1 : syscall_state_t) (m1 : mem) (scs2 : syscall_state_t) (m2 : mem)
           (fn:funname) (f : fundef) (vargs vargs': seq value)
           (s0 s1 s2: estate) (vres vres': seq value),
      get_fundef (p_funcs P) fn = Some f ->
      mapM2 ErrType dc_truncate_val f.(f_tyin) vargs' = ok vargs ->
      init_state f.(f_extra) (p_extra P) ev (Estate scs1 m1 Vm.init) = ok s0 ->
      write_vars (~~direct_call) (f_params f) vargs s0 = ok s1 ->
      sem s1 (f_body f) s2 ->
      Pc s1 (f_body f) s2 ->
      get_var_is (~~ direct_call) s2.(evm) (f_res f) = ok vres ->
      mapM2 ErrType dc_truncate_val f.(f_tyout) vres = ok vres' ->
      scs2 = s2.(escs) ->
      m2 = finalize f.(f_extra) s2.(emem) ->
      Pfun scs1 m1 fn vargs' scs2 m2 vres'.

  Hypotheses
    (Hcall: sem_Ind_call)
    (Hproc: sem_Ind_proc)
  .

  Fixpoint sem_Ind (e : estate) (l : cmd) (e0 : estate) (s : sem e l e0) {struct s} :
    Pc e l e0 :=
    match s in sem e1 l0 e2 return Pc e1 l0 e2 with
    | @Eskip s0 => Hnil s0
    | @Eseq s1 s2 s3 i c s0 s4 =>
        @Hcons s1 s2 s3 i c s0 (@sem_I_Ind s1 i s2 s0) s4 (@sem_Ind s2 c s3 s4)
    end

  with sem_i_Ind (e : estate) (i : instr_r) (e0 : estate) (s : sem_i e i e0) {struct s} :
    Pi_r e i e0 :=
    match s in sem_i e1 i0 e2 return Pi_r e1 i0 e2 with
    | @Eassgn s1 s2 x tag ty e1 v v' h1 h2 h3 =>
      @Hasgn s1 s2 x tag ty e1 v v' h1 h2 h3
    | @Eopn s1 s2 t o xs es e1 =>
      @Hopn s1 s2 t o xs es e1
    | @Esyscall s1 scs m s2 o xs es ves vs h1 h2 h3 =>
      @Hsyscall s1 scs m s2 o xs es ves vs h1 h2 h3
    | @Eif_true s1 s2 e1 c1 c2 e2 s0 =>
      @Hif_true s1 s2 e1 c1 c2 e2 s0 (@sem_Ind s1 c1 s2 s0)
    | @Eif_false s1 s2 e1 c1 c2 e2 s0 =>
      @Hif_false s1 s2 e1 c1 c2 e2 s0 (@sem_Ind s1 c2 s2 s0)
    | @Ewhile_true s1 s2 s3 s4 a c e1 c' s0 e2 s5 s6 =>
      @Hwhile_true s1 s2 s3 s4 a c e1 c' s0 (@sem_Ind s1 c s2 s0) e2 s5 (@sem_Ind s2 c' s3 s5) s6
          (@sem_i_Ind s3 (Cwhile a c e1 c') s4 s6)
    | @Ewhile_false s1 s2 a c e1 c' s0 e2 =>
      @Hwhile_false s1 s2 a c e1 c' s0 (@sem_Ind s1 c s2 s0) e2
    | @Efor s1 s2 i0 d lo hi c vlo vhi e1 e2 s0 =>
      @Hfor s1 s2 i0 d lo hi c vlo vhi e1 e2 s0
        (@sem_for_Ind i0 (wrange d vlo vhi) s1 c s2 s0)
    | @Ecall s1 scs2 m2 s2 xs f13 args vargs vs e2 s0 e3 =>
      @Hcall s1 scs2 m2 s2 xs f13 args vargs vs e2 s0
        (@sem_call_Ind (escs s1) (emem s1) f13 vargs scs2 m2 vs s0) e3
    end

  with sem_I_Ind (e : estate) (i : instr) (e0 : estate) (s : sem_I e i e0) {struct s} :
    Pi e i e0 :=
    match s in sem_I e1 i0 e2 return Pi e1 i0 e2 with
    | @EmkI ii i0 s1 s2 s0 => @HmkI ii i0 s1 s2 s0 (@sem_i_Ind s1 i0 s2 s0)
    end

  with sem_for_Ind (v : var_i) (l : seq Z) (e : estate) (l0 : cmd) (e0 : estate)
         (s : sem_for v l e l0 e0) {struct s} : Pfor v l e l0 e0 :=
    match s in sem_for v0 l1 e1 l2 e2 return Pfor v0 l1 e1 l2 e2 with
    | EForDone s0 i c => Hfor_nil s0 i c
    | @EForOne s1 s1' s2 s3 i w ws c e1 s0 s4 =>
      @Hfor_cons s1 s1' s2 s3 i w ws c e1 s0 (@sem_Ind s1' c s2 s0)
         s4 (@sem_for_Ind i ws s2 c s3 s4)
    end

  with sem_call_Ind (scs : syscall_state_t) (m : mem) (f13 : funname) (l : seq value) (scs0 : syscall_state_t) (m0 : mem)
         (l0 : seq value) (s : sem_call scs m f13 l scs0 m0 l0) {struct s} : Pfun scs m f13 l scs0 m0 l0 :=
    match s with
    | @EcallRun scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hget Hca Hi Hw Hsem Hvres Hcr hscs Hfi=>
      @Hproc scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hget Hca Hi Hw Hsem (sem_Ind Hsem) Hvres Hcr hscs Hfi
    end.

End SEM_IND.

End SEM.

(* ** Starting lemmas
 * ------------------------------------------------------------------- *)
Lemma type_of_get_global gd g v :
  get_global gd g = ok v -> type_of_val v = vtype g.
Proof. by move=> /get_globalI [?[]]. Qed.

Lemma get_global_defined gd x v : get_global gd x = ok v -> is_defined v.
Proof. by move=> /get_globalI [gv [_ -> _]]; case: gv. Qed.

Lemma get_gvar_compat wdb gd vm x v : get_gvar wdb gd vm x = ok v ->
   (~~wdb || is_defined v) /\ compat_val (vtype x.(gv)) v.
Proof.
  rewrite /get_gvar;case:ifP => ? heq.
  + by apply: get_var_compat heq.
  by rewrite /compat_val (type_of_get_global heq) (get_global_defined heq) orbT.
Qed.

Lemma get_var_to_word wdb vm x ws w :
  vtype x = sword ws ->
  get_var wdb vm x >>= to_word ws = ok w ->
  get_var wdb vm x = ok (Vword w).
Proof.
  t_xrbindP => htx v /dup[] /get_varP [] -> hdef + ->.
  rewrite htx => hcomp /to_wordI' [ws1 [w1 [hws hx ->]]].
  move: hcomp; rewrite hx => /compat_valE [ws2 [?] hws']; subst ws2.
  have <- : ws1 = ws; last by rewrite zero_extend_u.
  case: sw_allowed hws' => // hws'; apply: cmp_le_antisym hws' hws.
Qed.

Lemma to_word_get_var wdb vm x ws (w:word ws) :
  get_var wdb vm x = ok (Vword w) ->
  get_var wdb vm x >>= to_word ws = ok w.
Proof. by move=> -> /=; rewrite truncate_word_u. Qed.

(* Remark compat_type b = if b then subtype else eq *)
Lemma type_of_get_gvar x gd vm v :
  get_gvar true gd vm x = ok v ->
  compat_type sw_allowed (type_of_val v) (vtype x.(gv)).
Proof. by move=> /get_gvar_compat [/=hd]; rewrite /compat_val hd orbF. Qed.

Lemma type_of_get_gvar_sub x gd vm v :
  get_gvar true gd vm x = ok v ->
  subtype (type_of_val v) (vtype x.(gv)).
Proof. by move=> /type_of_get_gvar /compat_type_subtype. Qed.

(* We have a more precise result in the non-word cases. *)
Lemma type_of_get_gvar_not_word gd vm x v :
  (sw_allowed -> ~ is_sword x.(gv).(vtype)) ->
  get_gvar true gd vm x = ok v ->
  type_of_val v = x.(gv).(vtype).
Proof.
  move=> hnword; rewrite /get_gvar; case: ifP => ?.
  + by apply: type_of_get_var_not_word.
  by apply type_of_get_global.
Qed.

Lemma on_arr_varP {syscall_state : Type} {ep : EstateParams syscall_state}
  A (f : forall n, WArray.array n -> exec A) wdb v vm x P :
  (forall n t, vtype x = sarr n ->
               get_var wdb vm x = ok (@Varr n t) ->
               f n t = ok v -> P) ->
  on_arr_var (get_var wdb vm x) f = ok v -> P.
Proof.
  rewrite /on_arr_var=> H;apply: rbindP => vx hx.
  have [_] := get_var_compat hx; case: vx hx => // len t h /compat_valE h1.
  by apply: H.
Qed.

Lemma on_arr_gvarP A (f : forall n, WArray.array n -> exec A) wdb v gd s x P:
  (forall n t, vtype x.(gv) = sarr n ->
               get_gvar wdb gd s x = ok (@Varr n t) ->
               f n t = ok v -> P) ->
  on_arr_var (get_gvar wdb gd s x) f = ok v -> P.
Proof.
  rewrite /get_gvar.
  rewrite /on_arr_var=> H;apply: rbindP => vx hx.
  have [_] := get_gvar_compat hx; case: vx hx => // len t h /compat_valE h1.
  by apply: H.
Qed.

Lemma get_gvar_glob wdb gd x vm : is_glob x -> get_gvar wdb gd vm x = get_global gd (gv x).
Proof. by rewrite /get_gvar /is_lvar /is_glob => /eqP ->. Qed.

Lemma get_gvar_nglob wdb gd x vm : ~~is_glob x -> get_gvar wdb gd vm x = get_var wdb vm (gv x).
Proof. by rewrite /get_gvar is_lvar_is_glob => ->. Qed.

Section WITH_SCS.

  Context
    {asm_op syscall_state : Type}
    {ep : EstateParams syscall_state}
    {spp : SemPexprParams}
    (wdb : bool)
    (gd : glob_decls)
    (s1 : estate)
    (scs : syscall_state).

  Let P e : Prop :=
    sem_pexpr wdb gd s1 e = sem_pexpr wdb gd (with_scs s1 scs) e.

  Let Q es : Prop :=
    sem_pexprs wdb gd s1 es = sem_pexprs wdb gd (with_scs s1 scs) es.

  Lemma sem_pexpr_es_with_scs : (∀ e, P e) * (∀ es, Q es).
  Proof.
    apply: pexprs_ind_pair; split; subst P Q => //=; rewrite /sem_pexprs => *;
    repeat match goal with H: _ = _ |- _ => rewrite H // end.
  Qed.

  Definition sem_pexpr_with_scs := fst sem_pexpr_es_with_scs.
  Definition sem_pexprs_with_scs := snd sem_pexpr_es_with_scs.

End WITH_SCS.

Section EXEC_ASM.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {asmop : asmOp asm_op}.

Lemma sopn_toutP o vs vs' : exec_sopn o vs = ok vs' ->
  List.map type_of_val vs' = sopn_tout o.
Proof.
  rewrite /exec_sopn /sopn_tout /sopn_sem.
  t_xrbindP => p _ <-;apply type_of_val_ltuple.
Qed.

Lemma sopn_tinP o vs vs' : exec_sopn o vs = ok vs' ->
  all2 subtype (sopn_tin o) (List.map type_of_val vs).
Proof.
  rewrite /exec_sopn /sopn_tin /sopn_sem.
  case (get_instr_desc o) => /= _ tin _ tout _ semi _ _.
  t_xrbindP => p hp _.
  elim: tin vs semi hp => /= [ | t tin hrec] [ | v vs] // semi.
  by t_xrbindP => sv /= /of_val_subtype -> /hrec.
Qed.

End EXEC_ASM.

(* ** Instructions
 * -------------------------------------------------------------------- *)


Section SEM.

Context
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {scP : semCallParams}
  (P : prog)
  (ev : extra_val_t).

Notation gd := (p_globs P).
Notation sem     := (sem P ev).
Notation sem_i   := (sem_i P ev).
Notation sem_I   := (sem_I P ev).
Notation sem_for := (sem_for P ev).
Notation sem_call := (sem_call P ev).

Lemma semE s c s' :
  sem s c s' ->
  match c with
  | [::] => s' = s
  | i :: c' => exists si, sem_I s i si /\ sem si c' s'
  end.
Proof. by case; eauto. Qed.

Lemma sem_IE s i s' :
  sem_I s i s' ->
  let 'MkI ii r := i in
  sem_i s r s'.
Proof. by case. Qed.

Lemma sem_iE s i s' :
  sem_i s i s' ->
  match i with
  | Cassgn lv _ ty e =>
    ∃ v v',
    [/\ sem_pexpr true gd s e = ok v, truncate_val ty v = ok v' & write_lval true gd lv v' s = ok s' ]
  | Copn lvs _ op es => sem_sopn gd op s lvs es = ok s'
  | Csyscall xs o es =>
    ∃ scs m ves vs,
    [/\ sem_pexprs true gd s es = ok ves,
        exec_syscall s.(escs) s.(emem) o ves = ok (scs, m, vs) &
        write_lvals true gd (with_scs (with_mem s m) scs) xs vs = ok s']
  | Cif e th el =>
    ∃ b, sem_pexpr true gd s e = ok (Vbool b) ∧ sem s (if b then th else el) s'
  | Cfor i (d, lo, hi) c =>
    ∃ vlo vhi,
    [/\ sem_pexpr true gd s lo = ok (Vint vlo), sem_pexpr true gd s hi = ok (Vint vhi) &
        sem_for i (wrange d vlo vhi) s c s' ]
  | Cwhile a c e c' =>
    ∃ si b,
       [/\ sem s c si, sem_pexpr true gd si e = ok (Vbool b) &
                       if b then ∃ sj, sem si c' sj ∧ sem_i sj (Cwhile a c e c') s' else si = s' ]
  | Ccall xs f es =>
    ∃ vs scs2 m2 rs,
    [/\ sem_pexprs (~~direct_call) gd s es = ok vs,
        sem_call s.(escs) s.(emem) f vs scs2 m2 rs &
        write_lvals (~~direct_call) gd (with_scs (with_mem s m2) scs2) xs rs = ok s']
  end.
Proof.
  case => {s i s'} //.
  - by move => s s' x _ ty e v v' hv hv' hw; exists v, v'.
  - by move => s scs m s' xs o es ves vs h1 h2 h3; exists scs, m, ves, vs.
  - by move => s s' e th el he hth; exists true.
  - by move => s s' e th el he hel; exists false.
  - by move => s si sj s' c e c' hc he hc' hrec; exists si, true; constructor => //; exists sj.
  - by move => s s' c e c' hc he; exists s', false.
  - by move => s s' i d lo hi c vlo vhi hlo hhi hc; exists vlo, vhi.
  by move=> s scs m s' xs f es vs rs hvs h hrs; exists vs, scs, m, rs.
Qed.

Lemma sem_forE i ws s c s' :
  sem_for i ws s c s' →
  if ws is w :: ws then
    exists s1 s2,
      [/\
       write_var true i (Vint w) s = ok s1,
       sem s1 c s2 &
       sem_for i ws s2 c s' ]
  else s' = s.
Proof.
  case => { i ws s c s' } // s s1 s2 s' i w ws c ok_s1 exec_c ih.
  by exists s1, s2.
Qed.

Lemma sem_callE scs1 m1 fn vargs' scs2 m2 vres' :
  sem_call scs1 m1 fn vargs' scs2 m2 vres' ->
  ∃ f,
    get_fundef (p_funcs P) fn = Some f ∧
  ∃ vargs s0 s1 s2 vres,
  [/\
    mapM2 ErrType dc_truncate_val f.(f_tyin) vargs' = ok vargs,
    init_state f.(f_extra) (p_extra P) ev (Estate scs1 m1 Vm.init) = ok s0 /\
    write_vars (~~direct_call) f.(f_params) vargs s0 = ok s1,
    sem s1 f.(f_body) s2,
    get_var_is (~~ direct_call) s2.(evm) f.(f_res) = ok vres /\
    mapM2 ErrType dc_truncate_val f.(f_tyout) vres = ok vres' &
    scs2 = s2.(escs) /\ m2 = finalize f.(f_extra) s2.(emem) ].
Proof.
  case => { scs1 m1 fn vargs' scs2 m2 vres' } scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres'.
  move => hf ha hi hw hc hr ht hscs hfi.
  exists f; split => //.
  by exists vargs, s0, s1, s2, vres.
Qed.

Lemma sem_app l1 l2 s1 s2 s3:
  sem s1 l1 s2 -> sem s2 l2 s3 ->
  sem s1 (l1 ++ l2) s3.
Proof.
  elim: l1 s1;first by move => s1 /semE ->.
  move=> a l Hrec s1 /semE [si] [h1 hi] h.
  by apply (Eseq h1);apply Hrec.
Qed.

Lemma sem_seq1 i s1 s2:
  sem_I s1 i s2 -> sem s1 [::i] s2.
Proof.
  move=> Hi; apply (Eseq Hi);constructor.
Qed.

Lemma sem_seq1_iff (i : instr) s1 s2:
  sem_I s1 i s2 <-> sem s1 [:: i] s2.
Proof.
  split; first by apply sem_seq1.
  by case/semE => ? [?] /semE ->.
Qed.

Lemma sem_seq_ir ii ir s0 s1 :
  sem_i s0 ir s1
  -> sem s0 [:: MkI ii ir ] s1.
Proof. by move=> /(EmkI ii) /sem_seq1. Qed.

End SEM.

Section WITH_PARAMS.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}.

Definition write_var_Spec (wdb : bool) (x : var) (v : value) (s : estate) (s' : estate) : Prop :=
   [/\ s' = with_vm s (evm s).[x <- v],
       DB wdb v &  truncatable wdb (vtype x) v].

Definition write_get_var_Spec (wdb : bool) (x : var_i) (v : value) (s : estate) (s' : estate) : Prop :=
  [/\ DB wdb v, truncatable wdb (vtype x) v &
    (forall y, get_var wdb (evm s') y =
      if v_var x == y then
        Let _:= assert (~~wdb || is_defined v) ErrAddrUndef in ok (vm_truncate_val (vtype x) v)
      else get_var wdb (evm s) y)].

Definition write_get_gvar_Spec gd (wdb : bool) (x : var_i) (v : value) (s : estate) (s' : estate) : Prop :=
  [/\ DB wdb v, truncatable wdb (vtype x) v &
    (forall y, get_gvar wdb gd (evm s') y =
      if is_lvar y && (v_var x == gv y) then
        Let _:= assert (~~wdb || is_defined v) ErrAddrUndef in ok (vm_truncate_val (vtype x) v)
      else get_gvar wdb gd (evm s) y)].

Lemma get_var_set wdb vm x v y :
  truncatable wdb (vtype x) v ->
  get_var wdb vm.[x <- v] y =
     if x == y then
       Let _ := assert (~~wdb || is_defined v) ErrAddrUndef in ok (vm_truncate_val (vtype x) v)
     else get_var wdb vm y.
Proof. by rewrite {1}/get_var Vm.setP; case: eqP => // *; rewrite -vm_truncate_val_defined. Qed.

Lemma get_var_set_var wdb vm vm' x y v :
  (~~ wdb || is_defined v) ->
  set_var wdb vm y v = ok vm' ->
  get_var wdb vm' x =
    if x == y
    then ok (vm_truncate_val (vtype x) v)
    else get_var wdb vm x.
Proof.
  move=> hv /set_varP [_ ? ->].
  rewrite get_var_set // eq_sym hv /=.
  by case: eqP => [->|_].
Qed.

Lemma get_var_eq wdb x vm v :
  truncatable wdb (vtype x) v ->
  get_var wdb vm.[x <- v] x =
    Let _ := assert (~~wdb || is_defined v) ErrAddrUndef in ok (vm_truncate_val (vtype x) v).
Proof. by move=> h; rewrite get_var_set // eqxx. Qed.

Lemma get_var_neq wdb x y vm v : x <> y -> get_var wdb vm.[x <- v] y = get_var wdb vm y.
Proof. by move=> hne; rewrite /get_var Vm.setP_neq //; apply /eqP. Qed.

Lemma get_var_set_eq wdb vm1 vm2 (x y : var) v:
  get_var wdb vm1 y = get_var wdb vm2 y ->
  get_var wdb vm1.[x <- v] y = get_var wdb vm2.[x <- v] y.
Proof. by rewrite /get_var !Vm.setP; case: eqP. Qed.

Lemma get_gvar_eq wdb gd x vm v :
  truncatable wdb (vtype (gv x)) v ->
  ~ is_glob x ->
  get_gvar wdb gd vm.[x.(gv) <- v] x =
    Let _ := assert (~~wdb || is_defined v) ErrAddrUndef in ok (vm_truncate_val (vtype (gv x)) v).
Proof.
  by move=> h1 /negP h2; rewrite /get_gvar is_lvar_is_glob h2 get_var_eq.
Qed.

Lemma get_gvar_neq wdb gd (x:var) y vm v :
  (~ is_glob y -> x <> (gv y)) -> get_gvar wdb gd vm.[x <- v] y = get_gvar wdb gd vm y.
Proof.
  move=> h; rewrite /get_gvar is_lvar_is_glob.
  by case: negP => // hg; rewrite get_var_neq //; apply h.
Qed.

Lemma write_var_truncate wdb (x:var_i) v :
  DB wdb v -> truncatable wdb (vtype x) v ->
  forall s, write_var wdb x v s = ok (with_vm s (evm s).[x <- v]).
Proof. by move=> hdb htr s; rewrite /write_var (set_var_truncate hdb htr). Qed.

Lemma write_varP wdb x v s s':
  write_var wdb x v s = ok s' <-> write_var_Spec wdb x v s s'.
Proof.
  split.
  + by rewrite /write_var; t_xrbindP => vm' /set_varP [??->] ?; econstructor; eauto.
  by move=> [-> hdb htr]; rewrite write_var_truncate.
Qed.

Lemma write_varP_arr x len (a:WArray.array len) s s':
   write_var true x (Varr a) s = ok s' ->
   [/\ type_of_val (Varr a) = vtype x,
       truncatable true (vtype x) (Varr a),
       vm_truncate_val (vtype x) (Varr a) = Varr a &
       s' = with_vm s (evm s).[x <- (Varr a)]].
Proof. move=> /write_varP [-> hdb /vm_truncate_valE [-> ?]] => //. Qed.

Lemma write_var_spec wdb x v s1 s2 s1':
  write_var wdb x v s1 = ok s2 ->
  exists vmx, [/\ write_var wdb x v s1' = ok (with_vm s1' vmx),
                  evm s1' =[\ Sv.singleton x] vmx & vmx.[x] = (evm s2).[x]].
Proof.
  rewrite /write_var; t_xrbindP => vm hs <-{s2}.
  by have [vmx [-> ?? /=]] := set_var_spec (evm s1') hs; exists vmx.
Qed.

Lemma write_var_eq_type wdb (x:var_i) v:
  type_of_val v = vtype x -> DB wdb v ->
  forall s, write_var wdb x v s = ok (with_vm s (evm s).[x <- v]).
Proof. move=> h ?; apply/write_var_truncate => //; rewrite -h; apply truncatable_type_of. Qed.

Lemma write_get_varP wdb x v s s':
  write_var wdb x v s = ok s' -> write_get_var_Spec wdb x v s s'.
Proof. by move=> /write_varP [-> hdb htr]; econstructor; eauto => y /=; rewrite get_var_set. Qed.

Lemma write_getP_eq wdb (x:var_i) v s s':
  write_var wdb x v s = ok s' ->
  [/\ DB wdb v, truncatable wdb (vtype x) v &
      (evm s').[x] = (vm_truncate_val (vtype x) v)].
Proof. by move=> /write_varP => -[-> -> ->]; rewrite Vm.setP_eq. Qed.

Lemma write_getP_neq wdb (x:var_i) v s s' y: v_var x != y ->
  write_var wdb x v s = ok s' -> (evm s').[y] = (evm s).[y].
Proof. by move=> hne /write_varP => -[-> ??]; rewrite Vm.setP_neq. Qed.

Lemma write_get_varP_eq wdb (x:var_i) v s s':
  write_var wdb x v s = ok s' ->
  [/\ DB wdb v, truncatable wdb (vtype x) v &
      get_var wdb (evm s') x =
        Let _ := assert (~~wdb || is_defined v) ErrAddrUndef in ok (vm_truncate_val (vtype x) v)].
Proof. by move=> /write_get_varP [? ? ->]; rewrite eqxx. Qed.

Lemma write_get_varP_neq wdb wdb' (x:var_i) v s s' y: v_var x != y ->
  write_var wdb x v s = ok s' -> get_var wdb' (evm s') y = get_var wdb' (evm s) y.
Proof. rewrite /get_var => hne /write_varP => -[-> ??]; rewrite Vm.setP_neq //. Qed.

Lemma write_get_gvarP gd wdb x v s s':
  write_var wdb x v s = ok s' -> write_get_gvar_Spec gd wdb x v s s'.
Proof.
  move=> /write_get_varP [hdb htr hget]; econstructor; eauto => y.
  by rewrite /get_gvar hget; case: is_lvar.
Qed.

Lemma write_get_gvarP_eq wdb gd (x:var_i) v s s':
  write_var wdb x v s = ok s' ->
  [/\ DB wdb v, truncatable wdb (vtype x) v &
    get_gvar wdb gd (evm s') (mk_lvar x) =
    Let _ := assert (~~wdb || is_defined v) ErrAddrUndef in ok (vm_truncate_val (vtype x) v)].
Proof. by move=> /(write_get_gvarP gd) [hdb htr ->]; rewrite /= eqxx. Qed.

Lemma write_get_gvarP_neq wdb gd (x:var_i) v s s' y: (is_lvar y -> v_var x != gv y) ->
  write_var wdb x v s = ok s' -> get_gvar wdb gd (evm s') y = get_gvar wdb gd (evm s) y.
Proof.
  move=> h /(write_get_gvarP gd) [htr hdb ->].
  by case: is_lvar h => // /(_ erefl) /negbTE ->.
Qed.

Lemma is_wconstP wdb gd s sz e w:
  is_wconst sz e = Some w →
  sem_pexpr wdb gd s e >>= to_word sz = ok w.
Proof.
  case: e => // - [] // sz' e /=; case: ifP => // hle /oseq.obindI [z] [h] [<-].
  have := is_constP e; rewrite h => {h} /is_reflect_some_inv -> {e}.
  by rewrite /= truncate_word_le // zero_extend_wrepr.
Qed.

Lemma is_wconstI ws e w :
  is_wconst ws e = Some w ->
  exists ws' z, e = Papp1 (Oword_of_int ws') (Pconst z).
Proof.
  case: e => //.
  move=> [] //= ? e.
  case: (_ <= _)%CMP; last done.
  case: e => //.
  by eexists; eexists.
Qed.

Lemma vrvP_var wdb (x:var_i) v s1 s2 :
  write_var wdb x v s1 = ok s2 ->
  s1.(evm) =[\ Sv.singleton x] s2.(evm).
Proof. by rewrite /write_var;t_xrbindP => vm /set_var_eq_ex ? <-. Qed.

Lemma write_noneP wdb s s' ty v:
  write_none wdb s ty v = ok s' ->
  [/\ s' = s, truncatable wdb ty v & DB wdb v].
Proof. by rewrite /write_none; t_xrbindP. Qed.

Lemma vrvP wdb gd (x:lval) v s1 s2 :
  write_lval gd wdb x v s1 = ok s2 ->
  s1.(evm) =[\ vrv x] s2.(evm).
Proof.
  case x => /= [ _ ty | ? /vrvP_var| al sz y e| al aa sz y e | aa sz len y e] //.
  + by move=> /write_noneP [->].
  + by t_xrbindP => ptr yv hyv hptr ptr' ev hev hptr' w hw m hm <-.
  + by apply: on_arr_varP; t_xrbindP => *; apply: vrvP_var; eauto.
  by apply: on_arr_varP; t_xrbindP => *; apply: vrvP_var; eauto.
Qed.

Lemma vrvsP wdb gd xs vs s1 s2 :
  write_lvals wdb gd s1 xs vs = ok s2 ->
  s1.(evm) =[\ vrvs xs] s2.(evm).
Proof.
  elim: xs vs s1 s2 => [|x xs Hrec] [|v vs] s1 s2 //=.
  + by move=> [<-].
  apply: rbindP => s /vrvP Hrv /Hrec Hrvs.
  rewrite vrvs_cons; apply: eq_exT.
  + by apply: eq_exI Hrv;SvD.fsetdec.
  by apply: eq_exI Hrvs;SvD.fsetdec.
Qed.

Lemma write_var_memP wdb x v s1 s2 :
  write_var wdb x v s1 = ok s2 → emem s1 = emem s2.
Proof. by apply: rbindP=> ?? [] <-. Qed.

Lemma write_vars_memP wdb xs vs a z :
  write_vars wdb xs vs a = ok z →
  emem a = emem z.
Proof.
  elim: xs vs a => [ | x xs ih ] [] //.
  - by move => a [<-].
  by move => v vs a /=; t_xrbindP => b /write_var_memP -> /ih.
Qed.

Lemma lv_write_memP wdb gd (x:lval) v s1 s2:
  ~~ lv_write_mem x ->
  write_lval gd wdb x v s1 = ok s2 ->
  emem s1 = emem s2.
Proof.
  case: x=> //= [v0 t|v0|al aa ws v0 p|aa ws len v0 p] _.
  + by move => /write_noneP [-> _].
  + by apply: write_var_memP.
  + by apply: on_arr_varP; t_xrbindP=> *; apply: write_var_memP; eauto.
  by apply on_arr_varP; t_xrbindP => *; apply: write_var_memP; eauto.
Qed.

Lemma write_var_scsP wdb x v s1 s2 :
  write_var wdb x v s1 = ok s2 → escs s1 = escs s2.
Proof. by apply: rbindP=> ?? [] <-. Qed.

Lemma lv_write_scsP wdb gd (x:lval) v s1 s2:
  write_lval gd wdb x v s1 = ok s2 ->
  escs s1 = escs s2.
Proof.
  case: x=> /= [v0 t|v0|ws x e|al aa ws v0 p|aa ws len v0 p].
  + by move => /write_noneP [-> _].
  + by apply: write_var_scsP.
  + by t_xrbindP => *; subst s2.
  + by apply: on_arr_varP; t_xrbindP=> *; apply: write_var_scsP; eauto.
  by apply on_arr_varP; t_xrbindP => *; apply: write_var_scsP; eauto.
Qed.

Section Write.

Context
  {dc:DirectCall}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {sCP : semCallParams}.

Variable P : prog.
Variable ev : extra_val_t.

Let Pc s1 c s2 := s1.(evm) =[\ write_c c] s2.(evm).

Let Pi_r s1 i s2 := s1.(evm) =[\ write_i i] s2.(evm).

Let Pi s1 i s2 := s1.(evm) =[\ write_I i] s2.(evm).

Let Pfor x (_ : seq Z) s1 c s2 :=
  s1.(evm) =[\ (Sv.union (Sv.singleton x) (write_c c))] s2.(evm).

Let Pfun
  (_ : syscall_state_t)
  (_ : mem)
  (_ : funname)
  (_ : seq value)
  (_ : syscall_state_t)
  (_ : mem)
  (_ : seq value) :=
  True.

Lemma writeP c s1 s2 :
   sem P ev s1 c s2 -> s1.(evm) =[\ write_c c] s2.(evm).
Proof.
  apply:
    (sem_Ind
       (Pc := Pc)
       (Pi_r := Pi_r)
       (Pi := Pi)
       (Pfor := Pfor)
       (Pfun := Pfun))
    => {c s1 s2} //.
  + move=> s1 s2 s3 i c _ Hi _ Hc z;rewrite write_c_cons => Hnin.
    by rewrite Hi ?Hc //;SvD.fsetdec.
  + move=> s1 s2 x tag ty e v v' ? hty Hw z.
    by rewrite write_i_assgn;apply (vrvP Hw).
  + move=> s1 s2 t o xs es; rewrite /sem_sopn.
    case: (Let _ := sem_pexprs _ _ _ _ in _) => //= vs Hw z.
    by rewrite write_i_opn;apply (vrvsP Hw).
  + move=> s1 scs m s2 x o es ves vs hes hscs hw.
    by rewrite /Pi_r write_i_syscall; apply (vrvsP hw).
  + by move=> s1 s2 e c1 c2 _ _ Hrec z;rewrite write_i_if => Hnin;apply Hrec;SvD.fsetdec.
  + by move=> s1 s2 e c1 c2 _ _ Hrec z;rewrite write_i_if => Hnin;apply Hrec;SvD.fsetdec.
  + by move=> s1 s2 s3 s4 a c e c' _ Hc _ _ Hc' _ Hw z Hnin; rewrite Hc ?Hc' ?Hw //;
     move: Hnin; rewrite write_i_while; SvD.fsetdec.
  + move=> s1 s2 a c e c' _ Hc _ z Hnin; rewrite Hc //.
    by move: Hnin; rewrite write_i_while; SvD.fsetdec.
  + by move=> s1 s2 i d lo hi c vlo vhi _ _ _ Hrec z;rewrite write_i_for;apply Hrec.
  + move=> s1 s1' s2 s3 i w ws c Hw _ Hc _ Hf z Hnin.
    by rewrite (vrvP_var Hw) ?Hc ?Hf //;SvD.fsetdec.
  move=> s1 scs2 m2 s2 xs fn args vargs vs _ _ _ Hw z.
  rewrite write_i_call. apply (vrvsP Hw).
Qed.

Lemma write_IP i s1 s2 :
   sem_I P ev s1 i s2 -> s1.(evm) =[\ write_I i] s2.(evm).
Proof.
  move=> /sem_seq1 -/writeP.
  have := write_c_cons i [::].
  move=> Heq H x Hx;apply H; SvD.fsetdec.
Qed.

Lemma write_iP i s1 s2 :
   sem_i P ev s1 i s2 -> s1.(evm) =[\ write_i i] s2.(evm).
Proof. by move=> h; have /write_IP := EmkI dummy_instr_info h. Qed.

End Write.

Lemma set_var_disjoint_eq_on wdb x s v vm vm' :
  ~~ Sv.mem x s ->
  set_var wdb vm x v = ok vm' ->
  vm =[ s ] vm'.
Proof.
  move=> /Sv_memP hx /set_varP [_ _ ->] y hy.
  by rewrite Vm.setP_neq //; apply /eqP => ?; subst y; apply hx.
Qed.

Lemma disjoint_eq_on wdb gd s r s1 s2 v:
  disjoint s (vrv r) ->
  write_lval wdb gd r v s1 = ok s2 ->
  s1.(evm) =[s] s2.(evm).
Proof.
  move=> Hd /vrvP H z Hnin;apply H.
  move:Hd;rewrite /disjoint /is_true Sv.is_empty_spec;SvD.fsetdec.
Qed.

Lemma disjoint_eq_ons wdb gd s r s1 s2 v:
  disjoint s (vrvs r) ->
  write_lvals wdb gd s1 r v = ok s2 ->
  s1.(evm) =[s] s2.(evm).
Proof.
  move=> Hd /vrvsP H z Hnin;apply H.
  move:Hd;rewrite /disjoint /is_true Sv.is_empty_spec;SvD.fsetdec.
Qed.

Lemma get_var_eq_on wdb s vm' vm v: Sv.In v s -> vm =[s]  vm' -> get_var wdb vm v = get_var wdb vm' v.
Proof. by move=> hin hvm;rewrite /get_var hvm. Qed.

Lemma get_gvar_eq_on wdb s gd vm' vm v: Sv.Subset (read_gvar v) s -> vm =[s]  vm' ->
  get_gvar wdb gd vm v = get_gvar wdb gd vm' v.
Proof.
  rewrite /read_gvar /get_gvar; case: ifP => // _ hin.
  by apply: get_var_eq_on; SvD.fsetdec.
Qed.

Lemma on_arr_var_eq_on wdb s' X s A x (f: ∀ n, WArray.array n → exec A) :
   evm s =[X] evm s' -> Sv.In x X ->
   on_arr_var (get_var wdb (evm s) x) f = on_arr_var (get_var wdb (evm s') x) f.
Proof.
  by move=> Heq Hin;rewrite /on_arr_var;rewrite (get_var_eq_on _ Hin Heq).
Qed.

Lemma on_arr_gvar_eq_on wdb s' gd X s A x (f: ∀ n, WArray.array n → exec A) :
   evm s =[X] evm s' -> Sv.Subset (read_gvar x) X ->
   on_arr_var (get_gvar wdb gd (evm s) x) f = on_arr_var (get_gvar wdb gd (evm s') x) f.
Proof.
  move=> Heq; rewrite /get_gvar /read_gvar;case:ifP => _ Hin //.
  by apply: (on_arr_var_eq_on _ (X := X)) => //; SvD.fsetdec.
Qed.

Lemma get_var_eq_ex wdb vm1 vm2 X x:
  ~Sv.In x X ->
  vm1 =[\ X] vm2 ->
  get_var wdb vm1 x = get_var wdb vm2 x.
Proof. by move=> Hin Hvm;rewrite /get_var Hvm. Qed.

Lemma get_gvar_eq_ex wdb gd vm1 vm2 X x:
  disjoint (read_gvar x) X ->
  vm1 =[\ X] vm2 ->
  get_gvar wdb gd vm1 x = get_gvar wdb gd vm2 x.
Proof.
  rewrite /read_gvar /get_gvar; case: ifP => // _ /disjointP hin.
  apply: get_var_eq_ex; apply hin; SvD.fsetdec.
Qed.

Section READ_E_ES_EQ_ON.

  Context (wdb : bool) (gd : glob_decls) (s1 : estate) (vm' : Vm.t).

  Let P e : Prop :=
    ∀ s, evm s1 =[read_e_rec s e]  vm' →
         sem_pexpr wdb gd s1 e = sem_pexpr wdb gd (with_vm s1 vm') e.

  Let Q es : Prop :=
    ∀ s, evm s1 =[read_es_rec s es] vm' →
         sem_pexprs wdb gd s1 es = sem_pexprs wdb gd (with_vm s1 vm') es.

  Lemma read_e_es_eq_on : (∀ e, P e) * (∀ es, Q es).
  Proof.
    apply: pexprs_ind_pair; split; subst P Q => //=.
    - move => e rec es ih s Heq /=.
      have Heq' : evm s1 =[read_e_rec s e] vm'.
      + apply: (eq_onI _ Heq); rewrite /= read_esE; SvD.fsetdec.
      move: rec => /(_ _ Heq') ->.
      case: (sem_pexpr _ _ _ e) => //= v.
      by move: ih => /(_ _ Heq) ->.
    - by move=> x s /get_gvar_eq_on -> //; SvD.fsetdec.
    - move=> al aa sz x e He s Heq; rewrite (He _ Heq) => {He}.
      rewrite (on_arr_gvar_eq_on (s' := with_vm s1 vm') _ _ _ Heq) ?read_eE //.
      by SvD.fsetdec.
    - move=> aa sz len x e He s Heq; rewrite (He _ Heq) => {He}.
      rewrite (on_arr_gvar_eq_on (s' := with_vm s1 vm') _ _ _ Heq) ?read_eE //.
      by SvD.fsetdec.
    - by move=> al sz x e He s Hvm; rewrite (get_var_eq_on _ _ Hvm) ?(He _ Hvm) // read_eE;SvD.fsetdec.
    - by move=> op e He s /He ->.
    - move => op e1 He1 e2 He2 s Heq; rewrite (He1 _ Heq) (He2 s) //.
      by move=> z Hin; apply Heq; rewrite read_eE; SvD.fsetdec.
    - by move => op es Hes s heq; rewrite -!/(sem_pexprs wdb gd s1) (Hes _ heq).
    move=> t e He e1 He1 e2 He2 s Heq; rewrite (He _ Heq) (He1 s) ? (He2 s) //.
    + move=> z Hin;apply Heq;rewrite !read_eE.
      by move: Hin;rewrite read_eE;SvD.fsetdec.
    move=> z Hin;apply Heq;rewrite !read_eE.
    by move: Hin;rewrite read_eE;SvD.fsetdec.
  Qed.

End READ_E_ES_EQ_ON.

Definition read_e_eq_on wdb gd s vm' s1 e :=
  (read_e_es_eq_on wdb gd s1 vm').1 e s.

Lemma read_e_eq_on_empty wdb gd vm s e :
  evm s =[ read_e_rec Sv.empty e ]  vm
  -> sem_pexpr wdb gd s e = sem_pexpr wdb gd (with_vm s vm) e.
Proof. exact: read_e_eq_on. Qed.

Definition read_es_eq_on wdb gd es s s1 vm' :=
  (read_e_es_eq_on wdb gd s1 vm').2 es s.

Lemma read_es_eq_on_empty wdb gd es s vm :
  evm s =[ read_es_rec Sv.empty es ]  vm
  -> sem_pexprs wdb gd s es = sem_pexprs wdb gd (with_vm s vm) es.
Proof. exact: read_es_eq_on. Qed.

Corollary eq_on_sem_pexpr wdb s' gd s e :
  emem s = emem s' →
  evm s =[read_e e] evm s' →
  sem_pexpr wdb gd s e = sem_pexpr wdb gd s' e.
Proof.
  move=> eq_mem /read_e_eq_on ->; rewrite (sem_pexpr_with_scs _ gd _ (escs s')).
  by case: s' eq_mem => /= > <-.
Qed.

Corollary eq_on_sem_pexprs wdb s' gd s es :
  emem s = emem s' →
  evm s =[read_es es] evm s' →
  sem_pexprs wdb gd s es = sem_pexprs wdb gd s' es.
Proof.
  move=> eq_mem /read_es_eq_on ->; rewrite (sem_pexprs_with_scs _ gd _ (escs s')).
  by case: s' eq_mem => /= > <-.
Qed.

Section UseMem.

Context (wdb : bool) (s1 s2 : estate) (heq : evm s1 = evm s2).

Lemma use_memP gd e:
  ~~use_mem e ->
  sem_pexpr wdb gd s1 e = sem_pexpr wdb gd s2 e.
Proof.
  apply (pexpr_mut_ind (P := fun e => ~~use_mem e -> sem_pexpr wdb gd s1 e = sem_pexpr wdb gd s2 e)
                      (Q := fun e => ~~has use_mem e -> sem_pexprs wdb gd s1 e = sem_pexprs wdb gd s2 e)).
  split => //= {e}.
  + by move=> e hrec es hrecs; rewrite negb_or => /andP [] /hrec -> /hrecs ->.
  + by move=> x _; rewrite heq.
  + by move=> ??? x e hrec /hrec ->; rewrite heq.
  + by move=> ??? x e hrec /hrec ->; rewrite heq.
  + by move=> ? e hrec /hrec ->.
  + by move=> ? e1 hrec1 e2 hrec2; rewrite negb_or => /andP[] /hrec1 -> /hrec2 ->.
  + by move=> ? es; rewrite /sem_pexprs => h/h->.
  by move=> ty e he e1 he1 e2 he2; rewrite !negb_or=> /andP[]/andP[] /he-> /he1-> /he2->.
Qed.

End UseMem.

Lemma use_memP_eq_on wdb gd s1 s2 e:
  ~~use_mem e ->
  evm s1 =[read_e e] evm s2 ->
  sem_pexpr wdb gd s1 e = sem_pexpr wdb gd s2 e.
Proof.
  by move=> h1 h2; rewrite (use_memP wdb (s2:= with_vm s2 (evm s1)) _ gd h1) //; apply: eq_on_sem_pexpr.
Qed.

(* FIXME this is close to write_var_spec but less specified *)
Lemma write_var_eq_on1 wdb x v s1 s2 vm1:
  write_var wdb x v s1 = ok s2 ->
  exists2 vm2 : Vm.t,
    write_var wdb x v (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    evm s2 =[Sv.singleton x] vm2.
Proof.
  rewrite /write_var;t_xrbindP => vm2 hset <-.
  have [/= -> ? /=] := set_var_eq_on1 vm1 hset; eexists; eauto.
  by rewrite !with_vm_idem.
Qed.

Lemma write_var_eq_on wdb X x v s1 s2 vm1:
  write_var wdb x v s1 = ok s2 ->
  evm s1 =[X] vm1 ->
  exists2 vm2 : Vm.t,
    write_var wdb x v (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    evm s2 =[Sv.add x X] vm2.
Proof.
  move=> /dup [] /(write_var_eq_on1 vm1) [vm2' hw2 h] hw1 hs.
  exists vm2' => //; rewrite SvP.MP.add_union_singleton.
  apply: (eq_on_union hs h); [apply: vrvP_var hw1 | apply: vrvP_var hw2].
Qed.

Lemma write_lval_eq_on1 wdb gd s1 s2 vm1 x v:
  s1.(evm) =[read_rv x] vm1 ->
  write_lval wdb gd x v s1 = ok s2 ->
  exists2 vm2,
    write_lval wdb gd x v (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    s2.(evm) =[vrv x] vm2.
Proof.
  case:x => [vi ty | x | al sz x e | al aa sz' x e | aa sz' len x e] /=.
  + by move=> _ /write_noneP [-> h1 h2]; rewrite /write_none h1 h2; exists vm1.
  + by move=> _ /(write_var_eq_on1 vm1).
  + rewrite read_eE => Hvm.
    rewrite -(get_var_eq_on wdb _ Hvm); last by SvD.fsetdec.
    rewrite (@read_e_eq_on wdb gd Sv.empty vm1 s1);first last.
    + by apply: eq_onI Hvm;rewrite read_eE;SvD.fsetdec.
    by t_xrbindP => > -> /= -> > -> /= -> ? -> ? /= -> <- /=; exists vm1.
  + rewrite read_eE=> Hvm.
    rewrite (on_arr_var_eq_on _ (s' := with_vm s1 vm1) _ Hvm); last by SvD.fsetdec.
    rewrite (@read_e_eq_on _ gd (Sv.add x Sv.empty) vm1) /=;first last.
    + by apply: eq_onI Hvm;rewrite read_eE.
    apply: on_arr_varP => n t Htx; rewrite /on_arr_var => -> /=.
    by t_xrbindP => > -> /= -> ? -> ? /= -> /= /(write_var_eq_on1 vm1).
  rewrite read_eE=> Hvm.
  rewrite (on_arr_var_eq_on _ (s' := with_vm s1 vm1) _ Hvm); last by SvD.fsetdec.
  rewrite (@read_e_eq_on _ gd (Sv.add x Sv.empty) vm1) /=;first last.
  + by apply: eq_onI Hvm;rewrite read_eE.
  apply: on_arr_varP => n t Htx; rewrite /on_arr_var => -> /=.
  by t_xrbindP => > -> /= -> > -> ? /= -> /(write_var_eq_on1 vm1).
Qed.

Lemma write_lval_eq_on wdb gd X x v s1 s2 vm1 :
  Sv.Subset (read_rv x) X ->
  write_lval wdb gd x v s1 = ok s2 ->
  evm s1 =[X] vm1 ->
  exists2 vm2 : Vm.t,
   write_lval wdb gd x v (with_vm s1 vm1) = ok (with_vm s2 vm2) &
   evm s2 =[Sv.union (vrv x) X] vm2.
Proof.
  move=> hsub hw1 heq1.
  have [vm2 hw2 heq2]:= write_lval_eq_on1 (eq_onI hsub heq1) hw1.
  exists vm2 => //; apply: (eq_on_union heq1 heq2); [apply: vrvP hw1 | apply: vrvP hw2].
Qed.

Lemma write_lvals_eq_on wdb gd X xs vs s1 s2 vm1 :
  Sv.Subset (read_rvs xs) X ->
  write_lvals wdb gd s1 xs vs = ok s2 ->
  evm s1 =[X] vm1 ->
  exists2 vm2 : Vm.t,
    write_lvals wdb gd (with_vm s1 vm1) xs vs = ok (with_vm s2 vm2) &
    evm s2 =[Sv.union (vrvs xs) X] vm2.
Proof.
  elim: xs vs X s1 s2 vm1 => [ | x xs Hrec] [ | v vs] //= X s1 s2 vm1.
  + by move=> _ [<-] ?;exists vm1.
  rewrite read_rvs_cons => Hsub.
  t_xrbindP => s1' hw hws /(write_lval_eq_on _ hw) [ |vm1' -> hvm1'] /=; first by SvD.fsetdec.
  have [ |vm2 /= -> hvm2]:= Hrec _ _ _ _ _ _ hws hvm1';first by SvD.fsetdec.
  exists vm2 => //; rewrite vrvs_cons; apply: eq_onI hvm2;SvD.fsetdec.
Qed.

(* -------------------------------------------- *)

Lemma get_gvar_uincl_at wdb x gd vm1 vm2 v1:
  (if is_lvar x then value_uincl vm1.[gv x] vm2.[gv x] else True) ->
  get_gvar wdb gd vm1 x = ok v1 ->
  exists2 v2, get_gvar wdb gd vm2 x = ok v2 & value_uincl v1 v2.
Proof.
  rewrite /get_gvar; case:ifP => _.
  + exact: get_var_uincl_at.
  by move=> ? ->;exists v1.
Qed.

Corollary get_gvar_uincl wdb x gd vm1 vm2 v1:
  vm_uincl vm1 vm2 ->
  get_gvar wdb gd vm1 x = ok v1 ->
  exists2 v2, get_gvar wdb gd vm2 x = ok v2 & value_uincl v1 v2.
Proof. by move => /(_ x.(gv)) h; apply: get_gvar_uincl_at; case: ifP. Qed.

Lemma vuincl_sem_sop2 o ve1 ve1' ve2 ve2' v1 :
  value_uincl ve1 ve1' -> value_uincl ve2 ve2' ->
  sem_sop2 o ve1 ve2 = ok v1 ->
  sem_sop2 o ve1' ve2' = ok v1.
Proof.
  rewrite /sem_sop2; t_xrbindP=> /of_value_uincl_te h1 /of_value_uincl_te h2
    + /h1{h1} ++ /h2{h2} /=.
  by case: o => /=;
    match goal with
    | |- cmp_kind -> _ => case=> /=
    | |- op_kind -> _ => case=> /=
    | _ => idtac end => > -> > -> ? /=; (move=> -> || case=> ->) => /= ->.
Qed.

Lemma vuincl_sem_sop1 o ve1 ve1' v1 :
  value_uincl ve1 ve1' -> sem_sop1 o ve1 = ok v1 ->
  sem_sop1 o ve1' = ok v1.
Proof.
  rewrite /sem_sop1; t_xrbindP=> /of_value_uincl_te h + /h{h}.
  by case: o; last case; move=> > -> /= ->.
Qed.

Lemma vuincl_sem_opN op vs v vs' :
  sem_opN op vs = ok v →
  List.Forall2 value_uincl vs vs' →
  exists2 v' : value, sem_opN op vs' = ok v' & value_uincl v v'.
Proof.
  rewrite /sem_opN.
  t_xrbindP => q ok_q <-{v} hvs.
  have -> /= := vuincl_sopn _ hvs ok_q.
  + by eauto.
  case: {q ok_q} op => //.
  by move => sz n; rewrite /= all_nseq orbT.
Qed.

(* --------------------------------------------------------- *)
Lemma sem_pexpr_uincl_on_pair wdb gd s1 vm2 :
  (∀ e v1,
      s1.(evm) <=[read_e e] vm2 →
      sem_pexpr wdb gd s1 e = ok v1 →
      exists2 v2, sem_pexpr wdb gd (with_vm s1 vm2) e = ok v2 & value_uincl v1 v2
  ) ∧ (∀ es vs1,
          s1.(evm) <=[read_es es] vm2 →
          sem_pexprs wdb gd s1 es = ok vs1 →
          exists2 vs2,
         sem_pexprs wdb gd (with_vm s1 vm2) es = ok vs2 &
           List.Forall2 value_uincl vs1 vs2
      ).
Proof.
  apply: pexprs_ind_pair; split => //=;
    rewrite /read_e /= ?read_eE ?read_eE /read_gvar.
  + by move => _ _ /ok_inj <-; exists [::].
  + move => e rec es ih vs1.
    rewrite read_es_cons => /uincl_on_union_and [] /rec{}rec /ih{ih}ih /=.
    by t_xrbindP => v /rec [] v' -> h vs /ih [] vs' -> hs <- /=; exists (v' :: vs'); eauto.
  1-3: by move => ? _ _ /ok_inj <-; eexists.
  + move => ?? Hu; apply: get_gvar_uincl_at; move: Hu; case: ifP => // _; apply; SvD.fsetdec.
  + move => al aa sz x e Hp v; rewrite read_eE => /uincl_on_union_and[] /Hp{}Hp Hu.
    apply on_arr_gvarP => n t Htx; rewrite /on_arr_var => /get_gvar_uincl_at - /(_ vm2) [].
    * by move: Hu; case: ifP => // _; apply; SvD.fsetdec.
    t_xrbindP=> ? -> /value_uinclE [? -> /WArray.uincl_get hg] > /Hp{Hp}
      [? -> ] /[swap] /to_intI -> /value_uinclE -> ? /hg{hg} /= -> /= ->.
    by eauto.
  + move => aa sz len x e Hp v; rewrite read_eE => /uincl_on_union_and[] /Hp{Hp}Hp Hu.
    apply on_arr_gvarP => n t Htx; rewrite /on_arr_var => /get_gvar_uincl_at - /(_ vm2) [].
    * by move: Hu; case: ifP => // _; apply; SvD.fsetdec.
    t_xrbindP=> ? -> /value_uinclE [? -> /WArray.uincl_get_sub h] > /Hp{Hp}
      [? -> ] /[swap] /to_intI -> /value_uinclE -> ? /h{h} /= [? -> ?] /= <-.
    by eauto.
  + move => al sz x e Hp v; rewrite read_eE => /uincl_on_union_and[] /Hp{Hp}Hp Hu.
    t_xrbindP => > /get_var_uincl_at - /(_ vm2) [].
    * by apply: Hu; SvD.fsetdec.
    move=> ? -> /[swap] /to_wordI [? [? [-> /word_uincl_truncate h]]]
      /value_uinclE [? [? [-> /h{h} /= ->]]] > /Hp[] ? ->
      /[swap] /to_wordI[? [? [-> /word_uincl_truncate h]]]
      /value_uinclE [? [? [-> /h{h} /= ->]]] ? /= -> /= ->.
    by eauto.
  + by move => op e Hp v1; rewrite read_eE => /uincl_on_union_and[] /Hp{Hp}Hp Hu; t_xrbindP =>
      ve1 /Hp [] ve1' -> /vuincl_sem_sop1 Hvu1 /Hvu1; exists v1.
  + by move => op e1 He1 e2 He2 v1 ; rewrite !read_eE => /uincl_on_union_and[] /He1{He1}He1
      /uincl_on_union_and[] /He2{He2} He2 _; t_xrbindP =>
      ? /He1 [? -> /vuincl_sem_sop2 h1] ? /He2 [? -> /h1 h2/h2]; exists v1.
  + by move => op es Hes v /Hes{}Hes; t_xrbindP => vs1 /Hes[] vs2;
    rewrite /sem_pexprs => -> /vuincl_sem_opN h{}/h.
  move => t e He e1 He1 e2 He2 v1.
  rewrite !read_eE => /uincl_on_union_and[] /He{He}He /uincl_on_union_and[]
    /He1{He1}He1 /uincl_on_union_and[] /He2{He2}He2 _; t_xrbindP => b
    > /He[? ->] /[swap] /to_boolI -> /value_uinclE -> ?
    > /He1[? ->] /value_uincl_truncate h /h{h} [? /= -> ?]
    > /He2 [? -> /value_uincl_truncate h] /h{h} [? /= -> ?] /= <-.
  by case: b; eauto.
Qed.

Lemma sem_pexpr_uincl_on wdb gd s1 vm2 e v1 :
  s1.(evm) <=[read_e e] vm2 →
  sem_pexpr wdb gd s1 e = ok v1 →
  exists2 v2, sem_pexpr wdb gd (with_vm s1 vm2) e = ok v2 & value_uincl v1 v2.
Proof. exact: (proj1 (sem_pexpr_uincl_on_pair wdb gd s1 vm2)). Qed.

Corollary sem_pexpr_uincl wdb gd s1 vm2 e v1 :
  s1.(evm) <=1 vm2 →
  sem_pexpr wdb gd s1 e = ok v1 →
  exists2 v2, sem_pexpr wdb gd (with_vm s1 vm2) e = ok v2 & value_uincl v1 v2.
Proof. move => /(vm_uincl_uincl_on (dom:=read_e e)); exact: sem_pexpr_uincl_on. Qed.

Lemma sem_pexprs_uincl_on wdb gd s1 vm2 es vs1 :
  s1.(evm) <=[read_es es] vm2 →
  sem_pexprs wdb gd s1 es = ok vs1 →
  exists2 vs2, sem_pexprs wdb gd (with_vm s1 vm2) es = ok vs2 &
              List.Forall2 value_uincl vs1 vs2.
Proof. exact: (proj2 (sem_pexpr_uincl_on_pair wdb gd s1 vm2)). Qed.

Corollary sem_pexprs_uincl wdb gd s1 vm2 es vs1 :
  s1.(evm) <=1 vm2 →
  sem_pexprs wdb gd s1 es = ok vs1 →
  exists2 vs2, sem_pexprs wdb gd (with_vm s1 vm2) es = ok vs2 &
              List.Forall2 value_uincl vs1 vs2.
Proof. move => /(vm_uincl_uincl_on (dom:=read_es es)); exact: sem_pexprs_uincl_on. Qed.

Lemma sem_pexpr_uincl_on' wdb gd s vm' vm scs m e v1 :
  vm <=[read_e_rec s e] vm' ->
  sem_pexpr wdb gd {| escs := scs; emem := m; evm := vm |} e = ok v1 ->
  exists2 v2 : value,
               sem_pexpr wdb gd {| escs := scs; emem := m; evm := vm' |} e = ok v2 & value_uincl v1 v2.
Proof.
  rewrite read_eE => /(uincl_onI (SvP.MP.union_subset_1 _)) h1 h2.
  by have /(_ _ h1) := sem_pexpr_uincl_on _ h2.
Qed.

Lemma sem_pexprs_uincl_on' wdb gd es s scs m vm vm' vs1 :
  vm <=[read_es_rec s es] vm'->
  sem_pexprs wdb gd (Estate scs m vm) es = ok vs1 ->
  exists2 vs2,sem_pexprs wdb gd (Estate scs m vm') es = ok vs2 &
              List.Forall2 value_uincl vs1 vs2.
Proof.
  rewrite read_esE => /(uincl_onI (SvP.MP.union_subset_1 _)) h1 h2.
  by have /(_ _ h1) := sem_pexprs_uincl_on _ h2.
Qed.

Lemma vuincl_exec_opn {sip : SemInstrParams asm_op syscall_state} o vs vs' v :
  List.Forall2 value_uincl vs vs' -> exec_sopn o vs = ok v ->
  exists2 v', exec_sopn o vs' = ok v' & List.Forall2  value_uincl v v'.
Proof.
  rewrite /exec_sopn /sopn_sem => vs_vs' ho.
  exact: (get_instr_desc o).(semu) vs_vs' ho.
Qed.

Lemma write_var_uincl_on wdb X (x : var_i) v1 v2 s1 s2 vm1 :
  value_uincl v1 v2 ->
  write_var wdb x v1 s1 = ok s2 ->
  evm s1 <=[X]  vm1 ->
  exists2 vm2,
    write_var wdb x v2 (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    evm s2 <=[Sv.add x X] vm2.
Proof.
  move=> hv; rewrite /write_var;t_xrbindP => vm1' hmv1' <- /= h.
  have /(_ (Sv.add x X) vm1) []:= uincl_on_set_var hv _ hmv1'.
  + by apply: uincl_onI h; SvD.fsetdec.
  by move=> -> ?; eexists; eauto.
Qed.

Lemma write_var_uincl_on1 wdb s1 s2 vm1 v1 v2 (x : var_i) :
  value_uincl v1 v2 ->
  write_var wdb x v1 s1 = ok s2 ->
  exists2 vm2 : Vm.t,
    write_var wdb x v2 (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    s2.(evm) <=[Sv.singleton x] vm2.
Proof. by move=> hv /(write_var_uincl_on hv) -/(_ Sv.empty vm1); apply. Qed.

Corollary write_var_uincl wdb s1 s2 vm1 v1 v2 (x : var_i) :
  s1.(evm) <=1 vm1 ->
  value_uincl v1 v2 ->
  write_var wdb x v1 s1 = ok s2 ->
  exists2 vm2 : Vm.t,
    write_var wdb x v2 (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    s2.(evm) <=1 vm2.
Proof.
  move => Hvm hv /dup[] hw1 /(write_var_uincl_on1 vm1 hv) {hv} [] vm2 hw2 le.
  exists vm2 => //; apply: (uincl_on_vm_uincl Hvm le); [apply: vrvP_var hw1 | apply: vrvP_var hw2].
Qed.

Lemma write_vars_uincl wdb s1 s2 vm1 vs1 vs2 xs :
  vm_uincl (evm s1) vm1 ->
  List.Forall2 value_uincl vs1 vs2 ->
  write_vars wdb xs vs1 s1 = ok s2 ->
  exists2 vm2 : Vm.t,
    write_vars wdb xs vs2 (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    vm_uincl (evm s2) vm2.
Proof.
  elim: xs s1 vm1 vs1 vs2 => /= [ | x xs Hrec] s1 vm1 vs1 vs2 Hvm [] //=.
  + by move=> [] <-;eauto.
  move=> {vs1 vs2} v1 v2 vs1 vs2 Hv Hvs;apply: rbindP => s1'.
  by move=> /(write_var_uincl Hvm Hv) []vm2 -> Hvm2 /(Hrec _ _ _ _ Hvm2 Hvs).
Qed.

Lemma uincl_write_none wdb s2 v1 v2 s s' t:
  value_uincl v1 v2 ->
  write_none wdb s t v1 = ok s' ->
  write_none wdb s2 t v2 = ok s2.
Proof.
  move=> hu /write_noneP [_ htr hdb];rewrite /write_none.
  rewrite (value_uincl_DB hu hdb).
  have [|-> //] := vm_truncate_val_uincl _ htr hu.
  move=> /eqP /eqP ? hna _ _; subst wdb.
  apply: subtype_trans (value_uincl_subtype hu).
  by apply: vm_truncate_val_subtype htr.
Qed.

Lemma write_uincl_on wdb gd s1 s2 vm1 r v1 v2:
  s1.(evm) <=[read_rv r] vm1 ->
  value_uincl v1 v2 ->
  write_lval wdb gd r v1 s1 = ok s2 ->
  exists2 vm2,
    write_lval wdb gd r v2 (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    s2.(evm) <=[vrv r] vm2.
Proof.
  case: r => [xi ty | x | al sz x p | al aa sz1 x p | aa sz1 len x p] + Hv;
    rewrite /= ?read_eE; t_xrbindP=> Hvm1.
  + move=> H; have [-> _]:= write_noneP H.
    by rewrite (uincl_write_none _ Hv H); exists vm1.
  + exact: write_var_uincl_on1.
  + move: Hvm1 => /uincl_on_union_and[] /sem_pexpr_uincl_on Hvme Hvmx >
      /get_var_uincl_at -/(_ vm1) /[swap] /to_wordI[? [? [-> /word_uincl_truncate h]]] [].
    * by apply: Hvmx; SvD.fsetdec.
    move=> vx2 -> /value_uinclE[? [? [-> /h{h} /= ->]]] > /Hvme{Hvme} [? ->]
      /[swap] /to_wordI [? [? [-> /word_uincl_truncate h]]]
      /value_uinclE[? [? [-> /h{h} /= ->]]] ? /to_wordI[? [? [? ]]].
    subst; move: Hv => /value_uinclE [? [? [-> /word_uincl_truncate h]]]
      /= /h{h} -> ? /= -> <-.
    by exists vm1.
  + move: Hvm1 => /uincl_on_union_and[] /sem_pexpr_uincl_on Hvmp Hvmx.
    apply: on_arr_varP => n a Htx /get_var_uincl_at - /(_ vm1) [].
    * by apply: Hvmx; SvD.fsetdec.
    move=> ? /[swap] /value_uinclE [? -> /WArray.uincl_set hu] ->.
    t_xrbindP=> > /Hvmp{Hvmp} [? ->]
      /[swap] /to_intI -> /value_uinclE -> ? /to_wordI [? [? [? ]]].
    subst; move: Hv => /value_uinclE[? [? [-> /word_uincl_truncate h]]] /h{h}
      /= -> ? /hu{hu} /= [? [-> ?]] /write_var_uincl_on.
    by apply => //; rewrite Htx.
  move: Hvm1 => /uincl_on_union_and[] /sem_pexpr_uincl_on Hvm1 Hvmx.
  apply: on_arr_varP => n a Htx /get_var_uincl_at - /(_ vm1) [].
  + by apply: Hvmx; SvD.fsetdec.
  move=> ? /[swap] /value_uinclE [? -> /WArray.uincl_set_sub hu] ->.
  t_xrbindP=> > /Hvm1{Hvm1} [? ->]
    /[swap] /to_intI -> /value_uinclE -> ? /to_arrI ?.
  subst; move: Hv => /value_uinclE [? ->] /= h.
  by rewrite WArray.castK /= => ? /hu -/(_ _ h){hu h} [? -> ?] /= /write_var_uincl_on; apply => //; rewrite Htx.
Qed.

Corollary write_uincl wdb gd s1 s2 vm1 r v1 v2:
  s1.(evm) <=1 vm1 ->
  value_uincl v1 v2 ->
  write_lval wdb gd r v1 s1 = ok s2 ->
  exists2 vm2,
    write_lval wdb gd r v2 (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    s2.(evm) <=1 vm2.
Proof.
  move => hvm hv ok_s2.
  case: (write_uincl_on (vm_uincl_uincl_on hvm) hv ok_s2) => vm2 ok_vm2 hvm2.
  exists vm2; first exact: ok_vm2.
  apply: (uincl_on_vm_uincl hvm hvm2);[ apply: vrvP ok_s2 | apply: vrvP ok_vm2].
Qed.

Lemma writes_uincl_on wdb gd s1 s2 vm1 r v1 v2:
  s1.(evm) <=[read_rvs r] vm1 ->
  List.Forall2 value_uincl v1 v2 ->
  write_lvals wdb gd s1 r v1 = ok s2 ->
  exists2 vm2,
    write_lvals wdb gd (with_vm s1 vm1) r v2 = ok (with_vm s2 vm2) &
    s2.(evm) <=[vrvs r] vm2.
Proof.
  elim: r v1 v2 s1 s2 vm1 => [ | r rs Hrec] ?? s1 s2 vm1 Hvm1 /= [] //=.
  + by move=> [<-]; exists vm1.
  move: Hvm1; rewrite read_rvs_cons => /uincl_on_union_and[] hr hrs.
  move=> v1 v2 vs1 vs2 Hv Hforall.
  apply: rbindP => z ok_z ok_s2.
  have [ vm2 ok_vm2 Hvm2 ] := write_uincl_on hr Hv ok_z.
  have h : evm z <=[read_rvs rs] vm2.
  + move => x hx.
    case: (Sv_memP x (vrv r)); first exact: Hvm2.
    move => hxr; rewrite -(vrvP ok_z hxr) -(vrvP ok_vm2 hxr).
    exact: hrs.
  have [ vm3 ok_vm3 h3 ] := Hrec _ _ _ _ vm2 h Hforall ok_s2.
  exists vm3; first by rewrite ok_vm2.
  rewrite vrvs_cons uincl_on_union_and; split; last exact: h3.
  move => x hx.
  case: (Sv_memP x (vrvs rs)); first exact: h3.
  move => hxrs; rewrite -(vrvsP ok_vm3 hxrs) -(vrvsP ok_s2 hxrs).
  exact: Hvm2.
Qed.

Corollary writes_uincl wdb gd s1 s2 vm1 r v1 v2:
  s1.(evm) <=1 vm1 ->
  List.Forall2 value_uincl v1 v2 ->
  write_lvals wdb gd s1 r v1 = ok s2 ->
  exists2 vm2,
    write_lvals wdb gd (with_vm s1 vm1) r v2 = ok (with_vm s2 vm2) &
    s2.(evm) <=1 vm2.
Proof.
  move => hvm hv ok_s2.
  case: (writes_uincl_on (vm_uincl_uincl_on hvm) hv ok_s2) => vm2 ok_vm2 hvm2.
  exists vm2; first exact: ok_vm2.
  apply: (uincl_on_vm_uincl hvm hvm2); [apply: vrvsP ok_s2 | apply: vrvsP ok_vm2].
Qed.

Lemma write_vars_lvals wdb gd xs vs s1:
  write_vars wdb xs vs s1 = write_lvals wdb gd s1 [seq Lvar i | i <- xs] vs.
Proof.
  rewrite /write_vars /write_lvals.
  elim: xs vs s1 => [ | x xs Hrec] [ | v vs] //= s1.
  by case: write_var => //=.
Qed.

Lemma sem_pexprs_get_var wdb gd s xs :
  sem_pexprs wdb gd s [seq Pvar (mk_lvar i) | i <- xs] =
  get_var_is wdb (evm s) xs.
Proof.
  rewrite /sem_pexprs;elim: xs=> //= x xs Hrec.
  rewrite /get_gvar /=.
  by case: get_var => //= v;rewrite Hrec.
Qed.

Lemma get_var_is_uincl_on wdb dom (xs: seq var_i) vm1 vm2 vs1:
  vm1 <=[dom] vm2 ->
  (∀ x, List.In x xs → Sv.mem x dom) →
  get_var_is wdb vm1 xs = ok vs1 ->
  exists2 vs2,
    get_var_is wdb vm2 xs = ok vs2 & List.Forall2 value_uincl vs1 vs2.
Proof.
  move => hvm; elim: xs vs1 => [ | x xs Hrec] /= ? hdom.
  + by move=> [<-]; exists [::].
  apply: rbindP => v1 /get_var_uincl_at - /(_ vm2) [ | v2 -> ? ].
  + by apply: hvm; rewrite -Sv.mem_spec; apply: hdom; left.
  apply: rbindP => vs1 /Hrec{Hrec}ih [<-] /=.
  case: ih.
  + by move => y hy; apply: hdom; right.
  move => vs2 -> ih; exists (v2 :: vs2); first reflexivity.
  by constructor.
Qed.

Lemma get_var_is_uincl wdb xs vm1 vm2 vs1 :
  vm1 <=1 vm2 ->
  get_var_is wdb vm1 xs = ok vs1 ->
  exists2 vs2,
    get_var_is wdb vm2 xs = ok vs2
    & List.Forall2 value_uincl vs1 vs2.
Proof.
  move => hvm; apply: (get_var_is_uincl_on (dom := sv_of_list v_var xs)).
  + exact: vm_uincl_uincl_on hvm.
  move => /= y hy; rewrite sv_of_listE; apply/in_map.
  by exists y.
Qed.

Lemma get_vars_uincl wdb xs vm1 vm2 vs1 :
  vm1 <=1 vm2 ->
  get_vars wdb vm1 xs = ok vs1 ->
  exists2 vs2,
    get_vars wdb vm2 xs = ok vs2
    & List.Forall2 value_uincl vs1 vs2.
Proof.
  move=> /(get_var_is_uincl (wdb := wdb) (xs := map mk_var_i xs)).
  rewrite /get_var_is !mapM_map.
  exact.
Qed.

Lemma write_lval_uincl_on wdb gd X x v1 v2 s1 s2 vm1 :
  Sv.Subset (read_rv x) X ->
  value_uincl v1 v2 ->
  write_lval wdb gd x v1 s1 = ok s2 ->
  evm s1 <=[X]  vm1 ->
  exists2 vm2 : Vm.t,evm s2 <=[Sv.union (vrv x) X]  vm2 &
                     write_lval wdb gd x v2 (with_vm s1 vm1) = ok (with_vm s2 vm2).
Proof.
  move=> hX hvu hw hu.
  have [vm2 hw2 hu2] := write_uincl_on (uincl_onI hX hu) hvu hw.
  exists vm2 => //; apply: (uincl_on_union hu hu2); [ apply: vrvP hw | apply: vrvP hw2].
Qed.

Lemma write_lvals_uincl_on wdb gd X x v1 v2 s1 s2 vm1 :
  Sv.Subset (read_rvs x) X ->
  List.Forall2 value_uincl v1 v2 ->
  write_lvals wdb gd s1 x v1 = ok s2 ->
  evm s1 <=[X]  vm1 ->
  exists2 vm2 : Vm.t,evm s2 <=[Sv.union (vrvs x) X]  vm2 &
                     write_lvals wdb gd (with_vm s1 vm1) x v2 = ok (with_vm s2 vm2).
Proof.
  move=> hX hvu hw hu.
  have [vm2 hw2 hu2] := writes_uincl_on (uincl_onI hX hu) hvu hw.
  exists vm2 => //; apply: (uincl_on_union hu hu2); [ apply: vrvsP hw | apply: vrvsP hw2].
Qed.

Lemma write_lval_undef gd l v s1 s2 sz :
  write_lval true gd l v s1 = ok s2 ->
  type_of_val v = sword sz ->
  exists w: word sz, v = Vword w.
Proof.
  move=> Hw Ht.
  rewrite /type_of_val in Ht.
  case: v Ht Hw=> //=.
  + move=> sz' w [<-] _; by exists w.
  case => //= ?? [<-] /=.
  case: l => /=.
  + by move => _ ? /write_noneP [].
  + by rewrite /write_var; t_xrbindP => > /set_varP [].
  + by t_xrbindP.
  + by move => al aa ws [] [vt vn] /= _ e; apply: on_arr_varP => n t hty /= ?; t_xrbindP.
  by move => aa ws len [] [vt vn] /= _ e; apply: on_arr_varP => n t hty /= ?; t_xrbindP.
Qed.

(* MOVE THIS *)
Section Expr.

Context (wdb : bool) (gd : glob_decls) (s : estate).

Let P e : Prop :=
  forall v, sem_pexpr true gd s e = ok v -> sem_pexpr wdb gd s e = ok v.

Let Q es : Prop :=
  forall vs, sem_pexprs true gd s es = ok vs -> sem_pexprs wdb gd s es = ok vs.

Lemma get_var_wdb vm x v : get_var true vm x = ok v -> get_var wdb vm x = ok v.
Proof. by move=> /get_varP [-> h1 h2]; rewrite /get_var; case: wdb => //; rewrite h1. Qed.

Lemma get_gvar_wdb vm x v : get_gvar true gd vm x = ok v -> get_gvar wdb gd vm x = ok v.
Proof. rewrite /get_gvar; case: ifP => // _; apply get_var_wdb. Qed.

Lemma sem_pexpr_wdb_and : (forall e, P e) /\ (forall es, Q es).
Proof.
  apply: pexprs_ind_pair; subst P Q; split => //=.
  + by move=> e he es hes vs; t_xrbindP => ? /he -> ? /hes -> <-.
  + by move=> x v; apply get_gvar_wdb.
  + move=> al aa ws x e he v; apply on_arr_gvarP; t_xrbindP; rewrite /on_arr_var.
    by move=> len a ha /get_gvar_wdb -> ?? /he -> /= -> ? /= -> <-.
  + move=> aa ws len x e he v; apply on_arr_gvarP; t_xrbindP; rewrite /on_arr_var.
    by move=> ??? /get_gvar_wdb -> ?? /he -> /= -> ? /= -> <-.
  + by t_xrbindP => > he > /get_var_wdb -> /= -> > /he -> /= -> /= > -> <-.
  + by t_xrbindP => > he > /he -> /= ->.
  + by t_xrbindP => > he1 > he2 > /he1 -> > /he2 -> /= ->.
  + by t_xrbindP => > hes > /hes; rewrite -/(sem_pexprs _ _ _) => -> /= <-.
  by t_xrbindP => > he > he1 > he2 > /he -> /= -> > /he1 -> /= -> > /he2 -> /= -> <-.
Qed.

Lemma sem_pexpr_wdb e : P e.
Proof. by case: sem_pexpr_wdb_and. Qed.

Lemma sem_pexprs_wdb e : Q e.
Proof. by case: sem_pexpr_wdb_and. Qed.

Lemma sem_pexpr_ext_eq e vm :
  (evm s =1 vm)%vm ->
  sem_pexpr wdb gd s e = sem_pexpr wdb gd (with_vm s vm) e.
Proof. by move=> heq; apply/read_e_eq_on_empty/vm_eq_eq_on. Qed.

Lemma sem_pexprs_ext_eq es vm :
  (evm s =1 vm)%vm ->
  sem_pexprs wdb gd s es = sem_pexprs wdb gd (with_vm s vm) es.
Proof. by move=> heq; apply/read_es_eq_on_empty/vm_eq_eq_on. Qed.

Lemma write_lvar_ext_eq x v s1 s2 vm1 :
  (evm s1 =1 vm1)%vm ->
  write_lval wdb gd x v s1 = ok s2 ->
  exists2 vm2, evm s2 =1 vm2 & write_lval wdb gd x v (with_vm s1 vm1) = ok (with_vm s2 vm2).
Proof.
  move=> he hw.
  have hsub : Sv.Subset (read_rv x) (read_rv x) by SvD.fsetdec.
  have heq : evm s1 =[read_rv x]  vm1 by move=> ??;rewrite he.
  have [vm2 hw2 heq2]:= write_lval_eq_on hsub hw heq.
  exists vm2 => //.
  apply: (eq_on_eq_vm (d:=vrv x) he).
  + by apply: eq_onI heq2; SvD.fsetdec.
  + by apply: vrvP hw.
  by apply: vrvP hw2.
Qed.

Lemma write_lvars_ext_eq xs vs s1 s2 vm1 :
  (evm s1 =1 vm1)%vm ->
  write_lvals wdb gd s1 xs vs = ok s2 ->
  exists2 vm2, evm s2 =1 vm2 & write_lvals wdb gd (with_vm s1 vm1) xs vs = ok (with_vm s2 vm2).
Proof.
  move=> he hw.
  have hsub : Sv.Subset (read_rvs xs) (read_rvs xs) by SvD.fsetdec.
  have heq : evm s1 =[read_rvs xs]  vm1 by move=> ??;rewrite he.
  have [vm2 hw2 heq2]:= write_lvals_eq_on hsub hw heq.
  exists vm2 => //.
  apply: (eq_on_eq_vm (d:=vrvs xs) he).
  + by apply: eq_onI heq2; SvD.fsetdec.
  + by apply: vrvsP hw.
  by apply: vrvsP hw2.
Qed.

End Expr.


Section Sem_eqv.
Context
  {dc:DirectCall}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {sCP : semCallParams}
  (p:prog) (ev : extra_val_t).

Let Pc s1 c s2 :=
  forall vm1 X,
    Sv.Subset (read_c c) X ->
    evm s1 =[X] vm1 ->
    exists2 vm2, sem p ev (with_vm s1 vm1) c (with_vm s2 vm2) & evm s2 =[X] vm2.

Let Pi s1 (i:instr) s2 :=
  forall vm1 X,
    Sv.Subset (read_I i) X ->
    evm s1 =[X] vm1 ->
    exists2 vm2, sem_I p ev (with_vm s1 vm1) i (with_vm s2 vm2) & evm s2 =[X] vm2.

Let Pi_r s1 (i:instr_r) s2 :=
  forall vm1 X,
    Sv.Subset (read_i i) X ->
    evm s1 =[X] vm1 ->
    exists2 vm2, sem_i p ev (with_vm s1 vm1) i (with_vm s2 vm2) & evm s2 =[X] vm2.

Let Pfor (i:var_i) zs s1 c s2 :=
  forall vm1 X,
    Sv.Subset (read_c c) X ->
      evm s1 =[X] vm1 ->
      exists2 vm2, sem_for p ev i zs (with_vm s1 vm1) c (with_vm s2 vm2) & evm s2 =[X] vm2.

Let Pfun (scs:syscall_state) (m:mem) (fn:funname) (args: values) (scs':syscall_state) (m':mem) (res:values) := true.

Lemma read_cP X s1 c s2 vm1 :
  sem p ev s1 c s2 ->
  Sv.Subset (read_c c) X ->
  evm s1 =[X] vm1 ->
  exists2 vm2, sem p ev (with_vm s1 vm1) c (with_vm s2 vm2) & evm s2 =[X] vm2.
Proof.
  move=> hsem;move: hsem vm1 X.
  apply : (sem_Ind (Pc := Pc) (Pi := Pi) (Pi_r := Pi_r) (Pfor := Pfor) (Pfun := Pfun)) => {s1 c s2}.
  + by move=> s vm1 X hsub heq; exists vm1 => //;constructor.
  + move=> s1 s2 s3 i c _ ihi _ ihc vm1 X; rewrite read_c_cons => hsub heq1.
    have [|vm2 hi heq2] := ihi vm1 X _ heq1; first by SvD.fsetdec.
    have [|vm3 hc heq3] := ihc vm2 X _ heq2; first by SvD.fsetdec.
    by exists vm3 => //; econstructor; eauto.
  + move=> ii i s1 s2 _ ih vm1 X; rewrite read_Ii => hsub heq1.
    by case: (ih vm1 X hsub heq1) => vm2 ??;exists vm2.
  + move=> s1 s2 x t ty e v v' he htr hw vm1 X.
    rewrite read_i_assgn => hsub heq1.
    have [|vm2 ? heq2] := write_lval_eq_on _ hw heq1; first by SvD.fsetdec.
    exists vm2.
    + econstructor; eauto.
      rewrite -read_e_eq_on_empty //.
      by rewrite read_eE => z hz; apply heq1; SvD.fsetdec.
    by move=> z hz;apply heq2; SvD.fsetdec.
  + move=> s1 s2 t o xs es.
    rewrite /sem_sopn; t_xrbindP => vargs vres hes hex hw vm1 X.
    rewrite read_i_opn => hsub heq1.
    have [|vm2 hw2 heq2] := write_lvals_eq_on _ hw heq1; first by SvD.fsetdec.
    exists vm2; last by apply: eq_onI heq2; SvD.fsetdec.
    econstructor; eauto.
    rewrite /sem_sopn -(read_es_eq_on _ _ (s := X)) //; last first.
    + by move=> z;rewrite read_esE => hz;apply heq1; SvD.fsetdec.
    by rewrite hes /= hex /= hw2.
  + move=> s1 scs m s2 o xs es ves vs hes ho hw vm1 X.
    rewrite read_i_syscall => hsub heq1.
    have [|vm2 hw2 heq2] := write_lvals_eq_on _ hw heq1; first by SvD.fsetdec.
    exists vm2 => //; last by apply: eq_onI heq2; SvD.fsetdec.
    econstructor; eauto.
    rewrite -(read_es_eq_on _ _ (s := X)) //.
    by move=> z;rewrite read_esE => hz;apply heq1; SvD.fsetdec.
  + move=> s1 s2 e c1 c2 he _ ih vm1 X.
    rewrite read_i_if => hsub heq1.
    have [|vm2 hs2 heq2] := ih vm1 X _ heq1; first SvD.fsetdec.
    exists vm2 => //; apply Eif_true => //.
    rewrite -read_e_eq_on_empty //.
    by rewrite read_eE; apply: eq_onI heq1; SvD.fsetdec.
  + move=> s1 s2 e c1 c2 he _ ih vm1 X.
    rewrite read_i_if => hsub heq1.
    have [|vm2 hs2 heq2]:= ih vm1 X _ heq1; first SvD.fsetdec.
    exists vm2 => //; apply Eif_false => //.
    rewrite -read_e_eq_on_empty //.
    by rewrite read_eE; apply: eq_onI heq1; SvD.fsetdec.
  + move=> s1 s2 s3 s4 a c1 e c2 _ ih1 he _ ih2 _ ihw vm1 X.
    rewrite read_i_while => hsub heq1.
    have [|vm2 hs1 heq2] := ih1 vm1 X _ heq1; first SvD.fsetdec.
    have [|vm3 hs2 heq3] := ih2 vm2 X _ heq2; first SvD.fsetdec.
    have [|vm4 hs3 heq4] := ihw vm3 X _ heq3; first by rewrite read_i_while.
    exists vm4 => //; apply: Ewhile_true; eauto.
    rewrite -read_e_eq_on_empty //.
    by rewrite read_eE; apply: eq_onI heq2; SvD.fsetdec.
  + move=> s1 s2 a c1 e c2 _ ih1 he vm1 X.
    rewrite read_i_while => hsub heq1.
    have [|vm2 hs1 heq2]:= ih1 vm1 X _ heq1; first SvD.fsetdec.
    exists vm2 => //; apply: Ewhile_false; eauto.
    rewrite -read_e_eq_on_empty //.
    by rewrite read_eE; apply: eq_onI heq2; SvD.fsetdec.
  + move=> s1 s2 i d lo hi c vlo vhi hlo hhi _ ih vm1 X.
    rewrite read_i_for => hsub heq1.
    have [|vm2 ? heq2]:= ih vm1 X _ heq1; first by SvD.fsetdec.
    exists vm2 => //.
    by econstructor;
      eauto;
      rewrite -read_e_eq_on_empty // read_eE;
      apply: eq_onI heq1; SvD.fsetdec.
  + by move=> s1 i c vm1 X hsub heq1; exists vm1 => //;constructor.
  + move=> s1 s2 s3 s4 i z zs c hwi _ ihc _ ihf vm1 X hsub heq1.
    have [vm2 hw2 heq2] := write_var_eq_on hwi heq1.
    have [|vm3 ? heq3] := ihc vm2 X hsub; first by apply: eq_onI heq2; SvD.fsetdec.
    have [vm4 ? heq4] := ihf vm3 X hsub heq3; exists vm4 => //.
    by econstructor; eauto.
  + move=> s1 scs2 m2 s2 xs fn args vargs vs hargs hcall _ hw vm1 X.
    rewrite read_i_call => hsub heq1.
    case: (write_lvals_eq_on _ hw heq1); first by SvD.fsetdec.
    move=> vm2 hw2 heq2; exists vm2; last by apply: eq_onI heq2; SvD.fsetdec.
    econstructor; eauto.
    by rewrite -(read_es_eq_on _ _ (s := X)) // read_esE;
      apply: eq_onI heq1;
      SvD.fsetdec.
  done.
Qed.

Lemma sem_vm_eq s1 c s2 vm1:
  sem p ev s1 c s2 ->
  (evm s1 =1 vm1)%vm ->
  exists2 vm2, sem p ev (with_vm s1 vm1) c (with_vm s2 vm2) & evm s2 =1 vm2.
Proof.
  move=> hsem heq1.
  case: (read_cP (vm1 := vm1) (X:= Sv.union (read_c c) (write_c c)) hsem).
  + by SvD.fsetdec.
  + by move=> x hx;apply heq1.
  move=> vm2 hsem2 heq2; exists vm2 => //.
  move=> x; case: (Sv_memP x (write_c c)) => hx.
  + by apply heq2; SvD.fsetdec.
  rewrite -(writeP hsem) // heq1 //.
  by have := writeP hsem2; rewrite !evm_with_vm => ->.
Qed.

End Sem_eqv.

(* ---------------------------------------------------------------- *)
Section UNDEFINCL.

Context
  {dc:DirectCall}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {sCP : semCallParams}.
Variable p : prog.
Variable ev : extra_val_t.

Notation gd:= (p_globs p).

Let Pc s1 c s2 :=
  forall vm1 ,
    evm s1 <=1 vm1 ->
    exists vm2,
      sem p ev (with_vm s1 vm1) c (with_vm s2 vm2) /\
      evm s2 <=1 vm2.

Let Pi_r s1 i s2 :=
  forall vm1,
    evm s1 <=1 vm1 ->
    exists vm2,
      sem_i p ev (with_vm s1 vm1) i (with_vm s2 vm2) /\
      evm s2 <=1 vm2.

Let Pi s1 i s2 :=
  forall vm1,
    evm s1 <=1 vm1 ->
    exists vm2,
      sem_I p ev (with_vm s1 vm1) i (with_vm s2 vm2) /\
      evm s2 <=1 vm2.

Let Pfor (i:var_i) zs s1 c s2 :=
  forall vm1,
    evm s1 <=1 vm1 ->
    exists vm2,
      sem_for p ev i zs (with_vm s1 vm1) c (with_vm s2 vm2) /\
      evm s2 <=1 vm2.

Let Pfun scs1 m1 fd vargs scs2 m2 vres :=
  forall vargs',
    List.Forall2 value_uincl vargs vargs' ->
    exists vres',
      sem_call p ev scs1 m1 fd vargs' scs2 m2 vres' /\
      List.Forall2 value_uincl vres vres'.

Local Lemma Hnil : sem_Ind_nil Pc.
Proof. by move=> s vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ Hi _ Hc vm1 /Hi [vm2 []] Hsi /Hc [vm3 []] Hsc ?.
  by exists vm3;split=>//;econstructor;eauto.
Qed.

Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Proof. by move=> ii i s1 s2 _ Hi vm1 /Hi [vm2 []] Hsi ?;exists vm2. Qed.

Local Lemma Hasgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s1 s2 x tag ty e v v' hsem hty hwr vm1 Hvm1.
  have [w hsem' hle]:= sem_pexpr_uincl Hvm1 hsem.
  have [w'' hty' hle'] := value_uincl_truncate hle hty.
  have  [vm2 Hw ?]:= write_uincl Hvm1 hle' hwr;exists vm2;split=> //.
  by econstructor;first exact hsem'; eauto.
Qed.

Local Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move=> s1 s2 t o xs es H vm1 Hvm1; apply: rbindP H => rs;apply: rbindP => vs.
  move=> /(sem_pexprs_uincl Hvm1) [] vs' H1 H2.
  move=> /(vuincl_exec_opn H2) [] rs' H3 H4.
  move=> /(writes_uincl Hvm1 H4) [] vm2 ??.
  exists vm2;split => //;constructor.
  by rewrite /sem_sopn H1 /= H3.
Qed.

Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
Proof.
  move=> s1 scs m s2 xs o es ves vs hes hex hw vm1 hvm1.
  have [ves' hes' hle] := sem_pexprs_uincl hvm1 hes.
  have [vs' hex' hle']:= exec_syscallP hex hle.
  have  [vm2 Hw ?]:= writes_uincl (s1 := with_scs (with_mem s1 m) scs) hvm1 hle' hw.
  exists vm2;split=> //; econstructor; eauto.
Qed.

Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 H _ Hc vm1 Hvm1.
  have [v' H1 /value_uinclE ?]:= sem_pexpr_uincl Hvm1 H;subst v'.
  have [vm2 [??]]:= Hc _ Hvm1;exists vm2;split=>//.
  by apply Eif_true;rewrite // H1.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 H _ Hc vm1 Hvm1.
  have [v' H1 /value_uinclE ?]:= sem_pexpr_uincl Hvm1 H;subst v'.
  have [vm2 [??]]:= Hc _ Hvm1;exists vm2;split=>//.
  by apply Eif_false;rewrite // H1.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 s3 s4 a c e c' _ Hc H _ Hc' _ Hw vm1 Hvm1.
  have [vm2 [Hs2 Hvm2]] := Hc _ Hvm1.
  have [v' H1 /value_uinclE ?]:= sem_pexpr_uincl Hvm2 H;subst.
  have [vm3 [H4 /Hw [vm4] [??]]]:= Hc' _ Hvm2;exists vm4;split => //.
  by eapply Ewhile_true;eauto;rewrite H1.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 a c e c' _ Hc H vm1 Hvm1.
  have [vm2 [Hs2 Hvm2]] := Hc _ Hvm1.
  have [v' H1 /value_uinclE ?]:= sem_pexpr_uincl Hvm2 H;subst.
  by exists vm2;split=> //;apply: Ewhile_false=> //;rewrite H1.
Qed.

Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Proof.
  move=> s1 s2 i d lo hi c vlo vhi H H' _ Hfor vm1 Hvm1.
  have [? H1 /value_uinclE ?]:= sem_pexpr_uincl Hvm1 H;subst.
  have [? H3 /value_uinclE ?]:= sem_pexpr_uincl Hvm1 H';subst.
  have [vm2 []??]:= Hfor _ Hvm1; exists vm2;split=>//.
  by econstructor;eauto;rewrite ?H1 ?H3.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof. by move=> s i c vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  move=> s1 s1' s2 s3 i w ws c Hi _ Hc _ Hf vm1 Hvm1.
  have [vm1' Hi' /Hc] := write_var_uincl Hvm1 (value_uincl_refl _) Hi.
  move=> [vm2 [Hsc /Hf]] [vm3 [Hsf Hvm3]];exists vm3;split => //.
  by econstructor;eauto.
Qed.

Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
Proof.
  move=> s1 scs2 m2 s2 xs fn args vargs vs Hargs Hcall Hfd Hxs vm1 Hvm1.
  have [vargs' Hsa /Hfd [vs' [Hc Hvres]]]:= sem_pexprs_uincl Hvm1 Hargs.
  have Hvm1' : vm_uincl (evm (with_scs (with_mem s1 m2) scs2)) vm1 by done.
  have [vm2' ??] := writes_uincl Hvm1' Hvres Hxs.
  exists vm2';split=>//.
  econstructor;eauto.
Qed.

Lemma all2_check_ty_val v1 x v2 :
  all2 check_ty_val x v1 → List.Forall2 value_uincl v1 v2 → all2 check_ty_val x v2.
Proof.
  move=> /all2P H1 H2;apply /all2P;apply: Forall2_trans H1 H2;apply check_ty_val_uincl.
Qed.

Lemma mapM2_id tyin vargs vargs' :
  mapM2 ErrType (λ (_ : stype) (v : value), ok v) tyin vargs = ok vargs' ->
  vargs = vargs'.
Proof.
  elim: tyin vargs vargs' => /= [ | ty tyin hrec] [ | v vs] // >.
  + by move=> [].
  by t_xrbindP => > /hrec -> <-.
Qed.

Lemma dc_truncate_value_uincl t v1 v2 : dc_truncate_val t v1 = ok v2 → value_uincl v2 v1.
Proof.
  rewrite /dc_truncate_val; case: ifP => [_ [<-] // | _].
  apply truncate_value_uincl.
Qed.

Lemma mapM2_dc_truncate_value_uincl tyin vargs vargs' :
  mapM2 ErrType dc_truncate_val tyin vargs = ok vargs' → List.Forall2 value_uincl vargs' vargs.
Proof.
  rewrite /dc_truncate_val; case: direct_call; last by apply mapM2_truncate_value_uincl.
  by move=> /mapM2_id ->; apply List_Forall2_refl.
Qed.

Lemma mapM2_dc_truncate_val tys vs1' vs1 vs2' :
  mapM2 ErrType dc_truncate_val tys vs1' = ok vs1 →
  List.Forall2 value_uincl vs1' vs2' →
  exists2 vs2 : seq value,
    mapM2 ErrType dc_truncate_val tys vs2' = ok vs2 & List.Forall2 value_uincl vs1 vs2.
Proof.
  rewrite /dc_truncate_val; case: direct_call; last by apply mapM2_truncate_val.
  move=> h1 h2; elim: h2 tys vs1 h1 => {vs1' vs2'} [ | v1 v2 vs1' vs2' hu hus hrec] [] //=.
  + by move=> ? [<-]; exists [::].
  t_xrbindP => _ tys ?? /hrec [vs2 -> hall] <- /=; eexists; eauto.
Qed.

Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
Proof.
  move=> scs1 m1 scs2 m2 fn fd vargs vargs' s0 s1 s2 vres vres' Hget Hca hi Hargs Hsem Hrec Hmap Hcr hscs Hfi vargs1' Uargs.
  have [vargs2' hm2 Uargs']:= mapM2_dc_truncate_val Hca Uargs.
  have := write_vars_uincl (vm_uincl_refl _) Uargs' Hargs.
  rewrite with_vm_same => -[vm1 Hargs' Hvm1].
  have [vm2' /= [] Hsem' Uvm2]:= Hrec _ Hvm1.
  have [vs2 Hvs2 Hsub] := get_var_is_uincl Uvm2 Hmap.
  have [vres2' hmr2 Ures']:= mapM2_dc_truncate_val Hcr Hsub.
  by exists vres2';split=>//;econstructor;eauto.
Qed.

Lemma sem_call_uincl vargs scs1 m1 f scs2 m2 vres vargs':
  List.Forall2 value_uincl vargs vargs' ->
  sem_call p ev scs1 m1 f vargs scs2 m2 vres ->
  exists vres', sem_call p ev scs1 m1 f vargs' scs2 m2 vres' /\ List.Forall2 value_uincl vres vres'.
Proof.
  move=> H1 H2.
  exact:
    (sem_call_Ind
       Hnil
       Hcons
       HmkI
       Hasgn
       Hopn
       Hsyscall
       Hif_true
       Hif_false
       Hwhile_true
       Hwhile_false
       Hfor
       Hfor_nil
       Hfor_cons
       Hcall
       Hproc
       H2
       _
       H1).
Qed.

Lemma sem_i_uincl s1 i s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem_i p ev s1 i s2 ->
  exists vm2,
    sem_i p ev (with_vm s1 vm1) i (with_vm s2 vm2) /\
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  exact:
    (sem_i_Ind
       Hnil
       Hcons
       HmkI
       Hasgn
       Hopn
       Hsyscall
       Hif_true
       Hif_false
       Hwhile_true
       Hwhile_false
       Hfor
       Hfor_nil
       Hfor_cons
       Hcall
       Hproc
       H2
       _
       H1).
Qed.

Lemma sem_I_uincl s1 i s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem_I p ev s1 i s2 ->
  exists vm2,
    sem_I p ev (with_vm s1 vm1) i (with_vm s2 vm2) /\
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  exact:
    (sem_I_Ind
       Hnil
       Hcons
       HmkI
       Hasgn
       Hopn
       Hsyscall
       Hif_true
       Hif_false
       Hwhile_true
       Hwhile_false
       Hfor
       Hfor_nil
       Hfor_cons
       Hcall
       Hproc
       H2
       _
       H1).
Qed.

Lemma sem_uincl s1 c s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem p ev s1 c s2 ->
  exists vm2,
    sem p ev (with_vm s1 vm1) c (with_vm s2 vm2) /\
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  exact:
    (sem_Ind
       Hnil
       Hcons
       HmkI
       Hasgn
       Hopn
       Hsyscall
       Hif_true
       Hif_false
       Hwhile_true
       Hwhile_false
       Hfor
       Hfor_nil
       Hfor_cons
       Hcall
       Hproc
       H2
       _
       H1).
Qed.

End UNDEFINCL.

Lemma eq_gvarP wdb gd vm x x' : eq_gvar x x' → get_gvar wdb gd vm x = get_gvar wdb gd vm x'.
Proof. by rewrite /eq_gvar /get_gvar /is_lvar => /andP [] /eqP -> /eqP ->. Qed.

Lemma eq_exprP_pair wdb gd s :
  (∀ e e', eq_expr e e' → sem_pexpr wdb gd s e = sem_pexpr wdb gd s e') ∧
  (∀ es es', all2 eq_expr es es' → sem_pexprs wdb gd s es = sem_pexprs wdb gd s es').
Proof.
  apply: pexprs_ind_pair; split =>
    [| e he es hes |?|?|?|?|????? He|????? He|???? He|?? He|?? He1 ? He2|?? hes|?? He ? He1 ? He2] [] //=.
  - by move => e' es' /andP[] /he -> /hes ->.
  1-3: by move => ? /eqP ->.
  - exact: eq_gvarP.
  1-2: by move=> > /andP[] /andP[] /andP []/andP [] /eqP-> /eqP-> /eqP -> /eq_gvarP -> /He ->.
  - by move=> > /andP[] /andP[] /andP [] /eqP-> /eqP-> /eqP -> /He ->.
  - by move=> > /andP[]/eqP -> /He ->.
  - by move=> > /andP[]/andP[] /eqP -> /He1 -> /He2 ->.
  - by rewrite -/(sem_pexprs _ _ _) => > /andP[]/eqP-> /hes ->.
  by move=> > /andP[]/andP[]/andP[] /eqP -> /He -> /He1 -> /He2 ->.
Qed.

Lemma eq_exprP wdb gd s e1 e2 : eq_expr e1 e2 -> sem_pexpr wdb gd s e1 = sem_pexpr wdb gd s e2.
Proof. exact: (proj1 (eq_exprP_pair wdb gd s)). Qed.

Lemma eq_exprsP wdb gd m es1 es2:
  all2 eq_expr es1 es2 → sem_pexprs wdb gd m es1 = sem_pexprs wdb gd m es2.
Proof. exact: (proj2 (eq_exprP_pair wdb gd m)). Qed.

Lemma get_var_undef vm x v ty h :
  get_var true vm x = ok v -> v <> Vundef ty h.
Proof. by move=> /get_var_compat [] * ?; subst. Qed.

Lemma get_gvar_undef gd vm x v ty h :
  get_gvar true gd vm x = ok v -> v <> Vundef ty h.
Proof.
  rewrite /get_gvar; case: is_lvar; first by apply get_var_undef.
  move=> /get_globalI [gv [_ -> _]].
  by case: gv.
Qed.

Lemma get_var_is_allow_undefined vm xs :
  get_var_is false vm xs = ok [seq vm.[v_var x] | x <- xs ].
Proof. by elim: xs => //= ?? ->. Qed.

(* ------------------------------------------------------------------------------ *)

Section SEM_CALL_PARAMS.

Context
  {sip : SemInstrParams asm_op syscall_state}.

(* ** Semantic without stack
 * -------------------------------------------------------------------- *)

#[ global ]
Instance sCP_unit : semCallParams (pT := progUnit) :=
  { init_state := fun _ _ _ s => ok s;
    finalize   := fun _ m => m;
    exec_syscall  := exec_syscall_u;
    exec_syscallP := exec_syscallPu;
    exec_syscallS := exec_syscallSu;
}.

(* ** Semantic with stack
 * -------------------------------------------------------------------- *)

Definition init_stk_state (sf : stk_fun_extra) (pe:sprog_extra) (wrip:pointer) (s:estate) :=
  let scs1 := s.(escs) in
  let m1   := s.(emem) in
  let vm1  := s.(evm) in
  Let m1' := alloc_stack m1 sf.(sf_align) sf.(sf_stk_sz) sf.(sf_stk_ioff) sf.(sf_stk_extra_sz) in
  write_vars true [:: vid pe.(sp_rsp) ; vid pe.(sp_rip)]
             [:: Vword (top_stack m1'); Vword wrip] (Estate scs1 m1' Vm.init).

Definition finalize_stk_mem (sf : stk_fun_extra) (m:mem) :=
  free_stack m.

#[ global ]
Instance sCP_stack : semCallParams (pT := progStack) :=
  { init_state := init_stk_state;
    finalize   := finalize_stk_mem;
    exec_syscall  := exec_syscall_s;
    exec_syscallP := exec_syscallPs;
    exec_syscallS := exec_syscallSs;
}.

End SEM_CALL_PARAMS.

End WITH_PARAMS.

End WSW.

Ltac t_get_var :=
  repeat (
    rewrite get_var_eq
    || (rewrite get_var_neq; last by [|apply/nesym])
  ).

