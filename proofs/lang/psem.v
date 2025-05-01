(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
Require Import xseq.
Require Export array type expr gen_map warray_ sem_type sem_op_typed values varmap expr_facts low_memory syscall_sem psem_defs.
Require Export psem_core it_sems_core hoare_logic relational_logic.
Require Export
  flag_combination
  sem_params.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.
Open Scope vm_scope.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Section WSW.
Context {wsw:WithSubWord}.

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

Definition get_lvar_i (x: lval) : exec var_i :=
  if x is Lvar x then ok x else type_error.

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

| Ewhile_true s1 s2 s3 s4 a c e ei c' :
    sem s1 c s2 ->
    sem_pexpr true gd s2 e = ok (Vbool true) ->
    sem s2 c' s3 ->
    sem_i s3 (Cwhile a c e ei c') s4 ->
    sem_i s1 (Cwhile a c e ei c') s4

| Ewhile_false s1 s2 a c e ei c' :
    sem s1 c s2 ->
    sem_pexpr true gd s2 e = ok (Vbool false) ->
    sem_i s1 (Cwhile a c e ei c') s2

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

Lemma esem_sem c s s' : esem P ev c s = ok s' -> sem s c s'.
Proof.
  set Pi := fun i => forall s s', esem_i P ev i s = ok s' -> sem_I s i s'.
  set Pi_r := fun i => forall ii s s', esem_i P ev (MkI ii i) s = ok s' -> sem_i s i s'.
  set Pc := fun c => forall s s', esem P ev c s = ok s' -> sem s c s'.
  move: s s'.
  apply (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => {c} //; rewrite /Pi /Pi_r /Pc.
  + by move=> > h > /h ?; constructor.
  + by move=> > [<-]; constructor.
  + by move=> > hi hc > /=; t_xrbindP => > /hi ? /hc; apply Eseq.
  + by move=> > /=; rewrite /sem_assgn; t_xrbindP => *; eapply Eassgn; eauto.
  + by move=> > /=; apply: Eopn.
  + move=> > /=; rewrite /sem_syscall /fexec_syscall /upd_estate; t_xrbindP.
    move=> ? hes ? [[scs mem] vs] /= ? [<-] /= ?.
    by eapply Esyscall; eauto.
  + move=> > hc1 hc2 > /=; rewrite /sem_cond; t_xrbindP => b v hv /to_boolI ?; subst v.
    by case: b hv => [ hv /hc1 | hc /hc2]; [apply Eif_true | apply Eif_false].
  move=> > hc /= _ s s'; rewrite /sem_bound; t_xrbindP.
  move=> > hlo /to_intI ? > hhi /to_intI ? <- hfor; subst.
  eapply Efor; eauto => {hhi hlo}.
  elim: wrange s hfor => /= [ | j js hrec] s.
  + by move=> [<-]; constructor.
  t_xrbindP.
  by move=> s1 s2 hw /hc + /hrec; apply EForOne.
Qed.

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
    forall (s1 s2 s3 s4 : estate) a (c : cmd) (e : pexpr) (ei: instr_info) (c' : cmd),
    sem s1 c s2 -> Pc s1 c s2 ->
    sem_pexpr true gd s2 e = ok (Vbool true) ->
    sem s2 c' s3 -> Pc s2 c' s3 ->
    sem_i s3 (Cwhile a c e ei c') s4 -> Pi_r s3 (Cwhile a c e ei c') s4 -> Pi_r s1 (Cwhile a c e ei c') s4.

  Definition sem_Ind_while_false : Prop :=
    forall (s1 s2 : estate) a (c : cmd) (e : pexpr) (ei: instr_info) (c' : cmd),
    sem s1 c s2 -> Pc s1 c s2 ->
    sem_pexpr true gd s2 e = ok (Vbool false) ->
    Pi_r s1 (Cwhile a c e ei c') s2.

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
    | @Ewhile_true s1 s2 s3 s4 a c e1 ei c' s0 e2 s5 s6 =>
      @Hwhile_true s1 s2 s3 s4 a c e1 ei c' s0 (@sem_Ind s1 c s2 s0) e2 s5 (@sem_Ind s2 c' s3 s5) s6
          (@sem_i_Ind s3 (Cwhile a c e1 ei c') s4 s6)
    | @Ewhile_false s1 s2 a c e1 ei c' s0 e2 =>
      @Hwhile_false s1 s2 a c e1 ei c' s0 (@sem_Ind s1 c s2 s0) e2
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
  | Cwhile a c e ei c' =>
    ∃ si b,
       [/\ sem s c si, sem_pexpr true gd si e = ok (Vbool b) &
                       if b then ∃ sj, sem si c' sj ∧ sem_i sj (Cwhile a c e ei c') s' else si = s' ]
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
  - by move => s si sj s' c e c' ei hc he hc' hrec; exists si, true; constructor => //; exists sj.
  - by move => s s' c e c' ei hc he; exists s', false.
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
  case => { scs1 m1 fn vargs' scs2 m2 vres' } - scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres'.
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
  + by move=> s1 s2 s3 s4 a c e ei c' _ Hc _ _ Hc' _ Hw z Hnin; rewrite Hc ?Hc' ?Hw //;
     move: Hnin; rewrite write_i_while; SvD.fsetdec.
  + move=> s1 s2 a c e ei c' _ Hc _ z Hnin; rewrite Hc //.
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

Section ST_EQ.

Context
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {scP : semCallParams (wsw:= wsw) (pT := pT)}
  {dc: DirectCall}.

Lemma st_eq_refl d s : st_eq d s s.
Proof. by split. Qed.
Hint Resolve st_eq_refl : core.

Section PROG.

Context (p p': prog) (ev ev': extra_val_t).

Context (eq_globs: p_globs p = p_globs p').

Lemma st_eq_sem_pexpr wdb d e :
  wrequiv (st_eq d) ((sem_pexpr wdb (p_globs p))^~ e) ((sem_pexpr wdb (p_globs p'))^~ e) eq.
Proof.
  move=> s t v /st_relP [-> /=] hvm; rewrite eq_globs.
  rewrite -sem_pexpr_ext_eq //; eauto.
Qed.

Lemma st_eq_sem_pexprs wdb d es :
  wrequiv (st_eq d) ((sem_pexprs wdb (p_globs p))^~ es) ((sem_pexprs wdb (p_globs p'))^~ es) eq.
Proof.
  move=> s t v /st_relP [-> /=] hvm; rewrite eq_globs.
  rewrite -sem_pexprs_ext_eq //; eauto.
Qed.

Lemma st_eq_write_lvals wdb d x v d':
  wrequiv (st_eq d) (fun s => write_lvals wdb (p_globs p) s x v) (fun s => write_lvals wdb (p_globs p') s x v) (st_eq d').
Proof.
  rewrite eq_globs => s t s' /st_relP [-> /=] h1 h2.
  by have [vm2 h ->] := write_lvars_ext_eq h1 h2; eexists; eauto.
Qed.

Lemma wdb_ok_eq wdb1 wdb2 : wdb_ok wdb1 wdb2 -> wdb1 = wdb2.
Proof. by case => -[-> ->]. Qed.

Lemma checker_st_eqP : Checker_eq p p' checker_st_eq.
Proof.
  constructor.
  + by move=> wdb _ d es1 es2 d' /wdb_ok_eq <- <-; apply st_eq_sem_pexprs.
  move=> wdb _ d xs1 xs2 d' /wdb_ok_eq <- <- vs; apply st_eq_write_lvals.
Qed.
#[local] Hint Resolve checker_st_eqP : core.

Section FUN.

Context {E E0 : Type -> Type} {sem_F : sem_Fun E} {wE: with_Error E E0} {rE0 : EventRels E0}.

Let Pi i := wequiv p p' ev ev' (st_eq tt) [::i] [::i] (st_eq tt).

Let Pi_r i := forall ii, Pi (MkI ii i).

Let Pc c := wequiv p p' ev ev' (st_eq tt) c c (st_eq tt).

Lemma wequiv_st_eq c :
  (forall f, wequiv_f p p' ev ev' (λ (_ _ : funname), eq) f f (λ (_ _ : funname) (_ _ : fstate), eq)) ->
  Pc c.
Proof.
  move=> hf; apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => // {c}.
  + by apply wequiv_nil.
  + by move=> *; apply wequiv_cons with (st_eq tt).
  + by move=> >;apply wequiv_assgn_rel_eq with checker_st_eq tt.
  + by move=> >; apply wequiv_opn_rel_eq with checker_st_eq tt.
  + by move=> >; apply wequiv_syscall_rel_eq with checker_st_eq tt.
  + by move=> > hc1 hc2 ii; apply wequiv_if_rel_eq with checker_st_eq tt tt tt.
  + by move=> > hc ii; apply wequiv_for_rel_eq with checker_st_eq tt tt.
  + by move=> > hc hc' ii; apply wequiv_while_rel_eq with checker_st_eq tt.
  by move=> ????; apply wequiv_call_rel_eq with checker_st_eq tt.
Qed.

End FUN.

Section REC.

Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Lemma wequiv_rec_st_eq c : wequiv_rec p p' ev ev' eq_spec (st_eq tt) c c (st_eq tt).
Proof.
  apply wequiv_st_eq.
  by move=> f s t <-; apply xrutt_facts.xrutt_trigger.
Qed.

End REC.

End PROG.

Section WIEQUIV_F.

Context (p : prog) (ev: extra_val_t).
Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Lemma st_eq_finalize fd :
  wrequiv (st_eq tt) (finalize_funcall fd) (finalize_funcall fd) eq.
Proof.
  rewrite /finalize_funcall => s t fs' [h1 h2 h3].
  t_xrbindP => vs.
  rewrite -!(sem_pexprs_get_var _ [::]).
  rewrite (sem_pexprs_ext_eq _ _ _ h3).
  case: s t h1 h2 h3 => scs mem vm1 [/= _ _ vm2] <- <- h3 -> /= ? -> <- /=.
  eexists; eauto.
Qed.

Lemma wiequiv_f_eq fn : wiequiv_f p p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
  apply wequiv_fun_ind => hrec {fn}.
  move=> fn _ fs _ [<- <-] fd hget.
  exists fd => //.
  exists (st_eq tt), (st_eq tt).
  move=> s1; exists s1; split => //.
  + by apply wequiv_rec_st_eq.
  apply st_eq_finalize.
Qed.

Lemma wiequiv_st_eq c : wiequiv p p ev ev (st_eq tt) c c (st_eq tt).
Proof. by apply wequiv_st_eq => // f ???; apply wiequiv_f_eq. Qed.

End WIEQUIV_F.

End ST_EQ.

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
  + move=> s1 s2 s3 s4 a c1 e ei c2 _ ih1 he _ ih2 _ ihw vm1 X.
    rewrite read_i_while => hsub heq1.
    have [|vm2 hs1 heq2] := ih1 vm1 X _ heq1; first SvD.fsetdec.
    have [|vm3 hs2 heq3] := ih2 vm2 X _ heq2; first SvD.fsetdec.
    have [|vm4 hs3 heq4] := ihw vm3 X _ heq3; first by rewrite read_i_while.
    exists vm4 => //; apply: Ewhile_true; eauto.
    rewrite -read_e_eq_on_empty //.
    by rewrite read_eE; apply: eq_onI heq2; SvD.fsetdec.
  + move=> s1 s2 a c1 e ei c2 _ ih1 he vm1 X.
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

Section IT_Sem_eqv.

Context
  {dc:DirectCall}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {sCP : semCallParams}.

Definition st_eq_on X := st_rel eq_on X.

Lemma read_es_st_eq_on gd wdb es X :
  Sv.Subset (read_es es) X ->
  wrequiv (st_eq_on X) ((sem_pexprs wdb gd)^~ es) ((sem_pexprs wdb gd)^~ es) eq.
Proof.
  move=> hsub s t v [???];rewrite (eq_on_sem_pexprs _ (s' := t)) //.
  + by move => ->; eauto.
  by apply: (eq_onI hsub).
Qed.

Lemma write_lvals_st_eq_on gd wdb xs vs X :
  Sv.Subset (read_rvs xs) X ->
  wrequiv
    (st_eq_on X)
    (λ s1 : estate, write_lvals wdb gd s1 xs vs) (λ s2 : estate, write_lvals wdb gd s2 xs vs)
    (st_eq_on (Sv.union (vrvs xs) X)).
Proof.
  move=> hsub s [?? vm] s' [/= <- <- hvm] hw.
  by have [vm' -> ? ] := write_lvals_eq_on hsub hw hvm; eexists; eauto.
Qed.

Definition check_es_st_eq_on (X:Sv.t) (es1 es2 : pexprs) (X':Sv.t) :=
  [/\ X = X', es1 = es2 & Sv.Subset (read_es es1) X].

Definition check_lvals_st_eq_on (X:Sv.t) (xs1 xs2 : lvals) (X':Sv.t) :=
  [/\ X = X', xs1 = xs2 & Sv.Subset (read_rvs xs1) X].

Lemma check_esP_R_st_eq_on X es1 es2 X':
  check_es_st_eq_on X es1 es2 X' → ∀ vm1 vm2 : Vm.t, vm1 =[X] vm2 → vm1 =[X'] vm2.
Proof. by move=> [<-]. Qed.

Definition checker_st_eq_on : Checker_e eq_on :=
  {| check_es := check_es_st_eq_on;
     check_lvals := check_lvals_st_eq_on;
     check_esP_R := check_esP_R_st_eq_on |}.

Section PROG.

Context (p p':prog) (ev ev': extra_val_t).

Local Notation gd := (p_globs p).
Local Notation gd' := (p_globs p').

Context (eq_globs : gd = gd').

Lemma checker_st_eq_onP : Checker_eq p p' checker_st_eq_on.
Proof.
  constructor; rewrite -eq_globs.
  + by move=> wdb _ d es1 es2 d' /wdb_ok_eq <- [? <- ?]; apply read_es_st_eq_on.
  move=> wdb _ d xs1 xs2 d' /wdb_ok_eq <- [<- <- ?] vs.
  apply wrequiv_weaken with (st_rel eq_on d) (st_rel eq_on (Sv.union (vrvs xs1) d)) => //.
  + by apply st_rel_weaken => ??; apply eq_onI; SvD.fsetdec.
  by apply write_lvals_st_eq_on.
Qed.
#[local] Hint Resolve checker_st_eq_onP : core.

Section FUN.

Context {E E0 : Type -> Type} {sem_F : sem_Fun E} {wE: with_Error E E0} {rE0 : EventRels E0}.

Let Pi i :=
  forall X, Sv.Subset (read_I i) X ->
    wequiv p p' ev ev' (st_eq_on X) [::i] [::i] (st_eq_on X).

Let Pi_r i :=
 forall ii X, Sv.Subset (read_i i) X ->
    wequiv p p' ev ev' (st_eq_on X) [::MkI ii i] [::MkI ii i] (st_eq_on X).

Let Pc c :=
  forall X, Sv.Subset (read_c c) X ->
  wequiv p p' ev ev' (st_eq_on X) c c (st_eq_on X).

Lemma it_read_cP_aux c X :
  (forall fn,
     wequiv_f p p' ev ev' (λ (_ _ : funname), eq) fn fn (λ _ _  _ _, eq)) ->
  Sv.Subset (read_c c) X ->
  wequiv p p' ev ev' (st_eq_on X) c c (st_eq_on X).
Proof.
  move=> hfn; apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => // {c X}.
  + by move=> i ii hi X; apply hi.
  + by move=> ii X; apply wequiv_nil.
  + move=> i c hi hc X; rewrite read_c_cons => hsub.
    by apply wequiv_cons with (st_eq_on X); [apply hi | apply hc]; SvD.fsetdec.
  + move=> x tg ty e ii X. rewrite read_i_assgn => hsub.
    apply wequiv_assgn_rel_eq with checker_st_eq_on X => //=.
    + by split => //; rewrite /read_es /= read_eE; SvD.fsetdec.
    by split => //; rewrite /read_rvs /= read_rvE; SvD.fsetdec.
  + move=> xs tg o es ii X. rewrite read_i_opn => hsub.
    by apply wequiv_opn_rel_eq with checker_st_eq_on X => //=; split=> //; SvD.fsetdec.
  + move=> xs sc es ii X. rewrite read_i_syscall => hsub.
    by apply wequiv_syscall_rel_eq with checker_st_eq_on X => //=; split=> //; SvD.fsetdec.
  + move=> e c1 c2 hc1 hc2 ii X. rewrite read_i_if => hsub.
    apply wequiv_if_rel_eq with checker_st_eq_on X X X => //.
    + by split => //; rewrite /read_es /= read_eE; SvD.fsetdec.
    + by apply hc1; SvD.fsetdec.
    by apply hc2; SvD.fsetdec.
  + move=> i d lo hi c hc ii X; rewrite read_i_for => hsub.
    apply wequiv_for_rel_eq with checker_st_eq_on X X => //.
    + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
    + by split => //; rewrite /read_rvs /=; SvD.fsetdec.
    apply hc; SvD.fsetdec.
  + move=> a c e ii' c' hc hc' ii X. rewrite read_i_while => hsub.
    apply wequiv_while_rel_eq with checker_st_eq_on X => //.
    + by split => //; rewrite /read_es /= read_eE; SvD.fsetdec.
    + by apply hc; SvD.fsetdec.
    by apply hc'; SvD.fsetdec.
  + move=> xs fn es ii X; rewrite read_i_call => hsub.
  apply wequiv_call_rel_eq with checker_st_eq_on X => //.
  + by split => //; SvD.fsetdec.
  by split => //; SvD.fsetdec.
Qed.

End FUN.

Section REC.

Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Lemma it_read_cP_rec X c :
  Sv.Subset (read_c c) X ->
  wequiv_rec p p' ev ev' eq_spec (st_eq_on X) c c (st_eq_on X).
Proof.
  apply it_read_cP_aux.
  by move=> f s t <-; apply xrutt_facts.xrutt_trigger.
Qed.

End REC.

End PROG.

Section REFL.

Context (p : prog) (ev: extra_val_t).
Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Lemma it_read_cP X c :
  Sv.Subset (read_c c) X ->
  wiequiv p p ev ev (st_eq_on X) c c (st_eq_on X).
Proof. by apply it_read_cP_aux => // fn ?? h; apply wiequiv_f_eq. Qed.

End REFL.

End IT_Sem_eqv.

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
  move=> s1 s2 s3 s4 a c e ei c' _ Hc H _ Hc' _ Hw vm1 Hvm1.
  have [vm2 [Hs2 Hvm2]] := Hc _ Hvm1.
  have [v' H1 /value_uinclE ?]:= sem_pexpr_uincl Hvm2 H;subst.
  have [vm3 [H4 /Hw [vm4] [??]]]:= Hc' _ Hvm2;exists vm4;split => //.
  by eapply Ewhile_true;eauto;rewrite H1.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 a c e ei c' _ Hc H vm1 Hvm1.
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

(* ---------------------------------------------------------------- *)
Section IT_UNDEFINCL.

Context
  {dc:DirectCall}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {sCP : semCallParams}.

Lemma read_es_st_uincl d gd wdb es :
  wrequiv (st_uincl d) ((sem_pexprs wdb gd)^~ es) ((sem_pexprs wdb gd)^~ es) (List.Forall2 value_uincl).
Proof. by move=> s t vs /st_relP [/= -> h]; apply sem_pexprs_uincl. Qed.

Lemma write_lvals_st_uincl d d' gd wdb xs vs1 vs2 :
  List.Forall2 value_uincl vs1 vs2 ->
  wrequiv
    (st_uincl d)
    (λ s1 : estate, write_lvals wdb gd s1 xs vs1) (λ s2 : estate, write_lvals wdb gd s2 xs vs2)
    (st_uincl d').
Proof.
  move=> hu s t s' /st_relP [/= -> h] hw.
  by have [vm' -> ?] := writes_uincl h hu hw; eexists; eauto.
Qed.

Section PROG.

Context (p p':prog) (ev ev': extra_val_t).

Local Notation gd := (p_globs p).
Local Notation gd' := (p_globs p').

Context (eq_globs : gd = gd').

Lemma checker_st_uinclP : Checker_uincl p p' checker_st_uincl.
Proof.
  constructor; rewrite -eq_globs.
  + by move=> wdb _ d es1 es2 d' /wdb_ok_eq <- <-; apply read_es_st_uincl.
  move=> wdb _ d xs1 xs2 d' /wdb_ok_eq <- <-; apply write_lvals_st_uincl.
Qed.
#[local] Hint Resolve checker_st_uinclP : core.

Context {E E0 : Type -> Type} {sem_F : sem_Fun E} {wE: with_Error E E0} {rE0 : EventRels E0}.

Let Pi i := wequiv p p' ev ev' (st_uincl tt) [::i] [::i] (st_uincl tt).

Let Pi_r i :=
  forall ii, wequiv p p' ev ev' (st_uincl tt) [::MkI ii i] [::MkI ii i] (st_uincl tt).

Let Pc c :=
  wequiv p p' ev ev' (st_uincl tt) c c (st_uincl tt).

Lemma it_sem_uincl_aux c :
  (forall fn,
     wequiv_f p p' ev ev' (λ (_ _ : funname), fs_uincl) fn fn (λ _ _  _ _, fs_uincl)) ->
  wequiv p p' ev ev' (st_uincl tt) c c (st_uincl tt).
Proof.
  move=> hfn; apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => // {c}.
  + by move=> i ii hi X; apply hi.
  + by move=> ii X; apply wequiv_nil.
  + move=> i c hi hc.
    by apply wequiv_cons with (st_uincl tt).
  + by move=> x tg ty e ii; apply wequiv_assgn_rel_uincl with checker_st_uincl tt.
  + by move=> xs tg o es ii; apply wequiv_opn_rel_uincl with checker_st_uincl tt.
  + by move=> xs sc es ii; apply wequiv_syscall_rel_uincl with checker_st_uincl tt.
  + by move=> e c1 c2 hc1 hc2 ii; apply wequiv_if_rel_uincl with checker_st_uincl tt tt tt.
  + by move=> > hc ii; apply wequiv_for_rel_uincl with checker_st_uincl tt tt.
  + by move=> > ?? ii; apply wequiv_while_rel_uincl with checker_st_uincl tt.
  by move=> xs fn es ii; apply wequiv_call_rel_uincl with checker_st_uincl tt.
Qed.

End PROG.

Section REFL.

Context (p : prog) (ev: extra_val_t).
Context {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0}.

Definition uincl_spec : EquivSpec :=
  {| rpreF_ := fun (fn1 fn2 : funname) (fs1 fs2 : fstate) => fn1 = fn2 /\ fs_uincl fs1 fs2
   ; rpostF_ := fun (fn1 fn2 : funname) (fs1 fs2 fr1 fr2: fstate) => fs_uincl fr1 fr2 |}.

(* TODO: Can we generalize this to different semantic ? *)
Lemma fs_uincl_initialize p' fd fd' fs fs' s:
  f_tyin fd = f_tyin fd' ->
  f_extra fd = f_extra fd' ->
  f_params fd = f_params fd' ->
  p_extra p = p_extra p' ->
  fs_uincl fs fs' ->
  initialize_funcall p ev fd fs = ok s ->
  exists2 s', initialize_funcall p' ev fd' fs' = ok s' & st_uincl tt s s'.
Proof.
  move=> hty hex hpa hpex hfs; rewrite /initialize_funcall -hty -hex -hpa -hpex /estate0 /=.
  case: hfs => <- <- hu.
  t_xrbindP => vs htr s0 -> hw.
  have [vs' -> {}hu /=] := mapM2_dc_truncate_val htr hu.
  have [vm] := [elaborate write_vars_uincl (vm_uincl_refl (evm s0)) hu hw].
  by rewrite with_vm_same => -> ? /=; eexists; eauto.
Qed.

(* TODO: Can we generalize this to different semantic ? *)
Lemma fs_uincl_finalize fd fd' :
  f_tyout fd = f_tyout fd' ->
  f_extra fd = f_extra fd' ->
  f_res fd = f_res fd' ->
  wrequiv (st_uincl tt) (finalize_funcall fd) (finalize_funcall fd') fs_uincl.
Proof.
  rewrite /finalize_funcall => <- <- <- /= s t fs [<- <- hvm].
  t_xrbindP => vs hget vs' htr <-.
  have [vs1 -> hu /=] := get_var_is_uincl hvm hget.
  have [vs1' -> {}hu /=] := mapM2_dc_truncate_val htr hu.
  by eexists; eauto.
Qed.

Lemma it_sem_uincl_f fn :
  wiequiv_f p p ev ev (rpreF (eS:= uincl_spec)) fn fn (rpostF (eS:=uincl_spec)).
Proof.
  apply wequiv_fun_ind => hrec {fn}.
  move=> {}fn _ fs1 fs2 [<-] hu fd ->; exists fd => //.
  exists (st_uincl tt), (st_uincl tt) => s.
  move=> /(fs_uincl_initialize erefl erefl erefl erefl hu) [t] -> {}hu; exists t; split => //.
  + apply it_sem_uincl_aux => //.
    by move=> fn' fs1' fs2' h; apply hrec.
  by apply: fs_uincl_finalize.
Qed.

Lemma it_sem_uincl c :
  wiequiv p p ev ev (st_uincl tt) c c (st_uincl tt).
Proof. by apply it_sem_uincl_aux => //; move=> fn ?? h; apply it_sem_uincl_f. Qed.

End REFL.

End  IT_UNDEFINCL.

End WITH_PARAMS.

End WSW.



