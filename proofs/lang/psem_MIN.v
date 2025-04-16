(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
Require Import xseq.
Require Export array type expr gen_map warray_ sem_type sem_op_typed values varmap expr_facts low_memory syscall_sem psem_defs psem_core.
Require Export
  flag_combination
  sem_params.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.
Open Scope vm_scope.


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
Section SEM_defs.

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

End SEM_defs.


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
  move=> /[dup] /(write_var_eq_on1 vm1) [vm2' hw2 h] hw1 hs.
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
    rewrite (@read_e_eq_on _ _ _ _ wdb gd Sv.empty vm1 s1);first last.
    + by apply: eq_onI Hvm;rewrite read_eE;SvD.fsetdec.
    by t_xrbindP => > -> /= -> > -> /= -> ? -> ? /= -> <- /=; exists vm1.
  + rewrite read_eE=> Hvm.
    rewrite (on_arr_var_eq_on _ (s' := with_vm s1 vm1) _ Hvm); last by SvD.fsetdec.
    rewrite (@read_e_eq_on _ _ _ _ _ gd (Sv.add x Sv.empty) vm1) /=;first last.
    + by apply: eq_onI Hvm;rewrite read_eE.
    apply: on_arr_varP => n t Htx; rewrite /on_arr_var => -> /=.
    by t_xrbindP => > -> /= -> ? -> ? /= -> /= /(write_var_eq_on1 vm1).
  rewrite read_eE=> Hvm.
  rewrite (on_arr_var_eq_on _ (s' := with_vm s1 vm1) _ Hvm); last by SvD.fsetdec.
  rewrite (@read_e_eq_on _ _ _ _ _ gd (Sv.add x Sv.empty) vm1) /=;first last.
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

Section Expr.

Context (wdb : bool) (gd : glob_decls) (s : estate).

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

End WITH_PARAMS.

End WSW.

