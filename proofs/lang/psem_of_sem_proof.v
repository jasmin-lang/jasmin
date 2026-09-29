Require Import psem psem_facts it_sems_core relational_logic.
Import Utf8.
From mathcomp Require Import ssreflect ssrfun ssrbool.

#[local] Existing Instance indirect_c.
Section PROOF.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {sCP : forall {wsw : WithSubWord}, semCallParams}.

Variable (p:prog) (ev:extra_val_t).

Notation gd := (p_globs p).

Notation vmap_n := (Vm.t (wsw:= nosubword)).
Notation vmap_s := (Vm.t (wsw:= withsubword)).

Notation estate_n := (estate (wsw:= nosubword)).
Notation estate_s := (estate (wsw:= withsubword)).

#[local]Open Scope vm_scope.

Notation estate_sim := (st_eq (wsw1:=nosubword) (wsw2:=withsubword) tt).

Lemma estate_sim_scs env (e : estate_n env) (e' : estate_s env) scs :
  estate_sim e e' ->
  estate_sim (with_scs e scs) (with_scs e' scs).
Proof. by case => *; constructor. Qed.

Lemma estate_sim_mem env (e : estate_n env) (e' : estate env) m :
  estate_sim e e' ->
  estate_sim (with_mem e m) (with_mem e' m).
Proof. by case => *; constructor. Qed.

Lemma vmap0_sim env : (Vm.init (wsw:= nosubword) env =1 Vm.init (wsw:= withsubword) env)%vm.
Proof. by move=> x; rewrite !Vm.initP. Qed.

Lemma get_var_sim env1 env2 (vm : vmap_n env1) (vm' : vmap_s env2) :
  (vm =1 vm')%vm →
  ∀ x, get_var true vm x = get_var true vm' x.
Proof. by move=> heq x; rewrite /get_var heq. Qed.

Lemma get_gvar_sim env1 env2 gd (vm : vmap_n env1) (vm' : vmap_s env2) :
  env1 =1 env2 ->
  (vm =1 vm')%vm →
  ∀ x, get_gvar true gd vm x = get_gvar true gd vm' x.
Proof.
move => heq h x; rewrite /get_gvar (get_var_sim h).
by rewrite /get_global (eval_atype_ext heq).
Qed.

Lemma vm_truncate_val_sim t v :
  truncatable true (wsw:=nosubword) t v →
     vm_truncate_val (wsw:=nosubword) t v =
     vm_truncate_val (wsw:=withsubword) t v.
Proof.
  move=>/vm_truncate_valE; case: v => [b|z|len a|ws w|//].
  1-3: by move=> [-> ].
  by move=> [ws' [-> ]] /=.
Qed.

Lemma vmap_set_sim env1 env2 (vm : vmap_n env1) (vm' : vmap_s env2) x v:
  env1 =1 env2 ->
  (vm =1 vm')%vm →
  truncatable true (wsw:=nosubword) (eval_atype env2 (vtype x)) v →
  (vm.[x <- v] =1 vm'.[x <- v])%vm.
Proof.
  move => heq hvm hv y; rewrite !Vm.setP.
  rewrite (eval_atype_ext heq).
  by rewrite vm_truncate_val_sim // hvm.
Qed.

Lemma truncatable_sim ty v :
  truncatable true (wsw:= nosubword) ty v ->
  truncatable true (wsw:= withsubword) ty v.
Proof.
  move=> /vm_truncate_valE; case: (v) => [b|z|len a|ws w| t i] /=.
  1-3,5: by move=> [-> _] //=; rewrite eqxx.
  by move=> [ws' [-> _ _]] /=.
Qed.

Lemma set_var_sim env1 env2 (vm1 : vmap_n env1) (vm1' : vmap_s env2) x v vm2 :
  env1 =1 env2 ->
  (vm1 =1 vm1')%vm →
  set_var true vm1 x v = ok vm2 →
  ∃ vm2',
    (vm2 =1 vm2')%vm ∧
    set_var true vm1' x v = ok vm2'.
Proof.
  move=> heq hsim /set_varP [hdb /[dup]htr /truncatable_sim htr' ->].
  rewrite (eval_atype_ext heq) in htr'.
  rewrite (set_var_truncate hdb htr') //; eexists; split; last by eauto.
  apply vmap_set_sim => //.
  by rewrite -(eval_atype_ext heq).
Qed.

Section SEM_PEXPR_SIM.

  Context env1 env2 (s : estate_n env1) (s': estate env2) (hs: estate_sim s s').

  Let P e : Prop :=
    ∀ v,
      sem_pexpr true gd s e = ok v →
      sem_pexpr true gd s' e = ok v.

  Let Q es : Prop :=
    ∀ vs,
      sem_pexprs true gd s es = ok vs →
      sem_pexprs true gd s' es = ok vs.

  Lemma sem_pexpr_s_sim : (∀ e, P e) ∧ (∀ es, Q es).
  Proof using hs.
    case: hs => ? hmem heq hsim.
    apply: pexprs_ind_pair; subst P Q; split => //=; t_xrbindP.
    + by move=> ? he ? hes ?? /he -> ? /hes -> <-.
    + move=> ws n _ <-.
      by rewrite (eval_ext heq).
    + by move=> ?? <-;apply/esym/get_gvar_sim.
    1,2: move=> > he ?; rewrite /on_arr_var /on_arr_var (get_gvar_sim _ heq hsim);
         t_xrbindP => -[] // > ->; t_xrbindP => > /he -> /= -> ? /=.
    2: rewrite -(eval_ext heq).
    1,2: by move=> -> <-.
    + by move=> > he >; rewrite hmem => /he -> /= -> > /= -> <-.
    + move=> > he > /he -> /=.
      by rewrite (sem_sop1_ext heq).
    + move=> > he1 > he2 > /he1 -> > /he2 -> /=.
      by rewrite (sem_sop2_ext heq).
    + move=> > hes > /hes; rewrite /sem_pexprs => -> /=.
      by rewrite (sem_opN_ext heq).
    move=> > he > he1 > he2 > /he -> /= -> > /he1 ->.
    rewrite (eval_atype_ext heq).
    by move=> /= -> > /he2 -> /= -> <-.
  Qed.

End SEM_PEXPR_SIM.

Definition sem_pexpr_sim env1 env2 s e v s' h :=
  (@sem_pexpr_s_sim env1 env2 s s' h).1 e v.

Definition sem_pexprs_sim env1 env2 s es vs s' h :=
  (@sem_pexpr_s_sim env1 env2 s s' h).2 es vs.

Lemma write_var_sim env1 env2 (s1 : estate_n env1) x v (s2 : estate_n env1) (s1':estate env2) :
  estate_sim s1 s1' →
  write_var true x v s1 = ok s2 →
  ∃ s2', estate_sim s2 s2' ∧ write_var true x v s1' = ok s2'.
Proof.
case => hscs hm heq hvm; rewrite /write_var; t_xrbindP => vm hw <- {s2}.
case: (set_var_sim heq hvm hw) => vm' [hvm' ->].
by eexists; split; split.
Qed.

Corollary write_vars_sim env (s1 : estate_n env) xs vs s2 (s1' : estate env) :
  estate_sim s1 s1' →
  write_vars true xs vs s1 = ok s2 →
  ∃ s2', estate_sim s2 s2' ∧ write_vars true xs vs s1' = ok s2'.
Proof.
elim: xs vs s1 s1' s2.
- by case => // s1 s1' s2 h [<-]; exists s1'.
by move => x xs ih [] // v vs s1 s1' s3 hss'1 /=; apply: rbindP => s2 /(write_var_sim hss'1) [s2'] [hss'2 ->] /(ih _ _ _ _ hss'2).
Qed.

Lemma write_lval_sim env1 env2 (s1 : estate_n env1) x v s2 (s1' : estate env2) :
  estate_sim s1 s1' →
  write_lval true gd x v s1 = ok s2 →
  ∃ s2', estate_sim s2 s2' ∧ write_lval true gd x v s1' = ok s2'.
Proof.
case => hscs hm heq hvm; case: x => /=.
- move => _ ty; rewrite /write_none.
  rewrite -(eval_atype_ext heq).
  by t_xrbindP => /truncatable_sim -> -> <-; exists s1'.
- move => x; exact: write_var_sim.
- move => al sz vi e; t_xrbindP => ? ?;
    rewrite hm  => /(sem_pexpr_sim (And4 hscs hm heq hvm))
        -> /= -> ? -> ? /= -> <- /=.
  by eexists; split; split.
- move => al aa ws x e.
  rewrite /on_arr_var /on_arr_var (get_var_sim hvm) /write_var.
  t_xrbindP => -[] // n t -> /=; t_xrbindP => ??
      /(sem_pexpr_sim (And4 hscs hm heq hvm)) -> /= -> ? -> /= ? -> ? /(set_var_sim heq hvm) /= [vm' [h ->]] <-.
  by eexists; split; split.
move => aa ws ofs x e.
rewrite /on_arr_var (get_var_sim hvm) /write_var; t_xrbindP => t -> /=.
case: t => // n t; t_xrbindP => ?? /(sem_pexpr_sim (And4 hscs hm heq hvm)) -> /= ->.
rewrite (eval_ext heq) => ? -> /= ? -> ? /(set_var_sim heq hvm).
case => vm' [] h /= -> <- /=.
by eexists; split; split.
Qed.

Corollary write_lvals_sim env1 env2 (s1 : estate_n env1) xs vs s2 (s1' : estate env2) :
  estate_sim s1 s1' →
  write_lvals true gd s1 xs vs = ok s2 →
  ∃ s2', estate_sim s2 s2' ∧ write_lvals true gd s1' xs vs = ok s2'.
Proof.
elim: xs vs s1 s1'.
- by case => // ? ? h [<-]; eauto.
move => x xs ih [] // v vs s1 s1' h /=; apply: rbindP => s' /(write_lval_sim h) [s2'] [h'] ->.
exact: (ih _ _ _ h').
Qed.

Section IT_SEM.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Lemma wdb_ok_eq_true wdb1 wdb2: wdb_ok wdb1 wdb2 -> wdb1 /\ wdb2.
Proof. by case => -[-> ->]. Qed.

Lemma checker_st_uinclP : Checker_eq p p (checker_st_eq (wsw1:=nosubword) (wsw2:=withsubword)).
Proof.
  constructor.
  + move=> env1 env2 _ _ [] es1 es2 [] /wdb_ok_eq_true [-> ->] <- s1 s2 vs1 hsim he.
    by have := sem_pexprs_sim hsim he; eauto.
  move=> env1 env2 _ _ d xs1 xs2 d' /wdb_ok_eq_true [-> ->] <- vs s1 s2 s1' hsim hw.
  have [?[]]:= write_lvals_sim hsim hw; eauto.
Qed.
#[local] Hint Resolve checker_st_uinclP : core.

Section REC.

Hypothesis hsyscall : forall scs1 scs2 mem1 mem2 o ves vs,
  exec_syscall (wsw:= nosubword)   scs1 mem1 o ves = ok (scs2, mem2, vs) ->
  exec_syscall (wsw:= withsubword) scs1 mem1 o ves = ok (scs2, mem2, vs).

Context (env : env_t).

Let Pi_ (i:instr) :=
  wequiv_rec (wsw1:= nosubword) (wsw2:= withsubword) (env1:=env) (env2:=env)
    p p ev ev eq_spec estate_sim [::i] [::i] estate_sim.

Let Pr_ (i:instr_r) := forall ii, Pi_ (MkI ii i).

Let Pc_ (c:cmd) :=
  wequiv_rec (wsw1:= nosubword) (wsw2:= withsubword) (env1:=env) (env2:=env)
    p p ev ev eq_spec estate_sim c c estate_sim.

Lemma it_psem_call_rec c : Pc_ c.
Proof using hsyscall.
  apply (cmd_rect (Pr := Pr_) (Pi:=Pi_) (Pc:=Pc_)) => // {c}.
  + by apply wequiv_nil.
  + by move=> i c; apply wequiv_cons.
  + by move=> >;apply wequiv_assgn_rel_eq with checker_st_eq tt.
  + by move=> >; apply wequiv_opn_rel_eq with checker_st_eq tt.
  + move=> ????; apply wequiv_syscall_rel_eq_core with checker_st_eq tt => //.
    move=> [???] [???] ? [<- <- <-]; rewrite /fexec_syscall /=.
    by t_xrbindP => -[[??]?] /= /hsyscall -> [<-] /=; eauto.
  + by move=> a ii; apply wequiv_noassert.
  + by move=> > hc1 hc2 ii; apply wequiv_if_rel_eq with checker_st_eq tt tt tt.
  + by move=> > hc ii; apply wequiv_for_rel_eq with checker_st_eq tt tt.
  + by move=> > hc hc' ii; apply wequiv_while_rel_eq with checker_st_eq tt.
  move=> ?????; apply wequiv_call_rel_eq with checker_st_eq tt => //.
  by move=> ???? [<- <-]; apply: wequiv_fun_rec.
Qed.

End REC.

Lemma it_psem_call :
  (forall scs1 scs2 mem1 mem2 o ves vs,
    exec_syscall (wsw:= nosubword)   scs1 mem1 o ves = ok (scs2, mem2, vs) ->
    exec_syscall (wsw:= withsubword) scs1 mem1 o ves = ok (scs2, mem2, vs)) ->

  (forall fd scs mem env s,
    init_state (f_extra fd) (p_extra p) ev {| escs := scs; emem := mem; evm := Vm.init env |} = ok s ->
    exists2 s',
      init_state (f_extra fd) (p_extra p) ev {| escs := scs; emem := mem; evm := Vm.init env |} = ok s' &
      estate_sim s s') ->

  (forall fd mem, finalize (wsw:= nosubword) (f_extra fd) mem = finalize (wsw:= withsubword) (f_extra fd) mem) ->

  forall fn,
    wiequiv_f (wsw1:=nosubword) (wsw2:=withsubword) p p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
  move=> hsyscall hinitstate hfinal fn.
  rewrite /wiequiv_f.
  apply wequiv_fun_ind => {}fn _ vals _ fs _ [<- [<- <-]] fd ->; exists fd => //= s1 hinit.
  have : exists2 s2 : estate_s _, initialize_funcall p ev fd (create_env (f_al fd) vals) fs = ok s2 & estate_sim s1 s2.
  + move: hinit; rewrite /initialize_funcall.
    t_xrbindP => > -> s1' /hinitstate [s2'] /= -> hs hw.
    have [s2'' [] /=]:= write_vars_sim hs hw; eauto.
  move=> [s2 h1 h2]; exists s2 => //.
  exists estate_sim, estate_sim; split => //; last first.
  + move=> s1' s2' fs1' [hscs hmem heq hvm]; rewrite /finalize_funcall.
    t_xrbindP => vs.
    rewrite /get_var_is (mapM_ext (λ (x : var_i) _, get_var_sim hvm x)) hfinal hscs hmem => -> /=.
    by move=> ? -> <- /=; eauto.
  exact: it_psem_call_rec.
Qed.

End IT_SEM.

End PROOF.

Section INSTANCE.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Lemma it_psem_call_u (p:uprog) ev fn :
  wiequiv_f (wsw1:=nosubword) (wsw2:=withsubword) p p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
  apply (it_psem_call (sCP := fun wsw => sCP_unit (wsw := wsw))) => //=.
  move=> _ ???? [<-]; eexists; eauto.
  by split => //= x; rewrite !Vm.initP.
Qed.

Lemma it_psem_call_s (p:sprog) ev fn :
  wiequiv_f (wsw1:=nosubword) (wsw2:=withsubword) p p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
  apply (it_psem_call (sCP := fun wsw => sCP_stack (wsw := wsw))) => //=.
  clear.
  move=> fd scs mem env s.
  rewrite /init_stk_state; t_xrbindP => mem' -> hw.
  have hsim : st_eq (wsw1:= nosubword) (wsw2:= withsubword) tt
                 {| escs := scs; emem := mem'; evm := Vm.init env |}
                 {| escs := scs; emem := mem'; evm := Vm.init env |}.
  + by split => //= ?; rewrite !Vm.initP.
  have [s' [hsim' hw']] := write_vars_sim hsim hw.
  by exists s'.
Qed.

End INSTANCE.
