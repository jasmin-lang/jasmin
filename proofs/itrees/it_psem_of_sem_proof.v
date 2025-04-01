
Require Import psem psem_facts it_sems_core relational_logic.
Import Utf8.
From mathcomp Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Definition estate_sim (e: estate_n) (e': estate_s) : Prop :=
  [/\ escs e = escs e', emem e = emem e' & (evm e =1 evm e')%vm].

Lemma estate_sim_scs e e' scs :
  estate_sim e e' ->
  estate_sim (with_scs e scs) (with_scs e' scs).
Proof. by case => *; constructor. Qed.

Lemma estate_sim_mem e e' m :
  estate_sim e e' ->
  estate_sim (with_mem e m) (with_mem e' m).
Proof. by case => *; constructor. Qed.

Lemma vmap0_sim : (Vm.init (wsw:= nosubword) =1 Vm.init (wsw:= withsubword))%vm.
Proof. by move=> x; rewrite !Vm.initP. Qed.

Lemma get_var_sim (vm : vmap_n) (vm' : vmap_s) :
  (vm =1 vm')%vm →
  ∀ x, get_var true vm x = get_var true vm' x.
Proof. by move=> heq x; rewrite /get_var heq. Qed.

Lemma get_gvar_sim gd (vm : vmap_n) (vm' : vmap_s) :
  (vm =1 vm')%vm →
  ∀ x, get_gvar true gd vm x = get_gvar true gd vm' x.
Proof.
by move => h x; rewrite /get_gvar (get_var_sim h).
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

Lemma vmap_set_sim (vm : vmap_n) (vm' : vmap_s) x v:
  (vm =1 vm')%vm →
  truncatable true (wsw:=nosubword) (vtype x) v →
  (vm.[x <- v] =1 vm'.[x <- v])%vm.
Proof.
  move => hvm hv y; rewrite !Vm.setP.
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

Lemma set_var_sim (vm1 : vmap_n) (vm1' : vmap_s) x v vm2 :
  (vm1 =1 vm1')%vm →
  set_var true vm1 x v = ok vm2 →
  ∃ vm2',
    (vm2 =1 vm2')%vm ∧
    set_var true vm1' x v = ok vm2'.
Proof.
  move=> hsim /set_varP [hdb /[dup]htr /truncatable_sim htr' ->].
  rewrite (set_var_truncate hdb htr') //; eexists; split; last by eauto.
  by apply vmap_set_sim.
Qed.

Section SEM_PEXPR_SIM.

  Context s s' (hs: estate_sim s s').

  Let P e : Prop :=
    ∀ v,
      sem_pexpr true gd s e = ok v →
      sem_pexpr true gd s' e = ok v.

  Let Q es : Prop :=
    ∀ vs,
      sem_pexprs true gd s es = ok vs →
      sem_pexprs true gd s' es = ok vs.

  Lemma sem_pexpr_s_sim : (∀ e, P e) ∧ (∀ es, Q es).
  Proof.
    case: hs => ? hmem hsim.
    apply: pexprs_ind_pair; subst P Q; split => //=; t_xrbindP.
    + by move=> ? he ? hes ?? /he -> ? /hes -> <-.
    + by move=> ?? <-;apply/esym/get_gvar_sim.
    1,2: by move=> > he ?; rewrite /on_arr_var /on_arr_var (get_gvar_sim _ hsim);
         t_xrbindP => -[] // > ->; t_xrbindP => > /he -> /= -> ? /= -> <-.
    + by move=> > he >; rewrite (get_var_sim hsim) hmem => -> /= -> > /he -> /= -> > /= -> <-.
    + by move=> > he > /he ->.
    + by move=> > he1 > he2 > /he1 -> > /he2 ->.
    + by move=> > hes > /hes; rewrite /sem_pexprs => ->.
    by move=> > he > he1 > he2 > /he -> /= -> > /he1 -> /= -> > /he2 -> /= -> <-.
  Qed.

  End SEM_PEXPR_SIM.

Definition sem_pexpr_sim s e v s' h :=
  (@sem_pexpr_s_sim s s' h).1 e v.

Definition sem_pexprs_sim s es vs s' h :=
  (@sem_pexpr_s_sim s s' h).2 es vs.

Lemma write_var_sim s1 x v s2 s1' :
  estate_sim s1 s1' →
  write_var true x v s1 = ok s2 →
  ∃ s2', estate_sim s2 s2' ∧ write_var true x v s1' = ok s2'.
Proof.
case => hscs hm hvm; rewrite /write_var; t_xrbindP => vm hw <- {s2}.
case: (set_var_sim hvm hw) => vm' [hvm' ->].
by eexists; split; split.
Qed.

Corollary write_vars_sim s1 xs vs s2 s1' :
  estate_sim s1 s1' →
  write_vars true xs vs s1 = ok s2 →
  ∃ s2', estate_sim s2 s2' ∧ write_vars true xs vs s1' = ok s2'.
Proof.
elim: xs vs s1 s1' s2.
- by case => // s1 s1' s2 h [<-]; exists s1'.
by move => x xs ih [] // v vs s1 s1' s3 hss'1 /=; apply: rbindP => s2 /(write_var_sim hss'1) [s2'] [hss'2 ->] /(ih _ _ _ _ hss'2).
Qed.

Lemma write_lval_sim s1 x v s2 s1' :
  estate_sim s1 s1' →
  write_lval true gd x v s1 = ok s2 →
  ∃ s2', estate_sim s2 s2' ∧ write_lval true gd x v s1' = ok s2'.
Proof.
case => hscs hm hvm; case: x => /=.
- move => _ ty; rewrite /write_none.
  by t_xrbindP => /truncatable_sim -> -> <-; exists s1'.
- move => x; exact: write_var_sim.
- move => al sz x e; t_xrbindP => ? ?;
    rewrite hm (get_var_sim hvm) => -> /= -> ?? /(sem_pexpr_sim (And3 hscs hm hvm))
        -> /= -> ? -> ? /= -> <- /=.
  by eexists; split; split.
- move => al aa ws x e.
  rewrite /on_arr_var /on_arr_var (get_var_sim hvm) /write_var.
  t_xrbindP => -[] // n t -> /=; t_xrbindP => ??
      /(sem_pexpr_sim (And3 hscs hm hvm)) -> /= -> ? -> /= ? -> ? /(set_var_sim hvm) /= [vm' [h ->]] <-.
  by eexists; split; split.
move => aa ws ofs x e.
rewrite /on_arr_var (get_var_sim hvm) /write_var; t_xrbindP => t -> /=.
case: t => // n t; t_xrbindP => ?? /(sem_pexpr_sim (And3 hscs hm hvm)) -> /= -> ? -> /= ? -> ? /(set_var_sim hvm).
case => vm' [] h /= -> <- /=.
by eexists; split; split.
Qed.

Corollary write_lvals_sim s1 xs vs s2 s1' :
  estate_sim s1 s1' →
  write_lvals true gd s1 xs vs = ok s2 →
  ∃ s2', estate_sim s2 s2' ∧ write_lvals true gd s1' xs vs = ok s2'.
Proof.
elim: xs vs s1 s1'.
- by case => // ? ? h [<-]; eauto.
move => x xs ih [] // v vs s1 s1' h /=; apply: rbindP => s' /(write_lval_sim h) [s2'] [h'] ->.
exact: (ih _ _ _ h').
Qed.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : RelEvent E0}.
(*
#[local] Instance SC_nosubword_withsubword : sem_call_2 :=
  sc2_full (wsw1:= nosubword) (wsw2:= withsubword).

Let RPreFeq : relPreF :=
  fun fn1 fn2 fs1 fs2 =>
    fn1 = fn2 /\ fs1 = fs2.

Let RPostFeq : relPostF :=
  fun fn1 fn2 fs1 fs2 fr1 fr2 =>
    fr1 = fr2.
*)

Lemma wrequiv_sim_expr e :
  wrequiv estate_sim ((sem_pexpr true gd)^~ e) ((sem_pexpr true gd)^~ e) eq.
Proof. move=> s1 s2 v1 hsim he; have := sem_pexpr_sim hsim he; eauto. Qed.

Lemma wrequiv_sim_exprs es :
  wrequiv estate_sim ((sem_pexprs true gd)^~ es) ((sem_pexprs true gd)^~ es) eq.
Proof. move=> s1 s2 v1 hsim he; have := sem_pexprs_sim hsim he; eauto. Qed.

Lemma wrequiv_sim_lval x v :
   wrequiv estate_sim (λ s1 : estate_n, write_lval true gd x v s1)
                     (λ s2 : estate_s, write_lval true gd x v s2) estate_sim.
Proof. move=> s1 s2 s1' hsim hw; have [?[]]:= write_lval_sim hsim hw; eauto. Qed.

Lemma wrequiv_sim_lvals xs vs :
   wrequiv estate_sim (λ s1 : estate_n, write_lvals true gd s1 xs vs)
     (λ s2 : estate_s, write_lvals true gd s2 xs vs) estate_sim.
Proof. move=> s1 s2 s1' hsim hw; have [?[]]:= write_lvals_sim hsim hw; eauto. Qed.

Lemma wrequiv_sim_upd fs xs:
  wrequiv estate_sim (upd_estate true gd xs fs) (upd_estate true gd xs fs) estate_sim.
Proof. by move=> s1 s2 s1' hsim; apply wrequiv_sim_lvals; case hsim. Qed.

#[local] Hint Resolve wrequiv_sim_expr wrequiv_sim_exprs wrequiv_sim_lvals wrequiv_sim_upd wrequiv_sim_lval : core.

Notation wiequiv_f := (wequiv_f (sem_F1 := sem_fun_full (wsw:=nosubword)) (sem_F2:= sem_fun_full (wsw:=withsubword))).

Lemma psem_call :
  (forall scs1 scs2 mem1 mem2 o ves vs,
    exec_syscall (wsw:= nosubword)   scs1 mem1 o ves = ok (scs2, mem2, vs) ->
    exec_syscall (wsw:= withsubword) scs1 mem1 o ves = ok (scs2, mem2, vs)) ->

  (forall fd scs mem s,
    init_state (f_extra fd) (p_extra p) ev {| escs := scs; emem := mem; evm := Vm.init |} = ok s ->
    exists2 s',
      init_state (f_extra fd) (p_extra p) ev {| escs := scs; emem := mem; evm := Vm.init |} = ok s' &
      estate_sim s s') ->

  (forall fd mem, finalize (wsw:= nosubword) (f_extra fd) mem = finalize (wsw:= withsubword) (f_extra fd) mem) ->

  forall fn,
    wiequiv_f p p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
move=> hsyscall hinitstate hfinal fn.
apply wequiv_fun_ind => hrec {fn}.
move=> fn _ fs _ [<- <-] fd ->; exists fd => //.
exists estate_sim, estate_sim => s1 hinit.
have : exists2 s2 : estate_s, initialize_funcall p ev fd fs = ok s2 & estate_sim s1 s2.
+ move: hinit; rewrite /initialize_funcall.
  t_xrbindP => > -> s1' /hinitstate [s2'] /= -> hs hw.
  have [s2'' [] /=]:= write_vars_sim hs hw; eauto.
move=> [s2 h1 h2]; exists s2; split => //; last first.
+ move=> s1' s2' fs1' [hscs hmem hvm]; rewrite /finalize_funcall.
  t_xrbindP => vs.
  rewrite /get_var_is (mapM_ext (λ (x : var_i) _, get_var_sim hvm x)) hfinal hscs hmem => -> /=.
  move=> ? -> <- /=; eauto.
 set Pi := fun (i:instr) => wequiv_rec (wsw1:= nosubword) (wsw2:= withsubword)
                p p ev ev eq_spec estate_sim [::i] [::i] estate_sim.
 set Pr := fun (i:instr_r) => forall ii, Pi (MkI ii i).
 set Pc := fun (c:cmd) => wequiv_rec (wsw1:= nosubword) (wsw2:= withsubword)
                          p p ev ev eq_spec estate_sim c c estate_sim.
 move=> {fn fs hinit h1 h2 s1 s2 hfinal hinitstate}.
 apply (cmd_rect (Pr := Pr) (Pi:=Pi) (Pc:=Pc)) => // {fd}.
 + by apply wequiv_nil.
 + by move=> i c; apply wequiv_cons.
 + by move=> x tg ty e ii; apply wequiv_assgn_eq.
 + by move=> xs t o es ii; apply wequiv_opn_eq.
 + move=> xs o es ii; apply wequiv_syscall_eq => //.
   + by move=> > [].
   move=> [???] [???] ? [<- <- <-]; rewrite /fexec_syscall /=.
   by t_xrbindP => -[[??]?] /= /hsyscall -> [<-] /=; eauto.
 + by move=> e c1 c2 hc1 hc2 ii; apply wequiv_if_eq => // -[].
 + move=> j d lo hi c hc ii; apply wequiv_for_eq with estate_sim => //.
   move=> i s1 s2 s1' hsim hw; have [?[]]:= write_var_sim hsim hw; eauto.
 + by move=> al c e inf c' hc hc' ii; apply wequiv_while_eq.
 move=> xs f es ii; apply wequiv_call with  (rpreF (eS:=eq_spec)) (rpostF (eS:=eq_spec)) eq => //.
 + by rewrite /mk_fstate => > [<- <- _] <-.
 + by apply hrec.
 move=> fs1 fs2 fr _ _ <-.
 by apply wrequiv_sim_upd.
Qed.

End PROOF.

Section INSTANCE.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : RelEvent E0}.

Notation wiequiv_f := (wequiv_f (sem_F1 := sem_fun_full (wsw:=nosubword)) (sem_F2:= sem_fun_full (wsw:=withsubword))).

Lemma psem_call_u (p:uprog) ev fn :
  wiequiv_f p p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
  apply (psem_call (sCP := fun wsw => sCP_unit (wsw := wsw))) => //=.
  move=> _ ??? [<-]; eexists; eauto.
  by split => //= x; rewrite !Vm.initP.
Qed.

Lemma psem_call_s (p:sprog) ev fn :
  wiequiv_f p p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof.
  apply (psem_call (sCP := fun wsw => sCP_stack (wsw := wsw))) => //=.
  clear.
  move=> fd scs mem s.
  rewrite /init_stk_state; t_xrbindP => mem' -> hw.
  have hsim : estate_sim {| escs := scs; emem := mem'; evm := Vm.init |}
                    {| escs := scs; emem := mem'; evm := Vm.init |}.
  + by split => //= ?; rewrite !Vm.initP.
  have [s' [hsim' hw']] := write_vars_sim hsim hw.
  by exists s'.
Qed.

End INSTANCE.
