Require Import psem psem_facts.
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
  move=> hsim /set_varP [hdb /dup []htr /truncatable_sim htr' ->].
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

Let Pc s1 c s2 : Prop :=
  ∀ s1',
    estate_sim s1 s1' →
    ∃ s2',
      estate_sim s2 s2' ∧ sem p ev s1' c s2'.

Let Pi_r s1 i s2 : Prop :=
  ∀ s1',
    estate_sim s1 s1' →
    ∃ s2',
      estate_sim s2 s2' ∧ sem_i p ev s1' i s2'.

Let Pi s1 i s2 : Prop :=
  ∀ s1',
    estate_sim s1 s1' →
    ∃ s2',
      estate_sim s2 s2' ∧ sem_I p ev s1' i s2'.

Let Pfor x ws s1 c s2 : Prop :=
  ∀ s1',
    estate_sim s1 s1' →
    ∃ s2',
      estate_sim s2 s2' ∧ sem_for p ev x ws s1' c s2'.

Let Pfun := sem_call (wsw:= withsubword) p ev.

Lemma psem_call scs m fn va scs' m' vr :

  (forall scs1 scs2 mem1 mem2 o ves vs,
    exec_syscall (wsw:= nosubword)   scs1 mem1 o ves = ok (scs2, mem2, vs) ->
    exec_syscall (wsw:= withsubword) scs1 mem1 o ves = ok (scs2, mem2, vs)) ->

  (forall fd scs mem s,
    init_state (f_extra fd) (p_extra p) ev {| escs := scs; emem := mem; evm := Vm.init |} = ok s ->
    exists2 s',
      init_state (f_extra fd) (p_extra p) ev {| escs := scs; emem := mem; evm := Vm.init |} = ok s' &
      estate_sim s s') ->

  (forall fd mem, finalize (wsw:= nosubword) (f_extra fd) mem = finalize (wsw:= withsubword) (f_extra fd) mem) ->

  sem_call (wsw:= nosubword) p ev scs m fn va scs' m' vr →
  sem_call (wsw:= withsubword) p ev scs m fn va scs' m' vr.
Proof.
move=> hsyscall hinitstate hfinal.
apply:
  (sem_call_Ind
     (Pc := Pc)
     (Pi_r := Pi_r)
     (Pi := Pi)
     (Pfor := Pfor)
     (Pfun := Pfun))
  => {m fn va m' vr}.
- by move => s s' hss'; exists s'; split; first exact: hss'; constructor.
- move => s1 s2 s3 [ii i] c [] {ii i s1 s2} ii i s1 s2 _ ihi _ ihc s1' hss'1.
  case: (ihi s1' hss'1) => s2' [hss'2 hi].
  case: (ihc s2' hss'2) => s3' [hss'3 hc].
  by exists s3'; split; first exact: hss'3; econstructor; eauto.
- move => ii i s1 s2 _ ih s1' hss'1.
  case: (ih s1' hss'1) => s2' [hss'2 hi].
  by exists s2'; split; first exact: hss'2; constructor.
- move => s1 s2 x tg ty e v1 v2 hv1 hv2 hw s1' hss'1.
  have hv1' := sem_pexpr_sim hss'1 hv1.
  case: (write_lval_sim hss'1 hw) => s2' [hss'2 hw'].
  exists s2'; split; first exact: hss'2.
  by econstructor; eauto.
- move => s1 s2 tg op xs es; rewrite /sem_sopn; t_xrbindP => vr va /sem_pexprs_sim hva hvr /write_lvals_sim hw s1' hss'1.
  case: (hw _ hss'1) => s2' [hss'2 hw']; exists s2'; split; first exact: hss'2.
  econstructor; eauto.
  by rewrite /sem_sopn (hva) //= hvr.
- move=> s1 scs1 m1 s2 o xs es ves vs hes ho hw s1' hss'1.
  have hes' := sem_pexprs_sim hss'1 hes.
  have /= hss':= estate_sim_scs scs1 (estate_sim_mem m1 hss'1).
  have [s2' [??]]:= write_lvals_sim hss' hw.
  exists s2'; split => //.
  econstructor; eauto.
  by case: hss'1 => <- <- ?; apply hsyscall.
- move => s1 s2 e th el /sem_pexpr_sim he _ ih s1' hss'1.
  case: (ih _ hss'1) => s2' [hss'2 hth].
  exists s2'; split; first exact hss'2.
  once (econstructor; eauto; fail).
- move => s1 s2 e th el /sem_pexpr_sim he _ ih s1' hss'1.
  case: (ih _ hss'1) => s2' [hss'2 hel].
  exists s2'; split; first exact hss'2.
  once (econstructor; eauto; fail).
- move => s1 s2 s3 s4 a c e c' _ ih /sem_pexpr_sim he _ ih' _ ihwh s1' hss'1.
  case: (ih _ hss'1) => s2' [hss'2 hc].
  case: (ih' _ hss'2) => s3' [hss'3 hcc'].
  case: (ihwh _ hss'3) => s4' [hss'4 hwh].
  exists s4'; split; first exact: hss'4.
  once (econstructor; eauto; fail).
- move => s1 s2 a c e c' _ ih /sem_pexpr_sim he s1' hss'1.
  case: (ih _ hss'1) => s2' [hss'2 hc].
  exists s2'; split; first exact: hss'2.
  once (econstructor; eauto; fail).
- move => s1 s2 x d lo hi c vlo vhi /sem_pexpr_sim hlo /sem_pexpr_sim hhi _ ih s1' hss'1.
  case: (ih _ hss'1) => s2' [hss'2 hc].
  exists s2'; split; first exact: hss'2.
  once (econstructor; eauto; fail).
- by move => s1 x c s1' hss'1; exists s1'; split => //; constructor.
- move => s1 s2 s3 s4 x w ws c /write_var_sim hw _ ih _ ih' s1' hss'1.
  case: (hw _ hss'1) => s2' [hss'2 hw'].
  case: (ih _ hss'2) => s3' [hss'3 hc].
  case: (ih' _ hss'3) => s4' [hss'4 hf].
  exists s4'; split; first exact: hss'4.
  econstructor; eauto.
- move=> s1 scs2 m2 s2 xs fn args vargs vs
    /sem_pexprs_sim hargs _ ih /write_lvals_sim hres s1' [hscs hm hvm].
  rewrite hscs hm in ih.
  case: (hres (with_scs (with_mem s1' m2) scs2) (And3 erefl erefl hvm)) => s2' [hss'2 hw].
  exists s2'; split; first exact: hss'2.
  econstructor; eauto.
  by apply: hargs; split.
move => scs1 m scs2 m2 fn fd va va' s0 s1 s2 vr vr' hfn htyin /hinitstate [s0' hinit hsim].
move=> /(write_vars_sim hsim) [s1' [hss'1 hargs]].
move=> _ /(_ _ hss'1) [[scs2' m2' vm2']] [] [] /= <- <- {scs2' m2'} hvm ih.
rewrite /get_var_is (mapM_ext (λ (x : var_i) _, get_var_sim hvm x)) hfinal
  => hres htyout -> ->.
econstructor; eauto.
Qed.

End PROOF.

Section INSTANCE.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

Lemma psem_call_u (p:uprog) scs m fn va scs' m' vr :
  sem_call (wsw:= nosubword)   p tt scs m fn va scs' m' vr →
  sem_call (wsw:= withsubword) p tt scs m fn va scs' m' vr.
Proof.
  apply (psem_call (sCP := fun wsw => sCP_unit (wsw := wsw))) => //=.
  move=> _ ??? [<-]; eexists; eauto.
  by split => //= x; rewrite !Vm.initP.
Qed.

Lemma psem_call_s (p:sprog) ev scs m fn va scs' m' vr :
  sem_call (wsw:= nosubword)   p ev scs m fn va scs' m' vr →
  sem_call (wsw:= withsubword) p ev scs m fn va scs' m' vr.
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
