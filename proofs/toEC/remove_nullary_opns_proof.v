From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import psem.
Require Export remove_nullary_opns.

Section REMOVE_NULLARY_OPNS_PROOF.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE0 : EventRels E0}
.

#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.

Context
  (p p' : uprog)
  (ev : extra_val_t)
  (remove_nullary_opns_ok : remove_nullary_opns_prog p = p')
.

Lemma remove_nullary_opns_eq_globs : p_globs p = p_globs p'.
Proof using remove_nullary_opns_ok. by rewrite -remove_nullary_opns_ok. Qed.

#[local] Instance remove_nullary_opns_checker_st_eqP :
  Checker_eq p p' checker_st_eq := checker_st_eqP remove_nullary_opns_eq_globs.

#[local] Instance remove_nullary_opns_checker_a_st_eqP :
  Checker_a_eq p p' checker_a_st_eq := checker_a_st_eqP remove_nullary_opns_eq_globs.

#[local] Hint Resolve
  remove_nullary_opns_checker_st_eqP remove_nullary_opns_checker_a_st_eqP : core.

Lemma write_lvals_nilP wdb gd (s s' : estate) (vs : values) :
  write_lvals wdb gd s [::] vs = ok s' -> s' = s.
Proof.
rewrite /write_lvals /=; case: vs => [|v vs] //=.
by move=> [<-].
Qed.

Lemma sem_sopn_nilP gd o s es s' :
  sem_sopn gd o s [::] es = ok s' -> s' = s.
Proof.
rewrite /sem_sopn; t_xrbindP => vs hvs res hres.
exact: write_lvals_nilP.
Qed.

Let Pi (i : instr) :=
  wequiv_rec p p' ev ev eq_spec (st_eq tt)
    [:: i] (remove_nullary_opns_i i) (st_eq tt).

Let Pi_r (i : instr_r) := forall ii, Pi (MkI ii i).

Let Pc (c : cmd) :=
  wequiv_rec p p' ev ev eq_spec (st_eq tt)
    c (remove_nullary_opns_c remove_nullary_opns_i c) (st_eq tt).

Lemma remove_nullary_opns_cP c : Pc c.
Proof using E Pc Pi Pi_r asm_op dc ep ev p p' rE0
  remove_nullary_opns_ok sip spp syscall_state wE wsw.
apply: (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => // {c}.
- by apply wequiv_nil.
- move=> i c hi hc /=.
  rewrite -cat1s.
  by apply wequiv_cat with (st_eq tt); [exact hi | exact hc].
- by move=> >; apply wequiv_assgn_rel_eq with checker_st_eq tt.
- move=> xs t o es ii /=.
  case: xs => [ | x xs] /=; last first.
  + by apply wequiv_opn_rel_eq with checker_st_eq tt.
  apply wequiv_opn_esem => s u [hscs hmem hvm] s' hsem /=.
  exists u; first done.
  by rewrite (sem_sopn_nilP hsem).
- by move=> >; apply wequiv_syscall_rel_eq with checker_st_eq tt.
- by move=> a ii /=; apply wequiv_assert_rel_eq with checker_a_st_eq.
- by move=> e c1 c2 hc1 hc2 ii /=; apply wequiv_if_rel_eq with checker_st_eq tt tt tt.
- by move=> v dir lo hi c hc ii /=; apply wequiv_for_rel_eq with checker_st_eq tt tt.
- by move=> al c1 e inf c2 hc1 hc2 ii /=;
    apply wequiv_while_rel_eq with checker_st_eq tt.
move=> xs f es ii /=.
apply wequiv_call_rel_eq with checker_st_eq tt => //.
move=> ?? <-; exact/wequiv_fun_rec.
Qed.

Lemma get_fundef_remove_nullary_opns fn :
  get_fundef (p_funcs (remove_nullary_opns_prog p)) fn =
    omap remove_nullary_opns_fd (get_fundef (p_funcs p) fn).
Proof.
rewrite /get_fundef /remove_nullary_opns_prog /=.
by elim: (p_funcs p) => [|[fn' fd'] pfuns ih] //=; case: eqP.
Qed.

Lemma remove_nullary_opns_proof fn :
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using remove_nullary_opns_ok.
apply wequiv_fun_ind => {}fn _ fs _ [<- <-] fd hget.
exists (remove_nullary_opns_fd fd).
- by rewrite -remove_nullary_opns_ok get_fundef_remove_nullary_opns hget.
move=> s11 hinit.
exists s11.
- by apply: (eq_initialize _ _ _ _ hinit) => //; rewrite -remove_nullary_opns_ok.
exists (st_eq tt), (st_eq tt); split=> //.
- apply remove_nullary_opns_cP.
exact: (st_eq_finalize erefl erefl erefl).
Qed.

End REMOVE_NULLARY_OPNS_PROOF.
