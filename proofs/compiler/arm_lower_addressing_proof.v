(* ** Imports and settings *)
From ITree Require Import ITree ITreeFacts.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import ssralg.

Require Import psem psem_facts compiler_util lea_proof xrutt xrutt_facts it_sems_core_defs.

Require Import
  arch_decl
  arch_extra
  sem_params_of_arch_extra
  arm_decl
  arm_instr_decl
  arm_extra.

Require Export arm_lower_addressing.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

(* ** proofs
 * -------------------------------------------------------------------- *)

Section WITH_PARAMS.

#[local] Existing Instance progStack.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {atoI : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {sCP : semCallParams}.

Context (fresh_reg : string -> atype -> Ident.ident).

Context (p p' : sprog).

Hypothesis ok_p' : arm_lower_addressing_prog fresh_reg p = ok p'.

Context (ev : extra_val_t).

Lemma lower_addressing_prog_invariants :
  p.(p_globs) = p'.(p_globs) /\ p.(p_extra) = p'.(p_extra).
Proof using ok_p'.
  move: ok_p'; rewrite /arm_lower_addressing_prog.
  by t_xrbindP=> _ _ <- /=.
Qed.

#[local]
Lemma eq_globs :
  p.(p_globs) = p'.(p_globs).
Proof using ok_p'. by have [? _] := lower_addressing_prog_invariants. Qed.

Lemma lower_addressing_fd_invariants :
  forall fn fd,
  get_fundef p.(p_funcs) fn = Some fd ->
  exists2 fd',
    get_fundef p'.(p_funcs) fn = Some fd' &
    [/\ fd.(f_info) = fd'.(f_info),
        fd.(f_tyin) = fd'.(f_tyin),
        fd.(f_params) = fd'.(f_params),
        fd.(f_tyout) = fd'.(f_tyout),
        fd.(f_res) = fd'.(f_res) &
        fd.(f_extra) = fd'.(f_extra)].
Proof using ok_p'.
  move=> fn fd get_fd.
  move: ok_p'; rewrite /arm_lower_addressing_prog.
  t_xrbindP=> funcs ok_funcs <-.
  have [fd' ok_fd' get_fd'] := get_map_cfprog_gen ok_funcs get_fd.
  exists fd' => //.
  move: ok_fd'; rewrite /lower_addressing_fd.
  by t_xrbindP=> _ _ <- /=.
Qed.

Let sip := sip_of_asm_e.

(* The address computation assigns the pointer to [y]. *)
Lemma glob_addr_semP (y : var_i) e s pa :
  sem_pexpr true p'.(p_globs) s e >>= to_pointer = ok pa ->
  vtype y = aword Uptr ->
  sem_sopn p'.(p_globs) (Oasm (ExtOp Oarm_glob_addr)) s [:: Lvar y] [:: e]
  = ok (with_vm s (evm s).[y <- Vword pa]).
Proof.
  t_xrbindP=> ve ok_ve ok_pa hty.
  rewrite /sem_sopn /= ok_ve /= /exec_sopn /= ok_pa /=.
  by rewrite write_var_eq_type //= hty.
Qed.

Lemma lower_glob_loadP rip tmp s1 s2 t o xs es ii c X :
  lower_glob_load rip tmp xs t o es = Some c ->
  sem_sopn (p_globs p') o s1 xs es = ok s2 ->
  vtype tmp = aword Uptr ->
  ~ Sv.In tmp X -> Sv.Subset (Sv.union (read_rvs xs) (read_es es)) X ->
  exists2 vm2,
    esem p' ev (map (MkI ii) c) s1 = ok (with_vm s2 vm2) & evm s2 =[X] vm2.
Proof using dc.
  rewrite /lower_glob_load.
  case: o => // -[] // -[] // -[] // -[] mn opts.
  case: is_load_mn => //.
  case: es => // -[] // al ws e es'.
  case: is_glob_addr => //.
  case: es' => [ | c' es'].
  (* [x = [e]] becomes [x = e; x = [x]]. *)
  + case: xs => // -[] // x [] //; case: eqP => // hxty [<-].
    rewrite /sem_sopn /=.
    t_xrbindP => vs _ _ pa ve ok_ve ok_pa w ok_w <- <- ok_vs ok_s2 _ _ _.
    have h : sem_pexpr true (p_globs p') s1 e >>= to_word arm_reg_size = ok pa.
    + by rewrite ok_ve.
    move: (glob_addr_semP h hxty); rewrite /sem_sopn => -> /=.
    rewrite /get_gvar /= get_var_eq hxty /= cmp_le_refl orbT //= truncate_word_u /=.
    rewrite ok_w /= ok_vs /=.
    move: ok_s2; case: vs ok_vs => [ | v [ | v' vs]] ok_vs //=; last by t_xrbindP.
    t_xrbindP => s2' /write_varP [-> hdb htr] <-.
    rewrite (write_var_truncate hdb htr) /=.
    exists ((evm s1).[x <- Vword pa]).[x <- v]; first by rewrite with_vm_idem.
    by move=> z _; rewrite /= !Vm.setP; case: eqP.
  (* [xs = [e], es] becomes [tmp = e; xs = [tmp], es]. *)
  move=> [<-]; rewrite /sem_sopn /=.
  t_xrbindP => vs _ _ pa ve ok_ve ok_pa w ok_w <- _ vc ok_vc ves ok_ves <- <- ok_vs ok_s2
    tmp_ty tmp_nin hsub.
  have h : sem_pexpr true (p_globs p') s1 e >>= to_word arm_reg_size = ok pa.
  + by rewrite ok_ve.
  move: (glob_addr_semP h tmp_ty); rewrite /sem_sopn => -> /=.
  set vm1 := (evm s1).[tmp <- _].
  have eqX : evm s1 =[X] vm1.
  + by move=> z hz; rewrite Vm.setP_neq //; apply/eqP => ?; subst z.
  move: hsub; rewrite !read_es_cons => hsub.
  rewrite /get_gvar /= get_var_eq tmp_ty /= cmp_le_refl orbT //= truncate_word_u /=.
  rewrite ok_w /=.
  have -> : sem_pexpr true (p_globs p') (with_vm s1 vm1) c' = ok vc.
  + rewrite -ok_vc; symmetry; apply: eq_on_sem_pexpr => //.
    by apply: eq_onI eqX; clear -hsub; SvD.fsetdec.
  have -> : sem_pexprs true (p_globs p') (with_vm s1 vm1) es' = ok ves.
  + rewrite -ok_ves; symmetry; apply: eq_on_sem_pexprs => //.
    by apply: eq_onI eqX; clear -hsub; SvD.fsetdec.
  rewrite /= ok_vs /=.
  have hex : evm s1 =[\ Sv.singleton tmp] vm1.
  + move=> z hz; rewrite Vm.setP_neq //; apply/eqP => ?; subst z.
    by apply hz; SvD.fsetdec.
  have [|vm2 -> heq2] := write_lvals_eq_ex _ ok_s2 hex.
  + apply/disjointP => z /Sv.singleton_spec ? hz; subst z.
    by apply tmp_nin; clear -hsub hz; SvD.fsetdec.
  exists vm2 => // z hz; apply heq2 => /Sv.singleton_spec ?; subst z.
  exact: tmp_nin hz.
Qed.

Lemma Hopn_aux rip (tmp : var_i) (s1 s2 : estate) t o xs es ii vm1 X :
  sem_sopn (p_globs p) o s1 xs es = ok s2 ->
  vtype tmp = aword Uptr ->
  ~ Sv.In tmp X -> Sv.Subset (read_I (MkI ii (Copn xs t o es))) X ->
  evm s1 =[X] vm1 ->
  exists2 vm2 : Vm.t,
    esem p' ev (lower_addressing_i rip tmp (MkI ii (Copn xs t o es))) (with_vm s1 vm1)
    = ok (with_vm s2 vm2) &
    evm s2 =[X] vm2.
Proof using dc ok_p'.
  rewrite !read_writeE => ok_s2 tmp_ty tmp_nin hsub eq_vm1 /=.
  have [vm2 hsem eq_vm2] :
     exists2 vm2 : Vm.t,
       sem_sopn (p_globs p) o (with_vm s1 vm1) xs es = ok (with_vm s2 vm2)
       & evm s2 =[X] vm2.
  + move: ok_s2; rewrite /sem_sopn; t_xrbindP => vs vr hes hex hw.
    have [|vm2 hw2 heq2] := write_lvals_eq_on _ hw eq_vm1; first by clear -hsub; SvD.fsetdec.
    exists vm2; last by apply: eq_onI heq2; clear; SvD.fsetdec.
    rewrite  -(read_es_eq_on _ _ (s := X)) //; last first.
    + by move=> z;rewrite read_esE => hz;apply eq_vm1; clear -hsub hz; SvD.fsetdec.
    by rewrite hes /= hex /= hw2.
  rewrite eq_globs in hsem.
  case hlow: lower_glob_load => [c | ]; last by exists vm2 => //=; rewrite LetK.
  have [|vm3 hsem3 eq_vm3] := lower_glob_loadP ii hlow hsem tmp_ty tmp_nin.
  + by clear -hsub; SvD.fsetdec.
  exists vm3; first by rewrite hsem3 with_vm_idem.
  by apply: eq_onT eq_vm2 eq_vm3.
Qed.

Section IT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE0 : EventRels E0}.

#[ local ]
Lemma checker_st_eq_onP_ : Checker_eq p p' checker_st_eq_on.
Proof using ok_p'. apply checker_st_eq_onP; apply eq_globs. Qed.
#[local] Hint Resolve checker_st_eq_onP_ : core.

Lemma it_lower_addressing_progP fn:
  wiequiv_f p p' ev ev (rpreF (eS:=eq_spec)) fn fn (rpostF (eS:=eq_spec)).
Proof using ok_p'.
  apply wequiv_fun_ind => {}fn _ fs _ [<-] <- fd hget.
  move: ok_p'; rewrite /arm_lower_addressing_prog.
  set rip := {| vtype := _; vname := _ |}.
  set tmp := {| v_var := _; v_info := _ |}.
  t_xrbindP=> funcs ok_funcs hp'.
  have [f' ok_f' hget'] := get_map_cfprog_gen ok_funcs hget.
  move: ok_f'; rewrite /lower_addressing_fd.
  t_xrbindP=> /Sv_memP tmp_nin1 /Sv_memP tmp_nin2 ?; subst f'.
  set X := Sv.union (read_c (f_body fd)) (vars_l (f_res fd)).
  have tmp_nin : ~Sv.In tmp X by rewrite /X; clear -tmp_nin1 tmp_nin2; SvD.fsetdec.
  have htytmp : vtype tmp = aword Uptr by [].
  rewrite -{1}hp' /=; eexists; first by eauto.
  move => s.
  set c' := lower_addressing_c rip tmp (f_body fd).
  move=> /(eq_initialize (sip:= sip) (p':=p') (fd':=with_body fd c')) -> //; last by rewrite -hp'.
  exists s; first reflexivity.
  exists (st_eq_on X), (st_eq_on X).
  split => //=; last first.
  + apply wrequiv_weaken with (st_eq_on (vars_l (f_res fd))) eq => //.
    + by apply st_rel_weaken => ??; apply eq_onI; rewrite /= /X; clear; SvD.fsetdec.
    by apply: (st_eq_on_finalize (fd':=with_body fd c')).
  clear ok_funcs funcs fs fn hget' tmp_nin1 tmp_nin2 s hp' hget; subst c'.
  have : Sv.Subset (read_c (f_body fd)) X by rewrite /X; clear; SvD.fsetdec.
  move: rip tmp X tmp_nin htytmp (f_body fd) => rip tmp X tmp_nin htytmp {fd}.
  set Pi := fun i =>
    Sv.Subset (read_I i) X ->
    wequiv_rec (sip:=sip) p p' ev ev eq_spec (st_eq_on X) [::i] (lower_addressing_i rip tmp i) (st_eq_on X).
  set Pi_r := fun i => forall ii, Pi (MkI ii i).
  set Pc := fun c =>
    Sv.Subset (read_c c) X ->
    wequiv_rec (sip:=sip) p p' ev ev eq_spec (st_eq_on X) c (lower_addressing_c rip tmp c) (st_eq_on X).
  apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => //; subst Pi_r Pi Pc => /=.
  + by move=> hsub /=; apply (wequiv_nil (sip:=sip)).
  + move=> i c hi hc; rewrite read_writeE => hsub.
    rewrite -cat1s.
    apply (wequiv_cat (sip:=sip)) with (st_eq_on X).
    + by apply hi => //; clear -hsub; SvD.fsetdec.
    apply hc; last by clear -hsub; SvD.fsetdec.
  + move=> x tg ty e ii; rewrite !read_writeE => hsub.
    apply (wequiv_assgn_rel_eq (sip:=sip)) with checker_st_eq_on X => //.
    + by split => //; rewrite /read_es /= read_eE; clear -hsub; SvD.fsetdec.
    split => //; first by clear; SvD.fsetdec.
    by rewrite /read_rvs /= read_rvE; clear -hsub; SvD.fsetdec.
  + move=> xs tg o es ii hsub.
    apply (wequiv_opn_esem (sip:=sip)) => s t s' /st_relP [-> /= heq] hopn.
    have [vm2 h ?] := @Hopn_aux rip tmp _ _ _ _ _ _ _ _ _ hopn htytmp tmp_nin hsub heq.
    by exists (with_vm s' vm2).
  + move=> xs sc es ii; rewrite !read_writeE => hsub.
    by apply (wequiv_syscall_rel_eq (sip:=sip)) with checker_st_eq_on X => //=; split=> //; clear -hsub; SvD.fsetdec.
  (* Assertions are not allowed: both sides fail. *)
  + move=> a ii _ s1 s2 _ /=.
    rewrite /isem_assert /= !bind_throw; apply xrutt_CutL => //.
    by rewrite /core_logics.errcutoff /is_error /subevent /resum /fromErr mid12.
  + move=> e c1 c2 hc1 hc2 ii; rewrite !read_writeE => hsub.
    apply (wequiv_if_rel_eq (sip:=sip)) with checker_st_eq_on X X X => //.
    + by split => //; rewrite /read_es /= read_eE; clear -hsub; SvD.fsetdec.
    + by apply hc1; clear -hsub; SvD.fsetdec.
    by apply hc2; clear -hsub; SvD.fsetdec.
  + move=> x dir lo hi c hc ii; rewrite !read_writeE => hsub.
    apply (wequiv_for_rel_eq (sip:=sip)) with checker_st_eq_on X X => //.
    + by split => //; rewrite /read_es /= !read_eE; clear -hsub; SvD.fsetdec.
    + by split => //; rewrite /read_rvs /=; clear; SvD.fsetdec.
    by apply hc => //; clear -hsub; SvD.fsetdec.
  + move=> a c1 e ii' c2 hc1 hc2 ii; rewrite !read_writeE => hsub.
    apply (wequiv_while_rel_eq (sip:=sip)) with checker_st_eq_on X => //.
    + by split => //; rewrite /read_es /= !read_eE; clear -hsub; SvD.fsetdec.
    + by apply hc1 => //; clear -hsub; SvD.fsetdec.
    by apply hc2 => //; clear -hsub; SvD.fsetdec.
  move=> xs fn es ii; rewrite !read_writeE => hsub.
  apply (wequiv_call_rel_eq (sip:=sip)) with checker_st_eq_on X => //.
  + by split => //; clear -hsub; SvD.fsetdec.
  + by split => //; clear -hsub; SvD.fsetdec.
  by move=> ???; apply: (wequiv_fun_rec (spec := eq_spec)).
Qed.

End IT.

End WITH_PARAMS.
