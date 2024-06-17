(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import ssralg.

Require Import psem compiler_util lea_proof.

Require Import
  arch_decl
  arch_extra
  sem_params_of_arch_extra
  riscv_instr_decl
  riscv_decl
  riscv
  riscv_extra.
Require Export riscv_lower_addressing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** proofs
 * -------------------------------------------------------------------- *)

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {atoI : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {pT : progT}
  {sCP : semCallParams}.

Context (fresh_reg : string -> stype -> Ident.ident).
Context (p p' : prog).

Hypothesis ok_p' : lower_addressing_prog fresh_reg p = ok p'.

Context (ev : extra_val_t).

Lemma lower_addressing_prog_invariants :
  p.(p_globs) = p'.(p_globs) /\ p.(p_extra) = p'.(p_extra).
Proof.
  move: ok_p'; rewrite /lower_addressing_prog.
  by t_xrbindP=> _ _ <- /=.
Qed.

(* For convenience in this file, we prove this trivial corollary. *)
#[local]
Lemma eq_globs :
  p.(p_globs) = p'.(p_globs).
Proof. by have [? _] := lower_addressing_prog_invariants. Qed.

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
Proof.
  move=> fn fd get_fd.
  move: ok_p'; rewrite /lower_addressing_prog.
  t_xrbindP=> funcs ok_funcs <-.
  have [fd' ok_fd' get_fd'] := get_map_cfprog_gen ok_funcs get_fd.
  exists fd' => //.
  move: ok_fd'; rewrite /lower_addressing_fd.
  by t_xrbindP=> _ _ <- /=.
Qed.

Let Pi s1 i s2 :=
  forall (tmp : var_i) vm1,
    vtype tmp = sword Uptr ->
    ~ Sv.In tmp (read_I i) ->
    evm s1 =[\Sv.singleton tmp] vm1 ->
    exists2 vm2,
      sem p' ev (with_vm s1 vm1) (lower_addressing_i tmp i) (with_vm s2 vm2)
      & evm s2 =[\Sv.singleton tmp] vm2.

Let Pi_r s1 i s2 :=
  forall ii,
    Pi s1 (MkI ii i) s2.

Let Pc s1 c s2 :=
  forall (tmp : var_i) vm1,
    vtype tmp = sword Uptr ->
    ~ Sv.In tmp (read_c c) ->
    evm s1 =[\Sv.singleton tmp] vm1 ->
    exists2 vm2,
      sem p' ev (with_vm s1 vm1) (lower_addressing_c tmp c) (with_vm s2 vm2)
      & evm s2 =[\Sv.singleton tmp] vm2.

Let Pfor (i:var_i) zs s1 c s2 :=
  forall (tmp : var_i) vm1,
    vtype tmp = sword Uptr ->
    ~ Sv.In tmp (read_c c) ->
    evm s1 =[\Sv.singleton tmp] vm1 ->
    exists2 vm2,
      sem_for p' ev i zs (with_vm s1 vm1) (lower_addressing_c tmp c) (with_vm s2 vm2)
      & evm s2 =[\Sv.singleton tmp] vm2.

Let Pfun scs1 m1 fn vargs scs2 m2 vres :=
  sem_call p' ev scs1 m1 fn vargs scs2 m2 vres.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof.
  move=> s tmp vm1 _ _ eq_vm1; exists vm1 => //.
  by apply: Eskip.
Qed.

Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ Hu _ Hc tmp vm1 tmp_ty tmp_nin eq_vm1.
  have [tmp_nin1 tmp_nin2]: ~ Sv.In tmp (read_I i) /\ ~ Sv.In tmp (read_c c).
  + move: tmp_nin.
    rewrite read_c_cons.
    by move=> /Sv.union_spec /Decidable.not_or.
  have [vm2 hsem2 eq_vm2] := Hu tmp vm1 tmp_ty tmp_nin1 eq_vm1.
  have [vm3 hsem3 eq_vm3] := Hc tmp vm2 tmp_ty tmp_nin2 eq_vm2.
  exists vm3 => //.
  by apply (sem_app hsem2 hsem3).
Qed.

Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Proof. done. Qed.

(* TODO: move *)
Lemma write_lval_eq_ex wdb gd X x v s1 s2 vm1 :
  disjoint X (read_rv x) ->
  write_lval wdb gd x v s1 = ok s2 ->
  evm s1 =[\ X] vm1 ->
  exists2 vm2 : Vm.t,
    write_lval wdb gd x v (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    evm s2 =[\ X] vm2.
Proof.
  move=> hdisj hw eq_vm1.
  have eq_vm1' := eq_ex_disjoint_eq_on eq_vm1 hdisj.
  have [vm2 hw2 eq_vm2] := write_lval_eq_on1 eq_vm1' hw.
  exists vm2 => //.
  move=> y y_in.
  case: (Sv_memP y (vrv x)) => y_in'.
  + by apply eq_vm2.
  have /= <- := vrvP hw; last by clear -y_in'; SvD.fsetdec.
  have /= <- := vrvP hw2; last by clear -y_in'; SvD.fsetdec.
  by apply eq_vm1.
Qed.

(* TODO: move *)
Lemma write_lvals_eq_ex wdb gd X xs vs s1 s2 vm1 :
  disjoint X (read_rvs xs) ->
  write_lvals wdb gd s1 xs vs = ok s2 ->
  evm s1 =[\ X] vm1 ->
  exists2 vm2 : Vm.t,
    write_lvals wdb gd (with_vm s1 vm1) xs vs = ok (with_vm s2 vm2) &
    evm s2 =[\ X] vm2.
Proof.
  move=> hdisj hw eq_vm1.
  have eq_vm1' := eq_ex_disjoint_eq_on eq_vm1 hdisj.
  have [vm2 hw2 eq_vm2] := write_lvals_eq_on (@SvD.F.Subset_refl _) hw eq_vm1'.
  exists vm2 => //.
  move=> y y_in.
  case: (Sv_memP y (Sv.union (vrvs xs) (read_rvs xs))) => y_in'.
  + by apply eq_vm2.
  have /= <- := vrvsP hw; last by clear -y_in'; SvD.fsetdec.
  have /= <- := vrvsP hw2; last by clear -y_in'; SvD.fsetdec.
  by apply eq_vm1.
Qed.

Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s1 s2 x tag ty e v v' He htr Hw ii tmp vm1 _ tmp_nin eq_vm1 /=.
  have [hdisj1 hdisj2]:
    disjoint (Sv.singleton tmp) (read_rv x)
    /\ disjoint (Sv.singleton tmp) (read_e e).
  + rewrite 2!disjoint_singleton.
    move: tmp_nin; rewrite read_Ii read_i_assgn => {}tmp_nin.
    by split; apply /Sv_memP; clear -tmp_nin; SvD.fsetdec.
  have [vm2 Hw2 eq_vm2] := write_lval_eq_ex hdisj1 Hw eq_vm1.
  rewrite eq_globs in Hw2.
  exists vm2 => //.
  apply: sem_seq_ir; apply: Eassgn htr _ => //.
  rewrite -eq_globs.
  rewrite -(eq_on_sem_pexpr _ _ (s:=s1)) //=.
  by apply (eq_ex_disjoint_eq_on eq_vm1 hdisj2).
Qed.

Lemma shift_of_scaleP scale shift w :
  shift_of_scale scale = Some shift ->
  riscv_sll_semi w (wrepr U8 shift) = ok (wrepr Uptr scale * w)%R.
Proof.
  by case: scale => // -[|[|[]|]|] //= [<-]; rewrite /riscv_sll_semi wshl_sem.
Qed.

Lemma compute_addrP ii (tmp x:var_i) e prelude disp s1 wx we :
  get_var true (evm s1) x >>= to_pointer = ok wx ->
  sem_pexpr true p'.(p_globs) s1 e >>= to_pointer = ok we ->
  vtype tmp = sword Uptr ->
  compute_addr tmp x e = Some (prelude, disp) ->
  exists vm1 wtmp wdisp, [/\
    sem p' ev s1 (map (MkI ii) prelude) (with_vm s1 vm1),
    evm s1 =[\Sv.singleton tmp] vm1,
    get_var true vm1 tmp >>= to_pointer = ok wtmp,
    sem_pexpr true p'.(p_globs) (with_vm s1 vm1) disp >>= to_pointer = ok wdisp &
    (wx + we = wtmp + wdisp)%R].
Proof.
  move=> ok_wx ok_we tmp_ty.
  rewrite /compute_addr.
  move: disp => disp'.
  case hlea: mk_lea => [[disp base scale offset]|//] /=.
  case: base hlea => [base|//] hlea.
  case: offset hlea => [offset|//] hlea.
  case: eqP => [//|hneq] /=.
  case hshift: shift_of_scale => [shift|//].
  move=> [<- <-] {prelude disp'}.
  have lea_sem:
    sem_pexpr true p'.(p_globs) s1 (Papp2 (Oadd (Op_w Uptr)) (mk_lvar x) e) = ok (Vword (wx + we)).
  + move: ok_wx; t_xrbindP=> vx ok_vx ok_wx.
    move: ok_we; t_xrbindP=> ve ok_ve ok_we.
    rewrite /= /get_gvar /= ok_vx ok_ve /=.
    by rewrite /sem_sop2 /= ok_wx ok_we /=.
  have /(_ (cmp_le_refl _) (cmp_le_refl _)) := mk_leaP _ _ hlea lea_sem.
  rewrite zero_extend_u /sem_lea /=.
  (* t_xrbindP too aggressive *)
  apply: rbindP => wb.
  apply: rbindP => vb ok_vb ok_wb.
  apply: rbindP => wo.
  apply: rbindP => vo ok_vo ok_wo.
  move=> /ok_inj; rewrite GRing.addrC => {}lea_sem.

  eexists _, _, _; split.
  + apply: Eseq.
    + apply: EmkI; apply: Eopn.
      rewrite /sem_sopn /= wrepr_unsigned.
      rewrite /get_gvar /= ok_vo /=.
      rewrite /exec_sopn /= ok_wo /=.
      Local Opaque riscv_sll_semi.
      rewrite truncate_word_le //= zero_extend_wrepr //.
      rewrite /sopn_sem /= (shift_of_scaleP _ hshift) /=.
      Local Transparent riscv_sll_semi.
      by rewrite write_var_eq_type /=; first by reflexivity.
    apply: sem_seq_ir; apply: Eopn.
    rewrite /sem_sopn /=.
    rewrite /get_gvar /= get_var_eq tmp_ty /= cmp_le_refl orbT //.
    rewrite get_var_neq // ok_vb /=.
    rewrite /exec_sopn /= ok_wb /= truncate_word_u /=.
    by rewrite write_var_eq_type /with_vm /=; first by reflexivity.
  + do 2 (rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by move=> /Sv.singleton_spec).
    by apply eq_ex_refl.
  + rewrite /= get_var_eq tmp_ty /= cmp_le_refl orbT /=; last by [].
    by rewrite truncate_word_u; reflexivity.
  + by rewrite truncate_word_u wrepr_unsigned; reflexivity.
  done.
Qed.

Lemma is_one_LmemP xs al ws x e :
  is_one_Lmem xs = Some (al, ws, x, e) ->
  xs = [:: Lmem al ws x e].
Proof. by case: xs => [//|] [] // _ _ _ _ [] //= [-> -> -> ->]. Qed.

Lemma is_one_PloadP es al ws x e :
  is_one_Pload es = Some (al, ws, x, e) ->
  es = [:: Pload al ws x e].
Proof. by case: es => [//|] [] // _ _ _ _ [] //= [-> -> -> ->]. Qed.

(* TODO: move *)
Lemma sem_sopn_eq_ex X gd o xs es s1 s2 vm1 :
  disjoint X (Sv.union (read_rvs xs) (read_es es)) ->
  sem_sopn gd o s1 xs es = ok s2 ->
  evm s1 =[\X] vm1 ->
  exists2 vm2,
    sem_sopn gd o (with_vm s1 vm1) xs es = ok (with_vm s2 vm2) &
    evm s2 =[\X] vm2.
Proof.
  move=> hdisj hsem eq_vm1.
  have [hdisj1 hdisj2]:
    disjoint X (read_rvs xs) /\ disjoint X (read_es es).
  + by move: hdisj => /disjoint_sym /disjoint_union [/disjoint_sym ? /disjoint_sym ?].
  move: hsem; rewrite /sem_sopn.
  t_xrbindP=> vs2 vs1 ok_vs1 ok_vs2 ok_s2.
  have [vm2 ok_vm2 eq_vm2] := write_lvals_eq_ex hdisj1 ok_s2 eq_vm1.
  exists vm2 => //.
  rewrite -(eq_on_sem_pexprs _ _ (s:=s1)) //=; last first.
  + by apply (eq_ex_disjoint_eq_on eq_vm1 hdisj2).
  by rewrite ok_vs1 /= ok_vs2 /=.
Qed.

Local Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move=> s1 s2 t o xs es ok_s2 ii tmp vm1 tmp_ty tmp_nin eq_vm1 /=.

  have hdisj: disjoint (Sv.singleton tmp) (Sv.union (read_rvs xs) (read_es es)).
  + rewrite disjoint_singleton; apply /Sv_memP.
    by move: tmp_nin; rewrite read_Ii read_i_opn.
  have [vm2 hsem eq_vm2] := sem_sopn_eq_ex hdisj ok_s2 eq_vm1.
  rewrite eq_globs in hsem.
  have: [elaborate exists2 vm2,
    sem p' ev (with_vm s1 vm1) [:: MkI ii (Copn xs t o es)] (with_vm s2 vm2) &
    evm s2 =[\Sv.singleton tmp] vm2].
  + by exists vm2 => //; apply sem_seq_ir; apply Eopn.

  case hxs: is_one_Lmem => [[[[al ws] x] e]|].
  + move: hxs => /is_one_LmemP ?; subst xs.
    case hcompute: compute_addr => [[prelude disp]|//] _.
    move: hsem; rewrite /sem_sopn.
    t_xrbindP=> -[] // v [] /=; last by t_xrbindP.
    t_xrbindP=> vs ok_vs ok_v ? wx vx ok_vx ok_wx we ve ok_ve ok_we w ok_w
      m2 ok_m2 <- /= [eq_scs ??]; subst vm2 m2.
    have /(_ (with_vm s1 vm1) wx we) := compute_addrP ii _ _ tmp_ty hcompute.
    rewrite ok_vx ok_ve /= ok_wx ok_we.
    move=> /(_ erefl erefl) [vm1' [wtmp [wdisp [hsem1' eq_vm1' ok_wtmp ok_wdisp w_eq]]]].
    exists vm1'.
    + rewrite map_cat; apply (sem_app hsem1').
      apply: sem_seq_ir; apply: Eopn.
      rewrite /sem_sopn /=.
      rewrite -(eq_on_sem_pexprs _ _ (s:=with_vm s1 vm1)) //=; last first.
      + apply: (eq_ex_disjoint_eq_on eq_vm1').
        by move: hdisj => /disjoint_sym /disjoint_union [_ /disjoint_sym].
      rewrite ok_vs /= ok_v /=.
      move: ok_wtmp; t_xrbindP=> vtmp ok_vtmp ok_wtmp.
      move: ok_wdisp; t_xrbindP=> vdisp ok_vdisp ok_wdisp.
      rewrite ok_vtmp ok_vdisp /= ok_wtmp ok_wdisp /= ok_w /=.
      rewrite -w_eq ok_m2 /=.
      by rewrite /with_mem /with_vm /= eq_scs.
    by transitivity vm1.

  case hes: is_one_Pload => [[[[al ws] x] e]|//].
  move: hes => /is_one_PloadP ?; subst es.
  case hcompute: compute_addr => [[prelude disp]|//] _.
  move: hsem; rewrite /sem_sopn /=.
  t_xrbindP=> /= vs _ _ wx vx ok_vx ok_wx we ve ok_ve ok_we w ok_w <- <- ok_vs ok_vm2.
  have /(_ (with_vm s1 vm1) wx we) := compute_addrP ii _ _ tmp_ty hcompute.
  rewrite ok_vx ok_ve /= ok_wx ok_we.
  move=> /(_ erefl erefl) [vm1' [wtmp [wdisp [hsem1' eq_vm1' ok_wtmp ok_wdisp w_eq]]]].
  have hdisj1: disjoint (Sv.singleton tmp) (read_rvs xs).
  + by move: hdisj => /disjoint_sym /disjoint_union [/disjoint_sym ? _].
  have [vm1'' ok_vm1'' eq_vm1''] := write_lvals_eq_ex hdisj1 ok_vm2 eq_vm1'.
  exists vm1''.
  + rewrite map_cat; apply (sem_app hsem1').
    apply: sem_seq_ir; apply: Eopn.
    by rewrite /sem_sopn /= ok_wtmp ok_wdisp /= -w_eq ok_w /= ok_vs /= ok_vm1''.
  by transitivity vm2.
Qed.

Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
Proof.
  move=> s1 scs mem s2 o xs es ves vs hes ho hw ii tmp vm1 tmp_ty tmp_nin eq_vm1.
  have [hdisj1 hdisj2]:
    disjoint (Sv.singleton tmp) (read_rvs xs) /\
    disjoint (Sv.singleton tmp) (read_es es).
  + rewrite 2!disjoint_singleton.
    move: tmp_nin; rewrite read_Ii read_i_syscall => tmp_nin.
    split; apply /Sv_memP; clear -tmp_nin; SvD.fsetdec.
  have [vm2 hw2 eq_vm2] := write_lvals_eq_ex hdisj1 hw eq_vm1.
  rewrite eq_globs in hw2.
  exists vm2 => //.
  apply: sem_seq_ir; apply: (Esyscall _ (s1:=with_vm _ _) _ ho hw2).
  rewrite -eq_globs.
  rewrite -(eq_on_sem_pexprs _ _ (s:=s1)) //=.
  by apply (eq_ex_disjoint_eq_on eq_vm1 hdisj2).
Qed.

Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 He _ Hc1 ii tmp vm1 tmp_ty tmp_nin eq_vm1 /=.
  have tmp_nin1: ~ Sv.In tmp (read_c c1).
  + by move: tmp_nin; rewrite read_Ii read_i_if; clear; SvD.fsetdec.
  have [vm2 hsem2 eq_vm2] := Hc1 tmp vm1 tmp_ty tmp_nin1 eq_vm1.
  exists vm2 => //.
  apply: sem_seq_ir; apply: Eif_true => //.
  rewrite -eq_globs.
  rewrite -(eq_on_sem_pexpr _ _ (s:=s1)) //=.
  apply (eq_ex_disjoint_eq_on eq_vm1).
  rewrite disjoint_singleton; apply /Sv_memP.
  move: tmp_nin; rewrite read_Ii read_i_if; clear; SvD.fsetdec.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 He _ Hc2 ii tmp vm1 tmp_ty tmp_nin eq_vm1 /=.
  have tmp_nin2: ~ Sv.In tmp (read_c c2).
  + by move: tmp_nin; rewrite read_Ii read_i_if; clear; SvD.fsetdec.
  have [vm2 hsem2 eq_vm2] := Hc2 tmp vm1 tmp_ty tmp_nin2 eq_vm1.
  exists vm2 => //.
  apply: sem_seq_ir; apply: Eif_false => //.
  rewrite -eq_globs.
  rewrite -(eq_on_sem_pexpr _ _ (s:=s1)) //=.
  apply (eq_ex_disjoint_eq_on eq_vm1).
  rewrite disjoint_singleton; apply /Sv_memP.
  move: tmp_nin; rewrite read_Ii read_i_if; clear; SvD.fsetdec.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 s3 s4 a c e c' _ Hc He _ Hc' Hw1 Hw ii tmp vm1 tmp_ty tmp_nin eq_vm1.
  have tmp_nin1: ~ Sv.In tmp (read_c c).
  + by move: tmp_nin; rewrite read_Ii read_i_while; clear; SvD.fsetdec.
  have [vm2 hsem2 eq_vm2] := Hc tmp vm1 tmp_ty tmp_nin1 eq_vm1.
  have tmp_nin2: ~ Sv.In tmp (read_c c').
  + by move: tmp_nin; rewrite read_Ii read_i_while; clear; SvD.fsetdec.
  have [vm3 hsem3 eq_vm3] := Hc' tmp vm2 tmp_ty tmp_nin2 eq_vm2.
  have [vm4 hsem4 eq_vm4] := Hw ii tmp vm3 tmp_ty tmp_nin eq_vm3.
  exists vm4 => //=.
  apply: sem_seq_ir; apply: Ewhile_true.
  + by apply hsem2.
  + rewrite -eq_globs.
    rewrite -(eq_on_sem_pexpr _ _ (s:=s2)) //=.
    apply (eq_ex_disjoint_eq_on eq_vm2).
    rewrite disjoint_singleton; apply /Sv_memP.
    by move: tmp_nin; rewrite read_Ii read_i_while; clear; SvD.fsetdec.
  + by apply hsem3.
  by move: hsem4 => /= /sem_seq1_iff /sem_IE.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 a c e c' _ Hc He ii tmp vm1 tmp_ty tmp_nin eq_vm1.
  have tmp_nin1: ~ Sv.In tmp (read_c c).
  + by move: tmp_nin; rewrite read_Ii read_i_while; clear; SvD.fsetdec.
  have [vm2 hsem2 eq_vm2] := Hc tmp vm1 tmp_ty tmp_nin1 eq_vm1.
  exists vm2 => //=.
  apply: sem_seq_ir; apply: Ewhile_false => //.
  rewrite -eq_globs.
  rewrite -(eq_on_sem_pexpr _ _ (s:=s2)) //=.
  apply (eq_ex_disjoint_eq_on eq_vm2).
  rewrite disjoint_singleton; apply /Sv_memP.
  by move: tmp_nin; rewrite read_Ii read_i_while; clear; SvD.fsetdec.
Qed.

Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Proof.
  move=> s1 s2 i d lo hi c vlo vhi Hlo Hhi _ Hfor ii tmp vm1 tmp_ty tmp_nin eq_vm1.
  have tmp_nin': ~ Sv.In tmp (read_c c).
  + by move: tmp_nin; rewrite read_Ii read_i_for; clear; SvD.fsetdec.
  have [vm2 hsem2 eq_vm2] := Hfor tmp vm1 tmp_ty tmp_nin' eq_vm1.
  exists vm2 => //=.
  apply: sem_seq_ir; apply: Efor hsem2.
  + rewrite -eq_globs.
    rewrite -(eq_on_sem_pexpr _ _ (s:=s1)) //=.
    apply (eq_ex_disjoint_eq_on eq_vm1).
    rewrite disjoint_singleton; apply /Sv_memP.
    by move: tmp_nin; rewrite read_Ii read_i_for; clear; SvD.fsetdec.
  rewrite -eq_globs.
  rewrite -(eq_on_sem_pexpr _ _ (s:=s1)) //=.
  apply (eq_ex_disjoint_eq_on eq_vm1).
  rewrite disjoint_singleton; apply /Sv_memP.
  by move: tmp_nin; rewrite read_Ii read_i_for; clear; SvD.fsetdec.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof.
  by move=> s i c tmp vm1 tmp_ty tmp_nin eq_vm1; exists vm1 => //; constructor.
Qed.

(* TODO: move *)
Lemma write_var_eq_ex wdb X (x:var_i) v s1 s2 vm1 :
  write_var wdb x v s1 = ok s2 ->
  evm s1 =[\X] vm1 ->
  exists2 vm2,
    write_var wdb x v (with_vm s1 vm1) = ok (with_vm s2 vm2) &
    evm s2 =[\X] vm2.
Proof.
  move=> hw eq_vm1.
  have [vm2 hw2 eq_vm2] := write_var_eq_on1 vm1 hw.
  exists vm2 => //.
  move=> y y_in.
  case: (Sv_memP y (Sv.singleton x)) => y_in'.
  + by apply eq_vm2.
  have /= <- // := vrvP_var hw.
  have /= <- // := vrvP_var hw2.
  by apply eq_vm1.
Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  move => s1 s1' s2 s3 i w ws c Hw _ Hc _ Hf tmp vm1 tmp_ty tmp_nin eq_vm1.
  have [vm2 Hw2 eq_vm2] := write_var_eq_ex Hw eq_vm1.
  have [vm3 hsem3 eq_vm3] := Hc tmp vm2 tmp_ty tmp_nin eq_vm2.
  have [vm4 hsem4 eq_vm4] := Hf tmp vm3 tmp_ty tmp_nin eq_vm3.
  by exists vm4 => //; apply: EForOne Hw2 hsem3 hsem4.
Qed.

Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
Proof.
  move=> s1 scs2 m2 s2 xs fn args vargs vs Hargs Hcall Hfun Hvs
    ii tmp vm1 tmp_ty tmp_nin eq_vm1.
  have [hdisj1 hdisj2]:
    disjoint (Sv.singleton tmp) (read_rvs xs) /\
    disjoint (Sv.singleton tmp) (read_es args).
  + rewrite 2!disjoint_singleton.
    move: tmp_nin; rewrite read_Ii read_i_call => tmp_nin.
    by split; apply /Sv_memP; clear -tmp_nin; SvD.fsetdec.
  have [vm2 Hvs2 eq_vm2] := write_lvals_eq_ex hdisj1 Hvs eq_vm1.
  rewrite eq_globs in Hvs2.
  exists vm2 => //.
  apply: sem_seq_ir; apply: (Ecall (s1:=with_vm _ _) _ Hfun Hvs2).
  rewrite -eq_globs.
  rewrite -(eq_on_sem_pexprs _ _ (s:=s1)) //=.
  by apply (eq_ex_disjoint_eq_on eq_vm1 hdisj2).
Qed.

Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
Proof.
  move=> scs1 m1 sc2 m2 fn f vargs vargs' s0 s1 s2 vres vres'
    Hget Hargs Hi Hw _ Hc Hres Hfull Hscs Hfi.
  rewrite /Pfun.
  move: ok_p'; rewrite /lower_addressing_prog.
  set tmp := {| v_var := _; v_info := _ |}.
  t_xrbindP=> funcs ok_funcs ?; subst p'.
  have [f' ok_f' Hget'] := get_map_cfprog_gen ok_funcs Hget.
  move: ok_f'; rewrite /lower_addressing_fd.
  t_xrbindP=> /Sv_memP tmp_nin1 /Sv_memP tmp_nin2 ?; subst f'.
  have [vm2 hsem2 eq_vm2] := Hc tmp (evm s1) erefl tmp_nin1 (eq_ex_refl _).
  rewrite with_vm_same in hsem2.
  move: Hres.
  rewrite -(sem_pexprs_get_var _ p.(p_globs)).
  rewrite (eq_on_sem_pexprs _ (s' := with_vm s2 vm2)) //=; last first.
  + apply: (eq_ex_disjoint_eq_on eq_vm2).
    rewrite disjoint_singleton; apply /Sv_memP.
    by rewrite vars_l_read_es.
  rewrite sem_pexprs_get_var => Hres.
  by apply: EcallRun; eassumption.
Qed.

Lemma lower_addressing_progP scs mem f va scs' mem' vr:
  sem_call p ev scs mem f va scs' mem' vr ->
  sem_call p' ev scs mem f va scs' mem' vr.
Proof.
  exact:
    (sem_call_Ind
       Hskip
       Hcons
       HmkI
       Hassgn
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
       Hproc).
Qed.

End WITH_PARAMS.
