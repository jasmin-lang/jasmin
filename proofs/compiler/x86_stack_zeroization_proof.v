From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import Lia.

Require Import seq_extra.
Require Import
  expr
  fexpr
  fexpr_sem
  linear
  linear_sem
  linear_facts
  psem
  psem_facts
  low_memory.
Require stack_zeroization_proof.
Require Import
  arch_decl
  arch_extra
  sem_params_of_arch_extra.
Require Import
  x86_decl
  x86_extra
  x86_instr_decl.
Require Export x86_stack_zeroization.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* FIXME: We should use the higher-level [eval_lsem] lemmas. *)
Section FIXME.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {sip : SemInstrParams asm_op syscall_state}.

#[local]
Lemma find_instr_skip p fn P Q :
  is_linear_of p fn (P ++ Q) ->
  forall scs m vm n,
  find_instr p (Lstate scs m vm fn (size P + n)) = oseq.onth Q n.
Proof. by eauto using find_instr_skip'. Qed.

End FIXME.


#[local] Existing Instance withsubword.

Section STACK_ZEROIZATION.

Context {atoI : arch_toIdent} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.
Context {call_conv : calling_convention}.

Section RSP.

Context (rspn : Ident.ident).
Let rspi := vid rspn.

Let vlocal {t T} {_ : ToString t T} {_ : ToIdent T} (x : T) : gvar :=
  mk_lvar (mk_var_i (to_var x)).

Let tmp : gvar := vlocal RSI.
Let off : gvar := vlocal RDI.
Let vlr : gvar := vlocal XMM2.

Let rsp : gvar := mk_lvar rspi.
Let zf : gvar := vlocal ZF.
Let tmpi : var_i := gv tmp.
Let offi : var_i := gv off.
Let vlri : var_i := gv vlr.
Let zfi : var_i := gv zf.

Context (lp : lprog) (fn : funname) (lfd : lfundef) (lc : lcmd).
Context (ws_align : wsize) (ws : wsize) (stk_max : Z).
Context (lt_0_stk_max : (0 < stk_max)%Z).
Context (halign : is_align stk_max ws).
Context (le_ws_ws_align : (ws <= ws_align)%CMP).
Context (hlfd : get_fundef lp.(lp_funcs) fn = Some lfd).
Context (ptr : pointer).
Context (hstack : (stk_max <= wunsigned (align_word ws_align ptr))%Z).
Let top := (align_word ws_align ptr - wrepr Uptr stk_max)%R.

Local Lemma top_aligned : is_align top ws.
Proof.
  rewrite /top.
  apply is_align_add.
  + apply (is_align_m le_ws_ws_align).
    by apply do_align_is_align.
  move: halign; rewrite -WArray.arr_is_align => /is_align_addE <-.
  by rewrite GRing.addrN.
Qed.

Record state_rel_unrolled_small vars s1 s2 n (p:word Uptr) := {
  sr_scs : s1.(escs) = s2.(escs);
  sr_mem : mem_equiv s1.(emem) s2.(emem);
  sr_mem_valid : forall p, between top stk_max p U8 -> validw s2.(emem) Aligned p U8;
  sr_disjoint :
    forall p, disjoint_zrange top stk_max p (wsize_size U8) ->
      read s1.(emem) Aligned p U8 = read s2.(emem) Aligned p U8;
  sr_zero : forall p,
    between (top + wrepr _ n) (stk_max - n) p U8 -> read s2.(emem) Aligned p U8 = ok 0%R;
  sr_vm : s1.(evm) =[\ Sv.add rspi vars] s2.(evm) ;
  sr_tmp : s2.(evm).[tmpi] = Vword ptr;
  sr_rsp : s2.(evm).[rspi] = Vword p;
  sr_aligned : is_align n ws;
  sr_bound : (0 <= n <= stk_max)%Z;
}.

Record state_rel_unrolled_large vars s1 s2 n p := {
  srul_vlr : s2.(evm).[vlri] = @Vword ws 0;
  srul_srs :> state_rel_unrolled_small vars s1 s2 n p
}.

Record state_rel_loop_small vars s1 s2 n p := {
  srls_off : s2.(evm).[offi] = Vword (wrepr Uptr n);
  srls_srs :> state_rel_unrolled_small vars s1 s2 n p
}.

Record state_rel_loop_large vars s1 s2 n p := {
  srll_vlr : s2.(evm).[vlri] = @Vword ws 0;
  srll_srs :> state_rel_loop_small vars s1 s2 n p
}.

Section LOOP.

Context (lbl : label.label).
Context (hlabel : ~~ has (is_label lbl) lc).

Section SMALL.

Context (hsmall : (ws <= U64)%CMP).
(* We introduce [cmd] to deal with Loop and LoopSCT at the same time. *)
Context (cmd : seq linstr).
Context (hbody : lfd.(lfd_body) = lc ++ loop_small_cmd rspn lbl ws_align ws stk_max ++ cmd).
Context (rsp_nin : ~ Sv.In rspi loop_small_vars).
(* FIXME: rename bottom into top/top_max in other files *)

Lemma loop_small_bodyP s1 s2 n :
  state_rel_loop_small loop_small_vars s1 s2 n top ->
  (0 < n)%Z ->
  exists s3,
    [/\ lsem lp (of_estate s2 fn (size lc + 5))
                (of_estate s3 fn (size lc + 7)),
        s3.(evm).[zfi] = Vbool (ZF_of_word (wrepr U64 n - wrepr U64 (wsize_size ws)))
      & state_rel_loop_small loop_small_vars s1 s3 (n - wsize_size ws) top].
Proof.
  move=> hsr hlt.
  have hn: (0 < wsize_size ws <= n)%Z.
  + split=> //.
    have := hsr.(sr_aligned).
    rewrite /is_align WArray.p_to_zE.
    move=> /eqP /Z.mod_divide [//|m ?].
    have ? := wsize_size_pos ws.
    have: (0 < m)%Z; nia.
  have hlinear:
    [elaborate (is_linear_of lp fn (lc ++ loop_small_cmd rspn lbl ws_align ws stk_max ++ cmd))].
  + by exists lfd.
  have: validw (emem s2) Aligned (top + (wrepr Uptr n - wrepr Uptr (wsize_size ws)))%R ws.
  + apply /validwP; split.
    + rewrite /= (is_align_addE top_aligned).
      have /is_align_addE <- := [elaborate (is_align_mul ws 1)].
      rewrite Z.mul_1_r GRing.addrC GRing.subrK.
      rewrite WArray.arr_is_align.
      by apply hsr.(sr_aligned).
    move=> k hk.
    apply hsr.(sr_mem_valid).
    rewrite /between /zbetween wsize8 !zify addE /top.
    rewrite -wrepr_sub -GRing.addrA -wrepr_add.
    have hbound := hsr.(sr_bound).
    have ? := [elaborate (wunsigned_range (align_word ws_align ptr))].
    by rewrite wunsigned_add; last rewrite wunsigned_sub; lia.
  move=> /(writeV 0) [m' hm'].
  eexists (Estate _ _ _); split=> /=.
  + apply: lsem_step.
    + rewrite /lsem1 /step.
      rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite /get_var hsr.(srls_off) /=.
      rewrite /exec_sopn /= !truncate_word_u /=.
      rewrite /of_estate /= /lnext_pc /=.
      by rewrite -addnS; reflexivity.
    apply: lsem_step1.
    rewrite /lsem1 /step.
    rewrite (find_instr_skip hlinear) /=.
    rewrite /eval_instr /=.
    rewrite wrepr0.
    have -> /=: exec_sopn (Ox86 (MOV ws)) [:: @Vword ws 0] = ok [:: @Vword ws 0].
    + rewrite /exec_sopn /= truncate_word_u /sopn_sem /=.
      rewrite /x86_MOV.
      by rewrite /check_size_8_64 hsmall /=.
    rewrite (@get_var_neq _ _ _ rspi);
      last by move=> /= h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
    do 5 rewrite (@get_var_neq _ _ _ rspi) //.
    rewrite [get_var _ _ rspi]/get_var hsr.(sr_rsp) /= (truncate_word_u top) /=.
    rewrite get_var_eq //= !truncate_word_u /=.
    rewrite hm' /=.
    rewrite /of_estate /= /lnext_pc /=.
    by rewrite -addnS; reflexivity.
  + rewrite Vm.setP_neq //.
    by rewrite Vm.setP_eq.
  case: hsr => hoff [hscs hmem hvalid hdisj hzero hvm htmp hrsp haligned hbound].
  split=> /=.
  + rewrite Vm.setP_eq /=.
    by rewrite wrepr_sub.
  split=> //=.
  + apply (mem_equiv_trans hmem).
    split.
    + by apply (Memory.write_mem_stable hm').
    by move=> ??; symmetry; apply (write_validw_eq hm').
  + move=> p hb.
    rewrite (write_validw_eq hm').
    by apply hvalid.
  + move=> p hp.
    rewrite (writeP_neq _ hm'); first by apply hdisj.
    apply: disjoint_range_alt.
    apply: disjoint_zrange_incl_l hp.
    rewrite /top /zbetween !zify -wrepr_sub.
    assert (h := wunsigned_range (align_word ws_align ptr)).
    by rewrite wunsigned_add; last rewrite wunsigned_sub; lia.
  + move=> p hb.
    rewrite (write_read8 hm') subE /=.
    case: ifPn => [_|h].
    + by rewrite LE.read0.
    apply hzero.
    move: h hb; rewrite /between /zbetween wsize8 !zify /top.
    change x86_reg_size with Uptr.
    rewrite -wrepr_sub -wrepr_opp -!GRing.addrA -!wrepr_add.
    have ? := [elaborate (wunsigned_range (align_word ws_align ptr))].
    rewrite wunsigned_sub_if.
    rewrite wunsigned_add; last by lia.
    rewrite wunsigned_add; last by lia.
    case: ZleP; lia.
  + by do 6 (rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; right;
      apply /sv_of_listP; rewrite !in_cons /= eqxx /= ?orbT).
  + rewrite Vm.setP_neq; last by apply /eqP => /(@inj_to_var _ _ _ _ _ _).
    by rewrite !Vm.setP_neq.
  + rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
    by do 5 rewrite Vm.setP_neq //.
  + rewrite -WArray.arr_is_align wrepr_sub.
    have /is_align_addE <- := [elaborate (is_align_mul ws 1)].
    rewrite Z.mul_1_r GRing.addrC GRing.subrK.
    by rewrite WArray.arr_is_align.
  by lia.
Qed.

Lemma loop_small_loopP s1 s2 n :
  state_rel_loop_small loop_small_vars s1 s2 n top ->
  (0 < n)%Z ->
  exists s3,
    [/\ lsem lp (of_estate s2 fn (size lc + 5))
                (of_estate s3 fn (size lc + 8))
      & state_rel_loop_small loop_small_vars s1 s3 0 top].
Proof.
  move=> hsr hlt.
  have hlinear:
    [elaborate (is_linear_of lp fn (lc ++ loop_small_cmd rspn lbl ws_align ws stk_max ++ cmd))].
  + by exists lfd.
  have [k hn]: (exists k, n = Z.of_nat k * wsize_size ws)%Z.
  + have := hsr.(sr_aligned).
    rewrite /is_align WArray.p_to_zE.
    move=> /eqP /Z.mod_divide [//|m ?].
    exists (Z.to_nat m).
    rewrite Z2Nat.id //.
    have := wsize_size_pos ws.
    by lia.
  elim: k n s2 hsr hlt hn => [|k ih] n s2 hsr hlt hn.
  + move: hn; rewrite Z.mul_0_l.
    by lia.
  have [s3 [hsem3 hzf3 hsr3]] := loop_small_bodyP hsr hlt.
  have: (k = 0 \/ 0 < k)%coq_nat by lia.
  case=> hk.
  + subst k.
    move: hn; rewrite Z.mul_1_l => ?; subst n.
    exists s3; split.
    + apply: (lsem_trans hsem3).
      apply lsem_step1.
      rewrite /lsem1 /step.
      rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite /get_var /= hzf3 /=.
      rewrite GRing.addrN /ZF_of_word /= eqxx /=.
      rewrite /lnext_pc /=.
      by rewrite -addnS.
    by move: hsr3; rewrite Z.sub_diag.
  have hlt3: (0 < n - wsize_size ws)%Z by nia.
  have hn3: (n - wsize_size ws)%Z = (Z.of_nat k * wsize_size ws)%Z by lia.
  have [s4 [hsem4 hsr4]] := ih _ _ hsr3 hlt3 hn3.
  exists s4; split=> //.
  apply: (lsem_trans hsem3).
  apply: lsem_step hsem4.
  rewrite /lsem1 /step.
  rewrite (find_instr_skip hlinear) /=.
  rewrite /eval_instr /=.
  rewrite /get_var /= hzf3 /=.
  have ->: ~~ ZF_of_word (wrepr U64 n - wrepr U64 (wsize_size ws)).
  + rewrite /ZF_of_word; apply /eqP => /(f_equal wunsigned).
    rewrite wunsigned0 -wrepr_sub wunsigned_repr_small; first by lia.
    change U64 with Uptr.
    have := hsr.(sr_bound).
    have! := (wunsigned_range (align_word ws_align ptr)).
    have := wsize_size_pos ws.
    by lia.
  rewrite hlfd /= hbody.
  rewrite (find_label_cat_hd (sip := sip_of_asm_e) _ hlabel).
  do 5 rewrite (find_labelE (sip := sip_of_asm_e)) /=.
  rewrite /is_label /= eqxx /=.
  rewrite /setcpc /=.
  by rewrite -addnS.
Qed.

Lemma loop_small_initP (s1 : estate) :
  valid_between s1.(emem) top stk_max ->
  s1.(evm).[rspi] = Vword ptr ->
  exists s2,
    lsem lp (of_estate s1 fn (size lc)) (of_estate s2 fn (size lc + 5)) /\
    state_rel_loop_small loop_small_vars s1 s2 stk_max top.
Proof.
Local Opaque wsize_size.
  move=> hvalid hrsp.
  have hlinear:
    [elaborate (is_linear_of lp fn (lc ++ loop_small_cmd rspn lbl ws_align ws stk_max ++ cmd))].
  + by exists lfd.
  eexists (Estate _ _ _); split.
  + apply: lsem_step5; rewrite /lsem1 /step /=.
    * rewrite -(addn0 (size lc)) (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite /get_var /= hrsp /=.
      rewrite /exec_sopn /= truncate_word_u /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
    * rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite get_var_neq;
        last by move=> h; apply /rsp_nin /sv_of_listP;
        rewrite !in_cons /= -h eqxx /= ?orbT.
      rewrite /get_var /= hrsp /=.
      rewrite /exec_sopn /= !truncate_word_u /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
    * rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite get_var_eq /=; last by [].
      rewrite /exec_sopn /= !truncate_word_u /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
    * rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite /exec_sopn /= truncate_word_u /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
    * rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite /setpc /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
  split=> /=.
  + by rewrite Vm.setP_eq.
  split=> //=.
  + move=> p.
    by rewrite Z.sub_diag /between (negbTE (not_zbetween_neg _ _ _ _)).
  + by do 14 (rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; (left; reflexivity) ||
      right; apply /sv_of_listP; rewrite !in_cons /= eqxx /= ?orbT).
  + do 13 (rewrite Vm.setP_neq;
      last by [|
        apply /eqP => /(@inj_to_var _ _ _ _ _ _) |
        apply /eqP => h; apply /rsp_nin /sv_of_listP;
          rewrite !in_cons /= -h eqxx /= ?orbT]).
    by rewrite Vm.setP_eq.
  + rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
    by rewrite Vm.setP_eq.
  by lia.
Local Transparent wsize_size.
Qed.

Lemma loop_small_finalP (s1 s2 : estate) :
  state_rel_loop_small loop_small_vars s1 s2 0 top ->
  exists s3,
    lsem lp
      (of_estate s2 fn (size lc + 8))
      (of_estate s3 fn (size lc + size (loop_small_cmd rspn lbl ws_align ws stk_max))) /\
    state_rel_loop_small loop_small_vars s1 s3 0 ptr.
Proof.
  move=> hsr.
  have hlinear:
    [elaborate (is_linear_of lp fn (lc ++ loop_small_cmd rspn lbl ws_align ws stk_max ++ cmd))].
  + by exists lfd.
  eexists (Estate _ _ _); split=> /=.
  + apply: lsem_step1.
    rewrite /lsem1 /step.
    rewrite (find_instr_skip hlinear) /=.
    rewrite /eval_instr /=.
    rewrite /get_var /= hsr.(sr_tmp) /=.
    rewrite /exec_sopn /= truncate_word_u /=.
    rewrite /of_estate /= /lnext_pc.
    by rewrite -addnS; reflexivity.
  case: hsr => hoff [hscs hmem hvalid hdisj hzero hvm htmp hrsp haligned hbound].
  split=> /=.
  + rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
    by rewrite hoff.
  split=> //=.
  + by rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; left; reflexivity.
  + by rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
  by rewrite Vm.setP_eq.
Qed.

Lemma loop_smallP (s1 : estate) :
  valid_between s1.(emem) top stk_max ->
  s1.(evm).[rspi] = Vword ptr ->
  exists s2,
    lsem lp
      (of_estate s1 fn (size lc))
      (of_estate s2 fn (size lc + size (loop_small_cmd rspn lbl ws_align ws stk_max))) /\
    state_rel_loop_small loop_small_vars s1 s2 0 ptr.
Proof.
  move=> hvalid hrsp.
  have [s2 [hsem2 hsr2]] := loop_small_initP hvalid hrsp.
  have [s3 [hsem3 hsr3]] := loop_small_loopP hsr2 lt_0_stk_max.
  have [s4 [hsem4 hsr4]] := loop_small_finalP hsr3.
  exists s4; split=> //.
  apply (lsem_trans hsem2).
  by apply (lsem_trans hsem3).
Qed.

End SMALL.

Section LARGE.

Context (hlarge : ~ (ws <= U64)%CMP).
(* We introduce [cmd] to deal with Loop and LoopSCT at the same time. *)
Context (cmd : seq linstr).
Context (hbody : lfd.(lfd_body) = lc ++ loop_large_cmd rspn lbl ws_align ws stk_max ++ cmd).
Context (rsp_nin : ~ Sv.In rspi loop_large_vars).
(* FIXME: rename bottom into top/top_max in other files *)

Lemma loop_large_bodyP s1 s2 n :
  state_rel_loop_large loop_large_vars s1 s2 n top ->
  (0 < n)%Z ->
  exists s3,
    [/\ lsem lp (of_estate s2 fn (size lc + 6))
                (of_estate s3 fn (size lc + 8)),
        s3.(evm).[zfi] = Vbool (ZF_of_word (wrepr U64 n - wrepr U64 (wsize_size ws)))
      & state_rel_loop_large loop_large_vars s1 s3 (n - wsize_size ws) top].
Proof.
  move=> hsr hlt.
  have hn: (0 < wsize_size ws <= n)%Z.
  + split=> //.
    have := hsr.(sr_aligned).
    rewrite /is_align WArray.p_to_zE.
    move=> /eqP /Z.mod_divide [//|m ?].
    have ? := wsize_size_pos ws.
    have: (0 < m)%Z; nia.
  have hlinear:
    [elaborate (is_linear_of lp fn (lc ++ loop_large_cmd rspn lbl ws_align ws stk_max ++ cmd))].
  + by exists lfd.
  have: validw (emem s2) Aligned (top + (wrepr Uptr n - wrepr Uptr (wsize_size ws)))%R ws.
  + apply /validwP; split.
    + rewrite /= (is_align_addE top_aligned).
      have /is_align_addE <- := [elaborate (is_align_mul ws 1)].
      rewrite Z.mul_1_r GRing.addrC GRing.subrK.
      rewrite WArray.arr_is_align.
      by apply hsr.(sr_aligned).
    move=> k hk.
    apply hsr.(sr_mem_valid).
    rewrite /between /zbetween wsize8 !zify addE /top.
    rewrite -wrepr_sub -GRing.addrA -wrepr_add.
    have hbound := hsr.(sr_bound).
    have ? := [elaborate (wunsigned_range (align_word ws_align ptr))].
    by rewrite wunsigned_add; last rewrite wunsigned_sub; lia.
  move=> /(writeV 0) [m' hm'].
  eexists (Estate _ _ _); split=> /=.
  + apply: lsem_step.
    + rewrite /lsem1 /step.
      rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite /get_var hsr.(srls_off) /=.
      rewrite /exec_sopn /= !truncate_word_u /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
    apply: lsem_step1.
    rewrite /lsem1 /step.
    rewrite (find_instr_skip hlinear) /=.
    rewrite /eval_instr /=.
    do 6 rewrite (@get_var_neq _ _ _ vlri) //.
    rewrite [get_var _ _ vlri]/get_var hsr.(srll_vlr) /=.
    rewrite /exec_sopn /= truncate_word_u /= /sopn_sem /= /x86_VMOVDQ.
    rewrite wsize_nle_u64_check_128_256 /=; last by apply /negbTE /negP.
    rewrite get_var_eq //=.
    rewrite get_var_neq;
      last by move=> h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
     do 5 rewrite get_var_neq //.
    rewrite /get_var /= hsr.(sr_rsp) /= !truncate_word_u /=.
    rewrite hm' /=.
    rewrite /of_estate /= /lnext_pc.
    by rewrite -addnS; reflexivity.
  + rewrite Vm.setP_neq //.
    by rewrite Vm.setP_eq.
  case: hsr => hvlr [hoff [hscs hmem hvalid hdisj hzero hvm htmp hrsp haligned hbound]].
  split=> /=.
  + by rewrite !Vm.setP_neq.
  split=> /=.
  + rewrite Vm.setP_eq /=.
    by rewrite wrepr_sub.
  split=> //=.
  + apply (mem_equiv_trans hmem).
    split.
    + by apply (Memory.write_mem_stable hm').
    by move=> ??; symmetry; apply (write_validw_eq hm').
  + move=> p hb.
    rewrite (write_validw_eq hm').
    by apply hvalid.
  + move=> p hp.
    rewrite (writeP_neq _ hm'); first by apply hdisj.
    apply: disjoint_range_alt.
    apply: disjoint_zrange_incl_l hp.
    rewrite /top /zbetween !zify -wrepr_sub.
    assert (h := wunsigned_range (align_word ws_align ptr)).
    by rewrite wunsigned_add; last rewrite wunsigned_sub; lia.
  + move=> p hb.
    rewrite (write_read8 hm') subE /=.
    case: ifPn => [_|h].
    + by rewrite LE.read0.
    apply hzero.
    move: h hb; rewrite /between /zbetween wsize8 !zify /top.
    change x86_reg_size with Uptr.
    rewrite -wrepr_sub -wrepr_opp -!GRing.addrA -!wrepr_add.
    have ? := [elaborate (wunsigned_range (align_word ws_align ptr))].
    rewrite wunsigned_sub_if.
    rewrite wunsigned_add; last by lia.
    rewrite wunsigned_add; last by lia.
    case: ZleP; lia.
  + by do 6 (rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; right;
      apply /sv_of_listP; rewrite !in_cons /= eqxx /= ?orbT).
  + rewrite Vm.setP_neq; last by apply /eqP => /(@inj_to_var _ _ _ _ _ _).
    by rewrite !Vm.setP_neq.
  + rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
    by do 5 rewrite Vm.setP_neq //.
  + rewrite -WArray.arr_is_align wrepr_sub.
    have /is_align_addE <- := [elaborate (is_align_mul ws 1)].
    rewrite Z.mul_1_r GRing.addrC GRing.subrK.
    by rewrite WArray.arr_is_align.
  by lia.
Qed.

Lemma loop_large_loopP s1 s2 n :
  state_rel_loop_large loop_large_vars s1 s2 n top ->
  (0 < n)%Z ->
  exists s3,
    [/\ lsem lp (of_estate s2 fn (size lc + 6))
                (of_estate s3 fn (size lc + 9))
      & state_rel_loop_large loop_large_vars s1 s3 0 top].
Proof.
  move=> hsr hlt.
  have hlinear:
    [elaborate (is_linear_of lp fn (lc ++ loop_large_cmd rspn lbl ws_align ws stk_max ++ cmd))].
  + by exists lfd.
  have [k hn]: (exists k, n = Z.of_nat k * wsize_size ws)%Z.
  + have := hsr.(sr_aligned).
    rewrite /is_align WArray.p_to_zE.
    move=> /eqP /Z.mod_divide [//|m ?].
    exists (Z.to_nat m).
    rewrite Z2Nat.id //.
    have := wsize_size_pos ws.
    by lia.
  elim: k n s2 hsr hlt hn => [|k ih] n s2 hsr hlt hn.
  + move: hn; rewrite Z.mul_0_l.
    by lia.
  have [s3 [hsem3 hzf3 hsr3]] := loop_large_bodyP hsr hlt.
  have: (k = 0 \/ 0 < k)%coq_nat by lia.
  case=> hk.
  + subst k.
    move: hn; rewrite Z.mul_1_l => ?; subst n.
    exists s3; split.
    + apply: (lsem_trans hsem3).
      apply lsem_step1.
      rewrite /lsem1 /step.
      rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite /get_var /= hzf3 /=.
      rewrite GRing.addrN /ZF_of_word /= eqxx /=.
      rewrite /lnext_pc /=.
      by rewrite -addnS.
    by move: hsr3; rewrite Z.sub_diag.
  have hlt3: (0 < n - wsize_size ws)%Z by nia.
  have hn3: (n - wsize_size ws)%Z = (Z.of_nat k * wsize_size ws)%Z by lia.
  have [s4 [hsem4 hsr4]] := ih _ _ hsr3 hlt3 hn3.
  exists s4; split=> //.
  apply: (lsem_trans hsem3).
  apply: lsem_step hsem4.
  rewrite /lsem1 /step.
  rewrite (find_instr_skip hlinear) /=.
  rewrite /eval_instr /=.
  rewrite /get_var /= hzf3 /=.
  have ->: ~~ ZF_of_word (wrepr U64 n - wrepr U64 (wsize_size ws)).
  + rewrite /ZF_of_word; apply /eqP => /(f_equal wunsigned).
    rewrite wunsigned0 -wrepr_sub wunsigned_repr_small; first by lia.
    change U64 with Uptr.
    have := hsr.(sr_bound).
    have! := (wunsigned_range (align_word ws_align ptr)).
    have := wsize_size_pos ws.
    by lia.
  rewrite hlfd /= hbody.
  rewrite (find_label_cat_hd (sip := sip_of_asm_e) _ hlabel).
  do 6 rewrite (find_labelE (sip := sip_of_asm_e)) /=.
  rewrite /is_label /= eqxx /=.
  rewrite /setcpc /=.
  by rewrite -addnS.
Qed.

Lemma loop_large_initP (s1 : estate) :
  valid_between s1.(emem) top stk_max ->
  s1.(evm).[rspi] = Vword ptr ->
  exists s2,
    lsem lp (of_estate s1 fn (size lc)) (of_estate s2 fn (size lc + 6)) /\
    state_rel_loop_large loop_large_vars s1 s2 stk_max top.
Proof.
Local Opaque wsize_size.
  move=> hvalid hrsp.
  have hlinear:
    [elaborate (is_linear_of lp fn (lc ++ loop_large_cmd rspn lbl ws_align ws stk_max ++ cmd))].
  + by exists lfd.
  eexists (Estate _ _ _); split.
  + apply: lsem_step6; rewrite /lsem1 /step.
    * rewrite -(addn0 (size lc)) (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite /get_var /= hrsp /=.
      rewrite /exec_sopn /= truncate_word_u /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
    * rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      have -> /=: exec_sopn (Oasm (ExtOp (Oset0 ws))) [::] = ok [:: @Vword ws 0].
      + rewrite /exec_sopn /= /sopn_sem /=.
        rewrite /Oset0_instr.
        by move /negP/negPf : hlarge => -> /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
    * rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite get_var_neq //.
      rewrite get_var_neq;
        last by move=> h; apply /rsp_nin /sv_of_listP;
        rewrite !in_cons /= -h eqxx /= ?orbT.
      rewrite /get_var /= hrsp /=.
      rewrite /exec_sopn /= !truncate_word_u /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
    * rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite get_var_eq /=; last by [].
      rewrite /exec_sopn /= !truncate_word_u /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
    * rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite /exec_sopn /= truncate_word_u /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
    * rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite /setpc /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
  split=> /=.
  + do 13 rewrite Vm.setP_neq //.
    by rewrite Vm.setP_eq /= wsize_ge_U256.
  split=> /=.
  + by rewrite Vm.setP_eq.
  split=> //=.
  + move=> p.
    by rewrite Z.sub_diag /between (negbTE (not_zbetween_neg _ _ _ _)).
  + by do 15 (rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; (left; reflexivity) ||
      right; apply /sv_of_listP; rewrite !in_cons /= eqxx /= ?orbT).
  + do 14 (rewrite Vm.setP_neq;
      last by [|
        apply /eqP => /(@inj_to_var _ _ _ _ _ _) |
        apply /eqP => h; apply /rsp_nin /sv_of_listP;
          rewrite !in_cons /= -h eqxx /= ?orbT]).
    by rewrite Vm.setP_eq.
  + rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
    by rewrite Vm.setP_eq.
  by lia.
Local Transparent wsize_size.
Qed.

Lemma loop_large_finalP (s1 s2 : estate) :
  state_rel_loop_large loop_large_vars s1 s2 0 top ->
  exists s3,
    lsem lp
      (of_estate s2 fn (size lc + 9))
      (of_estate s3 fn (size lc + size (loop_large_cmd rspn lbl ws_align ws stk_max))) /\
    state_rel_loop_large loop_large_vars s1 s3 0 ptr.
Proof.
  move=> hsr.
  have hlinear:
    [elaborate (is_linear_of lp fn (lc ++ loop_large_cmd rspn lbl ws_align ws stk_max ++ cmd))].
  + by exists lfd.
  eexists (Estate _ _ _); split=> /=.
  + apply: lsem_step1.
    rewrite /lsem1 /step.
    rewrite (find_instr_skip hlinear) /=.
    rewrite /eval_instr /=.
    rewrite /get_var /= hsr.(sr_tmp) /=.
    rewrite /exec_sopn /= truncate_word_u /=.
    rewrite /of_estate /= /lnext_pc.
    by rewrite -addnS; reflexivity.
  case: hsr => hvlr [hoff [hscs hmem hvalid hdisj hzero hvm htmp hrsp haligned hbound]].
  split=> /=.
  + by rewrite Vm.setP_neq.
  split=> /=.
  + rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
    by rewrite hoff.
  split=> //=.
  + by rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; left; reflexivity.
  + by rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
  by rewrite Vm.setP_eq.
Qed.

Lemma loop_largeP (s1 : estate) :
  valid_between s1.(emem) top stk_max ->
  s1.(evm).[rspi] = Vword ptr ->
  exists s2,
    lsem lp
      (of_estate s1 fn (size lc))
      (of_estate s2 fn (size lc + size (loop_large_cmd rspn lbl ws_align ws stk_max))) /\
    state_rel_loop_large loop_large_vars s1 s2 0 ptr.
Proof.
  move=> hvalid hrsp.
  have [s2 [hsem2 hsr2]] := loop_large_initP hvalid hrsp.
  have [s3 [hsem3 hsr3]] := loop_large_loopP hsr2 lt_0_stk_max.
  have [s4 [hsem4 hsr4]] := loop_large_finalP hsr3.
  exists s4; split=> //.
  apply (lsem_trans hsem2).
  by apply (lsem_trans hsem3).
Qed.

End LARGE.

Lemma loopP (s1 : estate) cmd vars cmd' :
  x86_stack_zero_loop rspn lbl ws_align ws stk_max = (cmd, vars) ->
  lfd_body lfd = lc ++ cmd ++ cmd' ->
  ~ Sv.In rspi vars ->
  valid_between s1.(emem) top stk_max ->
  s1.(evm).[rspi] = Vword ptr ->
  exists s2,
    lsem lp
      (of_estate s1 fn (size lc))
      (of_estate s2 fn (size lc + size cmd)) /\
    state_rel_loop_small vars s1 s2 0 ptr.
Proof.
  rewrite /x86_stack_zero_loop.
  case: ifPn => [hsmall|/negP hlarge] [<- <-] hbody rsp_nin hvalid hrsp.
  + exact: (loop_smallP hsmall hbody rsp_nin hvalid hrsp).
  have [s2 [hsem hsr]] := loop_largeP hlarge hbody rsp_nin hvalid hrsp.
  exists s2; split=> //.
  by case: hsr.
Qed.

End LOOP.

Section UNROLLED.

Section SMALL.

Context (hsmall : (ws <= U64)%CMP).
Context (hbody : lfd.(lfd_body) = lc ++ unrolled_small_cmd rspn ws_align ws stk_max).
Context (rsp_nin : ~ Sv.In rspi unrolled_small_vars).

(* FIXME: remove *)
Lemma onth_size T n (s : seq T) x :
  oseq.onth s n = Some x ->
  n < size s.
Proof. by elim: s n => [//|a s ih] [|n] //= /ih. Qed.

(* FIXME: remove *)
Lemma onth_rev T n (s : seq T) x :
  oseq.onth s n = Some x ->
  oseq.onth (rev s) (size s - n.+1) = Some x.
Proof.
  elim: s n => [|a s ih] n /=.
  + done.
  case: n => [|n].
  + move=> [<-]. rewrite rev_cons -cats1 oseq.onth_cat. rewrite size_rev.
    have ->: (size s).+1 - 1 = size s.
    + rewrite -minusE. lia.
    rewrite ltnn subnn. done.
  move=> /ih{}ih. rewrite rev_cons -cats1 oseq.onth_cat size_rev.
  have ->: (size s).+1 - n.+2= size s - n.+1.
  + rewrite -!minusE. lia.
  have := (onth_size ih). rewrite size_rev. move=> ->. done.
Qed.

Lemma unrolled_small_bodyP s1 s2 n :
  state_rel_unrolled_small unrolled_small_vars s1 s2 (stk_max - Z.of_nat n * wsize_size ws) top ->
  (Z.of_nat n < stk_max / wsize_size ws)%Z ->
  exists s3,
    [/\ lsem lp (of_estate s2 fn (size lc + 3 + n))
                (of_estate s3 fn (size lc + 3 + n.+1))
      & state_rel_unrolled_small unrolled_small_vars s1 s3 (stk_max - Z.of_nat n.+1 * wsize_size ws) top].
Proof.
Local Opaque wsize_size Z.of_nat.
  move=> hsr hlt.
  have hlinear:
    [elaborate (is_linear_of lp fn (lc ++ unrolled_small_cmd rspn ws_align ws stk_max))].
  + by exists lfd.
  have hlt': (0 < Z.of_nat n.+1 * wsize_size ws <= stk_max)%Z.
  + split; first by have := wsize_size_pos ws; lia.
    etransitivity; last by apply (Z.mul_div_le _ (wsize_size ws)).
    rewrite Z.mul_comm; apply Z.mul_le_mono_nonneg_l => //.
    rewrite Nat2Z.inj_succ.
    by apply Z.le_succ_l.
  have: validw (emem s2) Aligned (top + (wrepr Uptr (stk_max - Z.of_nat n.+1 * wsize_size ws)))%R ws.
  + apply /validwP; split.
    + rewrite /= (is_align_addE top_aligned).
      have /is_align_addE <- := [elaborate (is_align_mul ws (Z.of_nat n.+1))].
      rewrite Z.mul_comm wrepr_sub GRing.addrC GRing.subrK.
      by rewrite WArray.arr_is_align.
    move=> k hk.
    apply hsr.(sr_mem_valid).
    rewrite /between /zbetween wsize8 !zify addE /top.
    rewrite -GRing.addrA -wrepr_add.
    have hbound := hsr.(sr_bound).
    have ? := [elaborate (wunsigned_range (align_word ws_align ptr))].
    by rewrite wunsigned_add; last rewrite wunsigned_sub; lia.
  move=> /(writeV 0) [m' hm'].
  eexists (Estate _ _ _); split.
  + apply: lsem_step1.
    rewrite /lsem1 /step.
    rewrite -addnA (find_instr_skip hlinear) /=.
    rewrite onth_map.
    rewrite oseq.onth_cat !size_map size_rev size_ziota.
    have hlt'': n < Z.to_nat (stk_max / wsize_size ws) by apply /ltP; lia.
    rewrite hlt''.
    rewrite !onth_map.
    rewrite oseq.onth_nth (nth_map 0%Z); last by rewrite size_rev size_ziota.
    have ->:
      (nth 0 (rev (ziota 0 (stk_max / wsize_size ws))) n * wsize_size ws =
        stk_max - Z.of_nat n.+1 * wsize_size ws)%Z.
    + rewrite nth_rev; last by rewrite size_ziota.
      rewrite nth_ziota /=; last first.
      + by rewrite size_ziota -minusE; apply /ltP; lia.
      rewrite size_ziota.
      rewrite Nat2Z.n2zB //.
      rewrite Z2Nat.id; last by lia.
      rewrite Z.mul_sub_distr_r.
      rewrite Z.mul_comm -(proj2 (Z.div_exact _ _ _)) //.
      by move: halign; rewrite /is_align WArray.p_to_zE => /eqP.
    rewrite /eval_instr /=.
    rewrite wrepr0.
    have -> /=: exec_sopn (Ox86 (MOV ws)) [:: @Vword ws 0] = ok [:: @Vword ws 0].
    + rewrite /exec_sopn /= truncate_word_u /sopn_sem /=.
      rewrite /x86_MOV.
      by rewrite /check_size_8_64 hsmall /=.
    rewrite /get_var /= hsr.(sr_rsp) /=.
    rewrite !truncate_word_u /=.
    rewrite hm' /=.
    rewrite /of_estate /= /lnext_pc /=.
    by rewrite -!addnS addnA.
  case: hsr => hscs hmem hvalid hdisj hzero hvm htmp hrsp haligned hbound.
  split=> //=.
  + apply (mem_equiv_trans hmem).
    split.
    + by apply (Memory.write_mem_stable hm').
    by move=> ??; symmetry; apply (write_validw_eq hm').
  + move=> p hb.
    rewrite (write_validw_eq hm').
    by apply hvalid.
  + move=> p hp.
    rewrite (writeP_neq _ hm'); first by apply hdisj.
    apply: disjoint_range_alt.
    apply: disjoint_zrange_incl_l hp.
    rewrite /top /zbetween !zify.
    assert (h := wunsigned_range (align_word ws_align ptr)).
    by rewrite wunsigned_add; last rewrite wunsigned_sub; lia.
  + move=> p hb.
    rewrite (write_read8 hm') subE /=.
    case: ifPn => [_|h].
    + by rewrite LE.read0.
    apply hzero.
    move: h hb; rewrite /between /zbetween wsize8 !zify /top.
    change x86_reg_size with Uptr.
    rewrite -wrepr_opp -!GRing.addrA -!wrepr_add.
    have ? := [elaborate (wunsigned_range (align_word ws_align ptr))].
    rewrite wunsigned_sub_if.
    rewrite wunsigned_add; last by lia.
    rewrite wunsigned_add; last by lia.
    case: ZleP; lia.
  + rewrite -WArray.arr_is_align.
    have /is_align_addE <- := [elaborate (is_align_mul ws (Z.of_nat n.+1))].
    rewrite Z.mul_comm wrepr_sub GRing.addrC GRing.subrK.
    by rewrite WArray.arr_is_align.
  by lia.
Local Transparent wsize_size Z.of_nat.
Qed.

Lemma unrolled_small_loopP s1 s2 :
  state_rel_unrolled_small unrolled_small_vars s1 s2 stk_max top ->
  exists s3,
    [/\ lsem lp (of_estate s2 fn (size lc + 3))
                (of_estate s3 fn (size lc + 3 + Z.to_nat (stk_max / wsize_size ws)))
      & state_rel_unrolled_small unrolled_small_vars s1 s3 0 top].
Proof.
  move=> hsr.
  have hlinear:
    [elaborate (is_linear_of lp fn (lc ++ unrolled_small_cmd rspn ws_align ws stk_max))].
  + by exists lfd.
  have [k [hmax hbound]]:
    exists k, (stk_max = Z.of_nat k * wsize_size ws)%Z
           /\ k <= Z.to_nat (stk_max / wsize_size ws).
  + have := halign.
    rewrite /is_align WArray.p_to_zE.
    move=> /eqP /Z.mod_divide [//|m h].
    exists (Z.to_nat m).
    split.
    + rewrite Z2Nat.id //.
      by have := wsize_size_pos ws; lia.
    by rewrite h Z.div_mul.
  rewrite -(Z.sub_diag stk_max).
  rewrite {1 3}hmax {hmax}.
  rewrite Z.div_mul // Nat2Z.id.
  elim: k s2 hbound hsr => [|k ih] s2 hbound hsr.
  + rewrite /= addn0 Z.sub_0_r.
    exists s2; split=> //.
    by apply Relation_Operators.rt_refl.
  have [s3 [hsem3 hsr3]] := ih _ (ltnW hbound) hsr.
  have hbound': (Z.of_nat k < stk_max / wsize_size ws)%Z.
  + by move/leP: hbound; lia.
  have [s4 [hsem4 hsr4]] := unrolled_small_bodyP hsr3 hbound'.
  exists s4; split=> //.
  by apply (lsem_trans hsem3).
Qed.

Lemma unrolled_small_initP (s1 : estate) :
  valid_between s1.(emem) top stk_max ->
  s1.(evm).[rspi] = Vword ptr ->
  exists s2,
    lsem lp (of_estate s1 fn (size lc)) (of_estate s2 fn (size lc + 3)) /\
    state_rel_unrolled_small unrolled_small_vars s1 s2 stk_max top.
Proof.
Local Opaque wsize_size.
  move=> hvalid hrsp.
  have hlinear:
    [elaborate (is_linear_of lp fn (lc ++ unrolled_small_cmd rspn ws_align ws stk_max))].
  + by exists lfd.
  eexists (Estate _ _ _); split.
  + apply: lsem_step3; rewrite /lsem1 /step.
    * rewrite -(addn0 (size lc)) (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite /get_var /= hrsp /=.
      rewrite /exec_sopn /= truncate_word_u /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
    * rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite get_var_neq;
        last by move=> h; apply /rsp_nin /sv_of_listP;
        rewrite !in_cons /= -h eqxx /= ?orbT.
      rewrite /get_var /= hrsp /=.
      rewrite /exec_sopn /= !truncate_word_u /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
    * rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite get_var_eq /=; last by [].
      rewrite /exec_sopn /= !truncate_word_u /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
  split=> //=.
  + move=> p.
    by rewrite Z.sub_diag /between (negbTE (not_zbetween_neg _ _ _ _)).
  + by do 13 (rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; (left; reflexivity) ||
      right; apply /sv_of_listP; rewrite !in_cons /= eqxx /= ?orbT).
  + do 12 (rewrite Vm.setP_neq;
      last by [|
        apply /eqP => /(@inj_to_var _ _ _ _ _ _) |
        apply /eqP => h; apply /rsp_nin /sv_of_listP;
          rewrite !in_cons /= -h eqxx /= ?orbT]).
    by rewrite Vm.setP_eq.
  + by rewrite Vm.setP_eq.
  by lia.
Local Transparent wsize_size.
Qed.

Lemma unrolled_small_finalP (s1 s2 : estate) :
  state_rel_unrolled_small unrolled_small_vars s1 s2 0 top ->
  exists s3,
    lsem lp
      (of_estate s2 fn (size lc + 3 + Z.to_nat (stk_max / wsize_size ws)))
      (of_estate s3 fn (size lc + size (unrolled_small_cmd rspn ws_align ws stk_max))) /\
    state_rel_unrolled_small unrolled_small_vars s1 s3 0 ptr.
Proof.
  move=> hsr.
  have hlinear:
    [elaborate (is_linear_of lp fn (lc ++ unrolled_small_cmd rspn ws_align ws stk_max))].
  + by exists lfd.
  have ->: size (unrolled_small_cmd rspn ws_align ws stk_max) =
        (3 + Z.to_nat (stk_max / wsize_size ws)).+1.
  + rewrite /= size_map size_cat !size_map size_rev size_ziota /=.
    by rewrite addnS addn0 -addSn.
  eexists (Estate _ _ _); split=> /=.
  + apply: lsem_step1.
    rewrite /lsem1 /step.
    rewrite -addnA (find_instr_skip hlinear) /=.
    rewrite onth_map.
    rewrite oseq.onth_cat !size_map size_rev size_ziota.
    rewrite ltnn subnn /=.
    rewrite /eval_instr /=.
    rewrite /get_var /= hsr.(sr_tmp) /=.
    rewrite /exec_sopn /= truncate_word_u /=.
    rewrite /of_estate /= /lnext_pc /=.
    by rewrite -addnS; reflexivity.
  case: hsr => hscs hmem hvalid hdisj hzero hvm htmp hrsp haligned hbound.
  split=> //=.
  + by rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; left; reflexivity.
  + by rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
  by rewrite Vm.setP_eq.
Qed.

Lemma unrolled_smallP (s1 : estate) :
  valid_between s1.(emem) top stk_max ->
  s1.(evm).[rspi] = Vword ptr ->
  exists s2,
    lsem lp
      (of_estate s1 fn (size lc))
      (of_estate s2 fn (size lc + size (unrolled_small_cmd rspn ws_align ws stk_max))) /\
    state_rel_unrolled_small unrolled_small_vars s1 s2 0 ptr.
Proof.
  move=> hvalid hrsp.
  have [s2 [hsem2 hsr2]] := unrolled_small_initP hvalid hrsp.
  have [s3 [hsem3 hsr3]] := unrolled_small_loopP hsr2.
  have [s4 [hsem4 hsr4]] := unrolled_small_finalP hsr3.
  exists s4; split=> //.
  apply (lsem_trans hsem2).
  by apply (lsem_trans hsem3).
Qed.

End SMALL.

Section LARGE.

Context (hlarge : ~ (ws <= U64)%CMP).
Context (hbody : lfd.(lfd_body) = lc ++ unrolled_large_cmd rspn ws_align ws stk_max).
Context (rsp_nin : ~ Sv.In rspi unrolled_large_vars).

Lemma unrolled_large_bodyP s1 s2 n :
  state_rel_unrolled_large unrolled_large_vars s1 s2 (stk_max - Z.of_nat n * wsize_size ws) top ->
  (Z.of_nat n < stk_max / wsize_size ws)%Z ->
  exists s3,
    [/\ lsem lp (of_estate s2 fn (size lc + 4 + n))
                (of_estate s3 fn (size lc + 4 + n.+1))
      & state_rel_unrolled_large unrolled_large_vars s1 s3 (stk_max - Z.of_nat n.+1 * wsize_size ws) top].
Proof.
Local Opaque wsize_size Z.of_nat.
  move=> hsr hlt.
  have hlinear:
    [elaborate (is_linear_of lp fn (lc ++ unrolled_large_cmd rspn ws_align ws stk_max))].
  + by exists lfd.
  have hlt': (0 < Z.of_nat n.+1 * wsize_size ws <= stk_max)%Z.
  + split; first by have := wsize_size_pos ws; lia.
    etransitivity; last by apply (Z.mul_div_le _ (wsize_size ws)).
    rewrite Z.mul_comm; apply Z.mul_le_mono_nonneg_l => //.
    rewrite Nat2Z.inj_succ.
    by apply Z.le_succ_l.
  have: validw (emem s2) Aligned (top + (wrepr Uptr (stk_max - Z.of_nat n.+1 * wsize_size ws)))%R ws.
  + apply /validwP; split.
    + rewrite /= (is_align_addE top_aligned).
      have /is_align_addE <- := [elaborate (is_align_mul ws (Z.of_nat n.+1))].
      rewrite Z.mul_comm wrepr_sub GRing.addrC GRing.subrK.
      by rewrite WArray.arr_is_align.
    move=> k hk.
    apply hsr.(sr_mem_valid).
    rewrite /between /zbetween wsize8 !zify addE /top.
    rewrite -GRing.addrA -wrepr_add.
    have hbound := hsr.(sr_bound).
    have ? := [elaborate (wunsigned_range (align_word ws_align ptr))].
    by rewrite wunsigned_add; last rewrite wunsigned_sub; lia.
  move=> /(writeV 0) [m' hm'].
  eexists (Estate _ _ _); split.
  + apply: lsem_step1.
    rewrite /lsem1 /step.
    rewrite -addnA (find_instr_skip hlinear) /=.
    rewrite onth_map.
    rewrite oseq.onth_cat !size_map size_rev size_ziota.
    have hlt'': n < Z.to_nat (stk_max / wsize_size ws) by apply /ltP; lia.
    rewrite hlt''.
    rewrite !onth_map.
    rewrite oseq.onth_nth (nth_map 0%Z); last by rewrite size_rev size_ziota.
    have ->:
      (nth 0 (rev (ziota 0 (stk_max / wsize_size ws))) n * wsize_size ws =
        stk_max - Z.of_nat n.+1 * wsize_size ws)%Z.
    + rewrite nth_rev; last by rewrite size_ziota.
      rewrite nth_ziota /=; last first.
      + by rewrite size_ziota -minusE; apply /ltP; lia.
      rewrite size_ziota.
      rewrite Nat2Z.n2zB //.
      rewrite Z2Nat.id; last by lia.
      rewrite Z.mul_sub_distr_r.
      rewrite Z.mul_comm -(proj2 (Z.div_exact _ _ _)) //.
      by move: halign; rewrite /is_align WArray.p_to_zE => /eqP.
    rewrite /eval_instr /=.
    rewrite [get_var _ _ vlri]/get_var hsr.(srul_vlr) /=.
    rewrite /exec_sopn /= (@truncate_word_u ws) /= /sopn_sem /= /x86_VMOVDQ.
    rewrite wsize_nle_u64_check_128_256 /=; last by apply /negbTE /negP.
    rewrite /get_var /= hsr.(sr_rsp) /= !truncate_word_u /=.
    rewrite hm' /=.
    rewrite /of_estate /= /lnext_pc /=.
    by rewrite -!addnS addnA.
  case: hsr => hvlr [hscs hmem hvalid hdisj hzero hvm htmp hrsp haligned hbound].
  split=> //=.
  split=> //=.
  + apply (mem_equiv_trans hmem).
    split.
    + by apply (Memory.write_mem_stable hm').
    by move=> ??; symmetry; apply (write_validw_eq hm').
  + move=> p hb.
    rewrite (write_validw_eq hm').
    by apply hvalid.
  + move=> p hp.
    rewrite (writeP_neq _ hm'); first by apply hdisj.
    apply: disjoint_range_alt.
    apply: disjoint_zrange_incl_l hp.
    rewrite /top /zbetween !zify.
    assert (h := wunsigned_range (align_word ws_align ptr)).
    by rewrite wunsigned_add; last rewrite wunsigned_sub; lia.
  + move=> p hb.
    rewrite (write_read8 hm') subE /=.
    case: ifPn => [_|h].
    + by rewrite LE.read0.
    apply hzero.
    move: h hb; rewrite /between /zbetween wsize8 !zify /top.
    change x86_reg_size with Uptr.
    rewrite -wrepr_opp -!GRing.addrA -!wrepr_add.
    have ? := [elaborate (wunsigned_range (align_word ws_align ptr))].
    rewrite wunsigned_sub_if.
    rewrite wunsigned_add; last by lia.
    rewrite wunsigned_add; last by lia.
    case: ZleP; lia.
  + rewrite -WArray.arr_is_align.
    have /is_align_addE <- := [elaborate (is_align_mul ws (Z.of_nat n.+1))].
    rewrite Z.mul_comm wrepr_sub GRing.addrC GRing.subrK.
    by rewrite WArray.arr_is_align.
  by lia.
Local Transparent wsize_size Z.of_nat.
Qed.

Lemma unrolled_large_loopP s1 s2 :
  state_rel_unrolled_large unrolled_large_vars s1 s2 stk_max top ->
  exists s3,
    [/\ lsem lp (of_estate s2 fn (size lc + 4))
                (of_estate s3 fn (size lc + 4 + Z.to_nat (stk_max / wsize_size ws)))
      & state_rel_unrolled_large unrolled_large_vars s1 s3 0 top].
Proof.
  move=> hsr.
  have hlinear:
    [elaborate (is_linear_of lp fn (lc ++ unrolled_large_cmd rspn ws_align ws stk_max))].
  + by exists lfd.
  have [k [hmax hbound]]:
    exists k, (stk_max = Z.of_nat k * wsize_size ws)%Z
           /\ k <= Z.to_nat (stk_max / wsize_size ws).
  + have := halign.
    rewrite /is_align WArray.p_to_zE.
    move=> /eqP /Z.mod_divide [//|m h].
    exists (Z.to_nat m).
    split.
    + rewrite Z2Nat.id //.
      by have := wsize_size_pos ws; lia.
    by rewrite h Z.div_mul.
  rewrite -(Z.sub_diag stk_max).
  rewrite {1 3}hmax {hmax}.
  rewrite Z.div_mul // Nat2Z.id.
  elim: k s2 hbound hsr => [|k ih] s2 hbound hsr.
  + rewrite /= addn0 Z.sub_0_r.
    exists s2; split=> //.
    by apply Relation_Operators.rt_refl.
  have [s3 [hsem3 hsr3]] := ih _ (ltnW hbound) hsr.
  have hbound': (Z.of_nat k < stk_max / wsize_size ws)%Z.
  + by move/leP: hbound; lia.
  have [s4 [hsem4 hsr4]] := unrolled_large_bodyP hsr3 hbound'.
  exists s4; split=> //.
  by apply (lsem_trans hsem3).
Qed.

Lemma unrolled_large_initP (s1 : estate) :
  valid_between s1.(emem) top stk_max ->
  s1.(evm).[rspi] = Vword ptr ->
  exists s2,
    lsem lp (of_estate s1 fn (size lc)) (of_estate s2 fn (size lc + 4)) /\
    state_rel_unrolled_large unrolled_large_vars s1 s2 stk_max top.
Proof.
Local Opaque wsize_size.
  move=> hvalid hrsp.
  have hlinear:
    [elaborate (is_linear_of lp fn (lc ++ unrolled_large_cmd rspn ws_align ws stk_max))].
  + by exists lfd.
  eexists (Estate _ _ _); split.
  + apply: lsem_step4; rewrite /lsem1 /step.
    * rewrite -(addn0 (size lc)) (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite /get_var /= hrsp /=.
      rewrite /exec_sopn /= truncate_word_u /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
    * rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      have -> /=: exec_sopn (Oasm (ExtOp (Oset0 ws))) [::] = ok [:: @Vword ws 0].
      + rewrite /exec_sopn /= /sopn_sem /=.
        rewrite /Oset0_instr.
        by move /negP/negPf : hlarge => -> /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
    * rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite get_var_neq //.
      rewrite get_var_neq;
        last by move=> h; apply /rsp_nin /sv_of_listP;
        rewrite !in_cons /= -h eqxx /= ?orbT.
      rewrite /get_var /= hrsp /=.
      rewrite /exec_sopn /= !truncate_word_u /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
    * rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite get_var_eq /=; last by [].
      rewrite /exec_sopn /= !truncate_word_u /=.
      rewrite /of_estate /= /lnext_pc.
      by rewrite -addnS; reflexivity.
  split=> /=.
  + do 12 rewrite Vm.setP_neq //.
    by rewrite Vm.setP_eq /= wsize_ge_U256.
  split=> //=.
  + move=> p.
    by rewrite Z.sub_diag /between (negbTE (not_zbetween_neg _ _ _ _)).
  + by do 14 (rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; (left; reflexivity) ||
      right; apply /sv_of_listP; rewrite !in_cons /= eqxx /= ?orbT).
  + do 13 (rewrite Vm.setP_neq;
      last by [|
        apply /eqP => /(@inj_to_var _ _ _ _ _ _) |
        apply /eqP => h; apply /rsp_nin /sv_of_listP;
          rewrite !in_cons /= -h eqxx /= ?orbT]).
    by rewrite Vm.setP_eq.
  + by rewrite Vm.setP_eq.
  by lia.
Local Transparent wsize_size.
Qed.

Lemma unrolled_large_finalP (s1 s2 : estate) :
  state_rel_unrolled_large unrolled_large_vars s1 s2 0 top ->
  exists s3,
    lsem lp
      (of_estate s2 fn (size lc + 4 + Z.to_nat (stk_max / wsize_size ws)))
      (of_estate s3 fn (size lc + size (unrolled_large_cmd rspn ws_align ws stk_max))) /\
    state_rel_unrolled_large unrolled_large_vars s1 s3 0 ptr.
Proof.
  move=> hsr.
  have hlinear:
    [elaborate (is_linear_of lp fn (lc ++ unrolled_large_cmd rspn ws_align ws stk_max))].
  + by exists lfd.
  have ->: size (unrolled_large_cmd rspn ws_align ws stk_max) =
        (4 + Z.to_nat (stk_max / wsize_size ws)).+1.
  + rewrite /= size_map size_cat !size_map size_rev size_ziota /=.
    by rewrite addnS addn0 -addSn.
  eexists (Estate _ _ _); split=> /=.
  + apply: lsem_step1.
    rewrite /lsem1 /step.
    rewrite -addnA (find_instr_skip hlinear) /=.
    rewrite onth_map.
    rewrite oseq.onth_cat !size_map size_rev size_ziota.
    rewrite ltnn subnn /=.
    rewrite /eval_instr /=.
    rewrite /get_var /= hsr.(sr_tmp) /=.
    rewrite /exec_sopn /= truncate_word_u /=.
    rewrite /of_estate /= /lnext_pc /=.
    by rewrite -addnS; reflexivity.
  case: hsr => hvlr [hscs hmem hvalid hdisj hzero hvm htmp hrsp haligned hbound].
  split=> /=.
  + by rewrite Vm.setP_neq.
  split=> //=.
  + by rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; left; reflexivity.
  + by rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
  by rewrite Vm.setP_eq.
Qed.

Lemma unrolled_largeP (s1 : estate) :
  valid_between s1.(emem) top stk_max ->
  s1.(evm).[rspi] = Vword ptr ->
  exists s2,
    lsem lp
      (of_estate s1 fn (size lc))
      (of_estate s2 fn (size lc + size (unrolled_large_cmd rspn ws_align ws stk_max))) /\
    state_rel_unrolled_large unrolled_large_vars s1 s2 0 ptr.
Proof.
  move=> hvalid hrsp.
  have [s2 [hsem2 hsr2]] := unrolled_large_initP hvalid hrsp.
  have [s3 [hsem3 hsr3]] := unrolled_large_loopP hsr2.
  have [s4 [hsem4 hsr4]] := unrolled_large_finalP hsr3.
  exists s4; split=> //.
  apply (lsem_trans hsem2).
  by apply (lsem_trans hsem3).
Qed.

End LARGE.

Lemma unrolledP (s1 : estate) cmd vars :
  x86_stack_zero_unrolled rspn ws_align ws stk_max = (cmd, vars) ->
  lfd_body lfd = lc ++ cmd ->
  ~ Sv.In rspi vars ->
  valid_between s1.(emem) top stk_max ->
  s1.(evm).[rspi] = Vword ptr ->
  exists s2,
    lsem lp
      (of_estate s1 fn (size lc))
      (of_estate s2 fn (size lc + size cmd)) /\
    state_rel_unrolled_small vars s1 s2 0 ptr.
Proof.
  rewrite /x86_stack_zero_unrolled.
  case: ifPn => [hsmall|/negP hlarge] [<- <-] hbody rsp_nin hvalid hrsp.
  + exact: (unrolled_smallP hsmall hbody rsp_nin hvalid hrsp).
  have [s2 [hsem hsr]] := unrolled_largeP hlarge hbody rsp_nin hvalid hrsp.
  exists s2; split=> //.
  by case: hsr.
Qed.

End UNROLLED.

End RSP.

Lemma x86_stack_zero_cmd_no_ext_lbl szs rspn lbl ws_align ws stk_max cmd vars :
  x86_stack_zero_cmd szs rspn lbl ws_align ws stk_max = ok (cmd, vars) ->
  label_in_lcmd cmd = [::].
Proof.
  rewrite /x86_stack_zero_cmd.
  case: szs.
  + rewrite /x86_stack_zero_loop.
    by case: ifPn => _ [<- _].
  + rewrite /x86_stack_zero_loopSCT /x86_stack_zero_loop.
    by case: ifPn => _ [<- _].
  rewrite /x86_stack_zero_unrolled.
  by case: ifPn => _ [<- _] /=; elim: rev.
Qed.

Lemma x86_stack_zero_cmdP szs rspn lbl ws_align ws stk_max cmd vars :
  x86_stack_zero_cmd szs rspn lbl ws_align ws stk_max = ok (cmd, vars) ->
  stack_zeroization_proof.sz_cmd_spec rspn lbl ws_align ws stk_max cmd vars.
Proof.
  move=> hcmd rsp_nin lt_0_stk_max halign le_ws_ws_align lp fn lfd lc
    /negP hlabel hlfd hbody ls ptr hfn hpc hstack hrsp top hvalid.
  have [s2 [hsem hsr]]: [elaborate
    exists s2,
      lsem lp ls (of_estate s2 fn (size lc + size cmd))
      /\ state_rel_unrolled_small
          rspn ws_align ws stk_max ptr vars (to_estate ls) s2 0 ptr].
  + move: hcmd; rewrite /x86_stack_zero_cmd.
    case: szs.
    + move=> [hcmd].
      have {}hbody: lfd_body lfd = lc ++ cmd ++ [::].
      + by rewrite cats0.
      have [s2 [hsem hsr]] :=
        loopP lt_0_stk_max halign le_ws_ws_align hlfd hstack hlabel hcmd
          hbody rsp_nin (s1 := to_estate _) hvalid hrsp.
      exists s2; split=> //.
      + by rewrite -{1}hfn -{1}hpc of_estate_to_estate in hsem.
      by case: hsr.
    + move=> [].
      rewrite /x86_stack_zero_loopSCT.
      case hcmd: (x86_stack_zero_loop rspn lbl ws_align ws stk_max)
        => [cmd' vars'] [??]; subst cmd vars.
      have [s2 [hsem hsr]] :=
        loopP lt_0_stk_max halign le_ws_ws_align hlfd hstack hlabel hcmd
          hbody rsp_nin (s1 := to_estate _) hvalid hrsp.
      exists s2; split; last by case: hsr.
      rewrite -{1}hfn -{1}hpc of_estate_to_estate in hsem.
      apply: (lsem_step_end hsem).
      rewrite /lsem1 /step.
      have hlinear:
        [elaborate
          is_linear_of lp fn
            ((lc ++ cmd') ++
              [:: {| li_ii := dummy_instr_info;
                     li_i := Lopn [::] (Ox86 LFENCE) [::] |}])].
      + by rewrite -catA; exists lfd.
      rewrite -{1}size_cat -(addn0 (size _)).
      rewrite (find_instr_skip hlinear) /=.
      rewrite /eval_instr /=.
      rewrite /of_estate /=.
      by rewrite size_cat /= addnA addn1.
    move=> [hcmd].
    have :=
      unrolledP lt_0_stk_max halign le_ws_ws_align hlfd hstack hcmd
        hbody rsp_nin (s1 := to_estate _) hvalid hrsp.
    by rewrite -{1}hfn -{1}hpc of_estate_to_estate.

  exists (emem s2), (evm s2); split=> //.
  + by rewrite -hfn /of_estate -hsr.(sr_scs) in hsem.
  + move=> x hin.
    case: (x =P vid rspn) => [->|hneq].
    + by rewrite hsr.(sr_rsp).
    apply hsr.(sr_vm).
    by case/Sv.add_spec.
  + by apply hsr.(sr_mem).
  + have := hsr.(sr_zero).
    by rewrite wrepr0 GRing.addr0 Z.sub_0_r.
  exact: hsr.(sr_disjoint).
Qed.

End STACK_ZEROIZATION.
