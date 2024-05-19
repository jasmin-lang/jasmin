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
  arm_decl
  arm_extra
  arm_instr_decl
  arm_params_common_proof.
Require Export arm_stack_zeroization.

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

Let vsaved_sp := mk_var_i (to_var R02).
Let voff := mk_var_i (to_var R03).
Let vzero := mk_var_i (to_var R12).
Let vzf := mk_var_i (to_var ZF).
Let vflags := [seq mk_var_i (to_var f) | f <- rflags ].
Let leflags := [seq LLvar f | f <- vflags ].

Lemma store_zero_eval_instr lp ii ws e (ls:lstate) (w1 w2 : word Uptr) m' :
  (ws <= U32)%CMP ->
  get_var true (lvm ls) vzero = ok (@Vword Uptr 0) ->
  get_var true (lvm ls) rspi = ok (Vword w1) ->
  sem_fexpr (lvm ls) e >>= to_word Uptr = ok w2 ->
  write (lmem ls) Aligned (w1 + w2)%R (sz:=ws) 0 = ok m' ->
  let i := MkLI ii (store_zero rspi ws e) in
  eval_instr lp i ls = ok (lnext_pc (lset_mem ls m')).
Proof.
  move=> ws_small hvzero hrsp he hm'.
  rewrite /eval_instr /= /store_zero.
  have [mn hstore]: exists mn, store_mn_of_wsize ws = Some mn.
  + by case: ws ws_small {hm'} => //= _; eexists; reflexivity.
  rewrite hstore /= hvzero /=.
  rewrite (store_mn_of_wsizeP (w:=0%R) hstore) /=;
    last by rewrite (truncate_word_le _ ws_small) zero_extend0.
  by rewrite hrsp /= (truncate_word_u w1) /= he /= truncate_word_u /= hm' /=.
Qed.

Context (lp : lprog) (fn : funname).
Context (ws_align : wsize) (ws : wsize) (stk_max : Z).
Context (lt_0_stk_max : (0 < stk_max)%Z).
Context (halign : is_align stk_max ws).
Context (le_ws_ws_align : (ws <= ws_align)%CMP).
Context (ptr : pointer).
Context (hstack : (stk_max <= wunsigned (align_word ws_align ptr))%Z).
Let top := (align_word ws_align ptr - wrepr Uptr stk_max)%R.

#[local]
Lemma top_aligned : is_align top ws.
Proof.
  rewrite /top.
  apply is_align_add.
  + apply (is_align_m le_ws_ws_align).
    by apply do_align_is_align.
  move: halign; rewrite -WArray.arr_is_align => /is_align_addE <-.
  by rewrite GRing.addrN.
Qed.

Record state_rel_unrolled vars s1 s2 n (p:word Uptr) := {
  sr_scs : s1.(escs) = s2.(escs);
  sr_mem : mem_equiv s1.(emem) s2.(emem);
  sr_mem_valid : forall p, between top stk_max p U8 -> validw s2.(emem) Aligned p U8;
  sr_disjoint :
    forall p, disjoint_zrange top stk_max p (wsize_size U8) ->
      read s1.(emem) Aligned p U8 = read s2.(emem) Aligned p U8;
  sr_zero : forall p,
    between (top + wrepr _ n) (stk_max - n) p U8 -> read s2.(emem) Aligned p U8 = ok 0%R;
  sr_vm : s1.(evm) =[\ Sv.add rspi vars] s2.(evm) ;
  sr_vsaved : s2.(evm).[vsaved_sp] = Vword ptr;
  sr_rsp : s2.(evm).[rspi] = Vword p;
  sr_vzero : s2.(evm).[vzero] = @Vword Uptr 0; (* contrary to x86, not ws but U32 *)
  sr_aligned : is_align n ws;
  sr_bound : (0 <= n <= stk_max)%Z;
}.

Record state_rel_loop vars s1 s2 n p := {
  srl_off : s2.(evm).[voff] = Vword (wrepr Uptr n);
  srl_srs :> state_rel_unrolled vars s1 s2 n p
}.

Lemma state_rel_unrolledI vars1 vars2 s1 s2 n p :
  Sv.Subset vars1 vars2 ->
  state_rel_unrolled vars1 s1 s2 n p ->
  state_rel_unrolled vars2 s1 s2 n p.
Proof.
  move=> hsubset hsr.
  case: hsr => hscs hmem hvalid hdisj hzero hvm hsaved hrsp hvzero haligned hbound.
  split=> //.
  apply: eq_exI hvm.
  by apply (SvD.F.add_s_m erefl hsubset).
Qed.

Lemma state_rel_loopI vars1 vars2 s1 s2 n p :
  Sv.Subset vars1 vars2 ->
  state_rel_loop vars1 s1 s2 n p ->
  state_rel_loop vars2 s1 s2 n p.
Proof.
  move=> hsubset hsr.
  case: hsr => hoff hsr.
  split=> //.
  by apply (state_rel_unrolledI hsubset hsr).
Qed.

Section INIT.

Definition sz_init_vars :=
  sv_of_list v_var [:: vsaved_sp; voff; vzero].

Context (pre pos : seq linstr).
Context (hbody : is_linear_of lp fn (pre ++ sz_init rspi ws_align stk_max ++ pos)).
Context (rsp_nin : ~ Sv.In rspi sz_init_vars).

Lemma sz_initP (s1 : estate) :
  valid_between (emem s1) top stk_max ->
  s1.(evm).[rspi] = Vword ptr ->
  exists s2,
    lsem lp (of_estate s1 fn (size pre)) (of_estate s2 fn (size pre + size (sz_init rspi ws_align stk_max))) /\
    state_rel_loop sz_init_vars s1 s2 stk_max top.
Proof.
  move=> hvalid hrsp.
  move: hbody => /=.
  set isave_sp := li_of_fopn_args _ (ARMFopn.mov _ _).
  set iload_off := li_of_fopn_args _ (ARMFopn.li _ _).
  set ialign := li_of_fopn_args _ (ARMFopn.align _ _ _).
  set istore_sp := li_of_fopn_args _ (ARMFopn.mov _ _).
  set isub_sp := li_of_fopn_args _ (ARMFopn.sub _ _ _).
  set izero := li_of_fopn_args _ (ARMFopn.movi _ _).
  move=> hbody'.

  eexists (Estate _ _ _); split=> /=.
  apply: lsem_step6.

  + apply: (eval_lsem1 hbody') => //.
    apply: ARMFopnP.mov_eval_instr.
    rewrite /get_var hrsp /=.
    reflexivity.

  + rewrite /lnext_pc /=.
    rewrite -cat_rcons in hbody'.
    apply: (eval_lsem1 hbody' _ _ ARMFopnP.li_eval_instr) => //.
    by rewrite size_rcons.

  + rewrite /lnext_pc /=.
    rewrite -2!cat_rcons in hbody'.
    apply: (eval_lsem1 hbody') => //=; first by rewrite !size_rcons.
    apply: ARMFopnP.align_eval_instr.
    rewrite /= get_var_neq //; last by move=> /(@inj_to_var _ _ _ _ _ _).
    by rewrite get_var_eq.

  + rewrite /lnext_pc /=.
    rewrite -3!cat_rcons in hbody'.
    apply: (eval_lsem1 hbody') => //=.
    * by rewrite !size_rcons.
    apply: ARMFopnP.mov_eval_instr.
    by rewrite get_var_eq.

  + rewrite /lnext_pc /=.
    rewrite -4!cat_rcons in hbody'.
    apply: (eval_lsem1 hbody') => //; first by rewrite !size_rcons.
    apply: ARMFopnP.sub_eval_instr => /=.
    * rewrite get_var_eq /=; last by []. reflexivity.
    rewrite get_var_neq;
      last by move=> h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
    rewrite get_var_neq; last by move=> /(@inj_to_var _ _ _ _ _ _).
    by rewrite get_var_eq.

  rewrite /lnext_pc /=.
  rewrite -5!cat_rcons in hbody'.
  apply: (eval_lsem1 hbody') => //=; first by rewrite !size_rcons.
  rewrite ARMFopnP.movi_eval_instr; last by left.
  by rewrite /lnext_pc /= -addn4 !addSnnS.

  split=> /=.
  + do 4 (rewrite Vm.setP_neq;
      last by [
        apply /eqP => /(@inj_to_var _ _ _ _ _ _) |
        apply /eqP => h; apply /rsp_nin /sv_of_listP;
          rewrite !in_cons /= -h eqxx /= ?orbT]).
    by rewrite Vm.setP_eq.

  split=> //=.
  + move=> p.
    by rewrite Z.sub_diag /between (negbTE (not_zbetween_neg _ _ _ _)).
  + do 4 (rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; (left; reflexivity) ||
      right; apply /sv_of_listP; rewrite !in_cons /= eqxx /= ?orbT).
    apply: eq_ex_set_r.
    by do 3 (move=> /Sv.add_spec /Decidable.not_or [] ?).
    rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; by repeat (apply/Sv.add_spec; ((by left) || right)).
    done.
  + do 4 (rewrite Vm.setP_neq;
      last by [
        apply /eqP => /(@inj_to_var _ _ _ _ _ _) |
        apply /eqP => h; apply /rsp_nin /sv_of_listP;
          rewrite !in_cons /= -h eqxx /= ?orbT]).
    rewrite Vm.setP_neq; first by rewrite Vm.setP_eq.
    by apply/eqP => /(@inj_to_var _ _ _ _ _ _).
  + rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
    by rewrite Vm.setP_eq.
  + rewrite Vm.setP_eq /=.
    by rewrite wrepr0.
  by lia.
Qed.

End INIT.

Section LOOP.

Definition sz_loop_vars :=
  sv_of_list v_var [:: voff & vflags].

Context (hsmall : (ws <= U32)%CMP).
Context (lbl : label.label) (pre pos : seq linstr).
Context (hbody : is_linear_of lp fn (pre ++ sz_loop rspi lbl ws ++ pos)).
Context (rsp_nin : ~ Sv.In rspi sz_loop_vars).
Context (hlabel : ~~ has (is_label lbl) pre).

Lemma loop_bodyP vars s1 s2 n :
  Sv.Subset sz_loop_vars vars ->
  state_rel_loop vars s1 s2 n top ->
  (0 < n)%Z ->
  exists s3,
    [/\ lsem lp (of_estate s2 fn (size pre + 1))
                (of_estate s3 fn (size pre + 3)),
        s3.(evm).[vzf] = Vbool (ZF_of_word (wrepr U32 n - wrepr U32 (wsize_size ws)))
      & state_rel_loop vars s1 s3 (n - wsize_size ws) top].
Proof.
  move=> hsubset hsr hlt.
  have hn: (0 < wsize_size ws <= n)%Z.
  + split=> //.
    have := hsr.(sr_aligned).
    rewrite /is_align WArray.p_to_zE.
    move=> /eqP /Z.mod_divide [//|m ?].
    have ? := wsize_size_pos ws.
    have: (0 < m)%Z; nia.
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
  apply: lsem_step2.
  + rewrite
      /lsem1 /step (find_instr_skip hbody) /= /eval_instr /=
      /get_var hsr.(srl_off) /= /exec_sopn /= !truncate_word_u /= wsub_wnot1
      /of_estate /= /lnext_pc /= -addnS.
    reflexivity.
  + rewrite /lsem1 /step (find_instr_skip hbody) /= -(addn1 2) addnA addn1.
    apply: store_zero_eval_instr => //=.
    + do 5 (rewrite (@get_var_neq _ _ _ vzero);
        last by [|move=> /(@inj_to_var _ _ _ _ _ _)]).
      by rewrite /get_var hsr.(sr_vzero).
    + do 5 (rewrite (@get_var_neq _ _ _ rspi);
        last by [|move=> /= h; apply /rsp_nin /sv_of_listP;
        rewrite !in_cons /= -h eqxx /= ?orbT]).
      by rewrite /get_var hsr.(sr_rsp); reflexivity.
    + rewrite get_var_eq //= truncate_word_u; reflexivity.
    exact: hm'.
  + do 3 (rewrite Vm.setP_neq;
      last by [|apply /eqP => /(@inj_to_var _ _ _ _ _ _)]).
    by rewrite Vm.setP_eq.
  case: hsr => hoff [hscs hmem hvalid hdisj hzero hvm hsaved hrsp hvzero haligned hbound].
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
    change arm_reg_size with Uptr.
    rewrite -wrepr_sub -wrepr_opp -!GRing.addrA -!wrepr_add.
    have ? := [elaborate (wunsigned_range (align_word ws_align ptr))].
    rewrite wunsigned_sub_if.
    rewrite wunsigned_add; last by lia.
    rewrite wunsigned_add; last by lia.
    case: ZleP; lia.
  + by do 5 (rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; right;
      apply /hsubset /sv_of_listP; rewrite !in_cons /= eqxx /= ?orbT).
  + rewrite Vm.setP_neq; last by apply /eqP => /(@inj_to_var _ _ _ _ _ _).
    by rewrite !Vm.setP_neq.
  + rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
    by do 4 rewrite Vm.setP_neq //.
  + by do 5 (rewrite Vm.setP_neq;
      last by [|apply /eqP => /(@inj_to_var _ _ _ _ _ _)]).
  + rewrite -WArray.arr_is_align wrepr_sub.
    have /is_align_addE <- := [elaborate (is_align_mul ws 1)].
    rewrite Z.mul_1_r GRing.addrC GRing.subrK.
    by rewrite WArray.arr_is_align.
  by lia.
Qed.

Lemma loopP vars s1 s2 n :
  Sv.Subset sz_loop_vars vars ->
  state_rel_loop vars s1 s2 n top ->
  (0 < n)%Z ->
  exists s3,
    [/\ lsem lp (of_estate s2 fn (size pre + 1))
                (of_estate s3 fn (size pre + 4))
      & state_rel_loop vars s1 s3 0 top].
Proof.
  move=> hsubset hsr hlt.
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
  have [s3 [hsem3 hzf3 hsr3]] := loop_bodyP hsubset hsr hlt.
  have: (k = 0 \/ 0 < k)%coq_nat by lia.
  case=> hk.
  + subst k.
    move: hn; rewrite Z.mul_1_l => ?; subst n.
    exists s3; split.
    + apply: (lsem_step_end hsem3).
      by rewrite /lsem1 /step (find_instr_skip hbody) /= /eval_instr /=
         /get_var /= hzf3 /= GRing.addrN /ZF_of_word /= eqxx /= /setpc /=
         /lnext_pc /= -addnS.
    by move: hsr3; rewrite Z.sub_diag.
  have hlt3: (0 < n - wsize_size ws)%Z by nia.
  have hn3: (n - wsize_size ws)%Z = (Z.of_nat k * wsize_size ws)%Z by lia.
  have [s4 [hsem4 hsr4]] := ih _ _ hsr3 hlt3 hn3.
  exists s4; split=> //.
  apply: (lsem_trans hsem3).
  apply: lsem_step hsem4.
  rewrite /lsem1 /step.
  rewrite (find_instr_skip hbody) /=.
  rewrite /eval_instr /=.
  rewrite /get_var /= hzf3 /=.
  have ->: ~~ ZF_of_word (wrepr U32 n - wrepr U32 (wsize_size ws)).
  + rewrite /ZF_of_word; apply /eqP => /(f_equal wunsigned).
    rewrite wunsigned0 -wrepr_sub wunsigned_repr_small; first by lia.
    change U32 with Uptr.
    have := hsr.(sr_bound).
    have! := (wunsigned_range (align_word ws_align ptr)).
    have := wsize_size_pos ws.
    by lia.
  have [lfd -> -> /=] := hbody.
  rewrite (find_label_cat_hd (sip := sip_of_asm_e) _ hlabel).
  rewrite (find_labelE (sip := sip_of_asm_e)) /=.
  rewrite /is_label /= eqxx /=.
  rewrite /setcpc /=.
  by rewrite -addnS.
Qed.

Lemma sz_loopP vars s1 s2 n :
  Sv.Subset sz_loop_vars vars ->
  state_rel_loop vars s1 s2 n top ->
  (0 < n)%Z ->
  exists s3,
    [/\ lsem lp (of_estate s2 fn (size pre))
                (of_estate s3 fn (size pre + size (sz_loop rspi lbl ws)))
      & state_rel_loop vars s1 s3 0 top].
Proof.
  move=> hsubset hsr hlt.
  have [s3 [hsem3 hsr3]] := loopP hsubset hsr hlt.
  exists s3; split=> //.
  apply: (lsem_step _ hsem3).
  apply: (eval_lsem1 hbody) => //.
  by rewrite addn1.
Qed.

End LOOP.

Section RESTORE.

(* We write to [rspi], so we assume that it is different from the variables
   occurring in the invariant predicate. *)
Definition restore_sp_vars :=
  sv_of_list v_var [:: voff; vzero].

Context (pre pos : seq linstr).
Context (hbody : is_linear_of lp fn (pre ++ restore_sp rspi ++ pos)).
Context (rsp_nin : ~ Sv.In rspi restore_sp_vars).

Lemma restore_spP vars (s1 s2 : estate) :
  state_rel_unrolled vars s1 s2 0 top ->
  exists s3,
    lsem lp
      (of_estate s2 fn (size pre))
      (of_estate s3 fn (size pre + size (restore_sp rspi))) /\
    state_rel_unrolled vars s1 s3 0 ptr.
Proof.
  move=> hsr.
  eexists (Estate _ _ _); split=> /=.
  + apply: (eval_lsem_step1 hbody) => //.
    rewrite addn1.
    apply: ARMFopnP.mov_eval_instr.
    by rewrite /get_var /= hsr.(sr_vsaved) /=; reflexivity.
  case: hsr => hscs hmem hvalid hdisj hzero hvm hsaved hrsp hvzero haligned hbound.
  split=> //=.
  + by rewrite (eq_ex_set_l _ (eq_ex_refl _));
      last by case; apply Sv.add_spec; left; reflexivity.
  + rewrite Vm.setP /=.
    by case: eq_op.
  + by rewrite Vm.setP_eq.
  + by rewrite Vm.setP_neq;
      last by apply /eqP => h; apply /rsp_nin /sv_of_listP;
      rewrite !in_cons /= -h eqxx /= ?orbT.
Qed.

End RESTORE.

Section UNROLLED.

Context (hsmall : (ws <= U32)%CMP).
Context (pre pos : seq linstr).
Context (hbody : is_linear_of lp fn (pre ++ sz_unrolled rspi ws stk_max ++ pos)).

Lemma unrolled_bodyP vars s1 s2 n :
  state_rel_unrolled vars s1 s2 (stk_max - Z.of_nat n * wsize_size ws) top ->
  (Z.of_nat n < stk_max / wsize_size ws)%Z ->
  exists s3,
    [/\ lsem lp (of_estate s2 fn (size pre + n))
                (of_estate s3 fn (size pre + n.+1))
      & state_rel_unrolled vars s1 s3 (stk_max - Z.of_nat n.+1 * wsize_size ws) top].
Proof.
Local Opaque wsize_size Z.of_nat.
  move=> hsr hlt.
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
    rewrite /lsem1 /step (find_instr_skip hbody) /=.
    rewrite oseq.onth_cat !size_map size_rev size_ziota.
    have hlt'': n < Z.to_nat (stk_max / wsize_size ws) by apply /ltP; lia.
    rewrite hlt''.
    rewrite onth_map.
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
    rewrite addnS.
    apply: store_zero_eval_instr => //=.
    + by rewrite /get_var hsr.(sr_vzero).
    + by rewrite /get_var hsr.(sr_rsp); reflexivity.
    + by rewrite truncate_word_u; reflexivity.
    apply hm'.
  case: hsr => hscs hmem hvalid hdisj hzero hvm hsaved hrsp hvzero haligned hbound.
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
    change arm_reg_size with Uptr.
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

Lemma sz_unrolledP vars s1 s2 :
  state_rel_unrolled vars s1 s2 stk_max top ->
  exists s3,
    [/\ lsem lp (of_estate s2 fn (size pre))
                (of_estate s3 fn (size pre + size (sz_unrolled rspi ws stk_max)))
      & state_rel_unrolled vars s1 s3 0 top].
Proof.
  move=> hsr.
  rewrite /sz_unrolled size_map size_rev size_ziota.
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
  have [s4 [hsem4 hsr4]] := unrolled_bodyP hsr3 hbound'.
  exists s4; split=> //.
  by apply (lsem_trans hsem3).
Qed.

End UNROLLED.

Section STACK_ZERO_LOOP.

Context (hsmall : (ws <= U32)%CMP).
Context (lbl : label.label) (pre pos : seq linstr).
Context (hbody : is_linear_of lp fn (pre ++ stack_zero_loop rspi lbl ws_align ws stk_max ++ pos)).
Context (rsp_nin : ~ Sv.In rspi stack_zero_loop_vars).
Context (hlabel : ~~ has (is_label lbl) pre).

Lemma sz_init_no_lbl : ~~ has (is_label lbl) (sz_init rspi ws_align stk_max).
Proof. done. Qed.

Lemma stack_zero_loopP (s1 : estate) :
  valid_between (emem s1) top stk_max ->
  (evm s1).[rspi] = Vword ptr ->
  exists s2,
    [/\ lsem lp (of_estate s1 fn (size pre))
                (of_estate s2 fn (size pre + size (stack_zero_loop rspi lbl ws_align ws stk_max)))
      & state_rel_unrolled stack_zero_loop_vars s1 s2 0 ptr].
Proof.
  move=> hvalid hrsp.
  move: hbody; rewrite /stack_zero_loop -!catA => hbody'.
  have hsubset_init: Sv.Subset sz_init_vars stack_zero_loop_vars.
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /= !eqxx ?orbT /=.
  have rsp_nin_init: ~ Sv.In rspi sz_init_vars.
  + by move=> /hsubset_init.
  have [s2 [hsem2 hsr2]] := sz_initP hbody' rsp_nin_init hvalid hrsp.
  move: hbody'; rewrite catA => hbody'.
  have hsubset_loop: Sv.Subset sz_loop_vars stack_zero_loop_vars.
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /= !eqxx ?orbT /=.
  have rsp_nin_loop: ~ Sv.In rspi sz_loop_vars.
  + by move=> /hsubset_loop.
  have hlabel_loop: ~~ has (is_label lbl) (pre ++ sz_init rspi ws_align stk_max).
  + by rewrite has_cat negb_or hlabel sz_init_no_lbl.
  have hsr2' := state_rel_loopI hsubset_init hsr2.
  have [s3 [hsem3 hsr3]] :=
    sz_loopP hsmall hbody' rsp_nin_loop hlabel_loop hsubset_loop hsr2' lt_0_stk_max.
  move: hbody'; rewrite catA => hbody'.
  have hsubset_restore: Sv.Subset restore_sp_vars stack_zero_loop_vars.
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /= !eqxx ?orbT /=.
  have rsp_nin_restore: ~ Sv.In rspi restore_sp_vars.
  + by move=> /hsubset_restore.
  have [s4 [hsem4 hsr4]] := restore_spP hbody' rsp_nin_restore hsr3.

  exists s4; split=> //.
  apply (lsem_trans hsem2).
  rewrite -size_cat.
  apply (lsem_trans hsem3).
  rewrite -!size_cat !catA (size_cat _ (restore_sp _)).
  exact: hsem4.
Qed.

End STACK_ZERO_LOOP.

Section STACK_ZERO_UNROLLED.

Context (hsmall : (ws <= U32)%CMP).
Context (pre pos : seq linstr).
Context (hbody : is_linear_of lp fn (pre ++ stack_zero_unrolled rspi ws_align ws stk_max ++ pos)).
Context (rsp_nin : ~ Sv.In rspi stack_zero_unrolled_vars).

Lemma stack_zero_unrolledP (s1 : estate) :
  valid_between (emem s1) top stk_max ->
  (evm s1).[rspi] = Vword ptr ->
  exists s2,
    [/\ lsem lp (of_estate s1 fn (size pre))
                (of_estate s2 fn (size pre + size (stack_zero_unrolled rspi ws_align ws stk_max)))
      & state_rel_unrolled stack_zero_unrolled_vars s1 s2 0 ptr].
Proof.
  move=> hvalid hrsp.
  move: hbody; rewrite /stack_zero_loop -!catA => hbody'.
  have hsubset_init: Sv.Subset sz_init_vars stack_zero_unrolled_vars.
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /= !eqxx ?orbT /=.
  have rsp_nin_init: ~ Sv.In rspi sz_init_vars.
  + by move=> /hsubset_init.
  have [s2 [hsem2 hsr2]] := sz_initP hbody' rsp_nin_init hvalid hrsp.
  move: hbody'; rewrite catA => hbody'.
  have hsr2' := state_rel_unrolledI hsubset_init hsr2.
  have [s3 [hsem3 hsr3]] := sz_unrolledP hsmall hbody' hsr2'.
  move: hbody'; rewrite catA => hbody'.
  have hsubset_restore: Sv.Subset restore_sp_vars stack_zero_loop_vars.
  + move=> x /sv_of_listP hin.
    apply /sv_of_listP.
    move: hin; apply: allP.
    by rewrite /= !eqxx ?orbT /=.
  have rsp_nin_restore: ~ Sv.In rspi restore_sp_vars.
  + by move=> /hsubset_restore.
  have [s4 [hsem4 hsr4]] := restore_spP hbody' rsp_nin_restore hsr3.

  exists s4; split=> //.
  apply (lsem_trans hsem2).
  rewrite -size_cat.
  apply (lsem_trans hsem3).
  rewrite -!size_cat !catA (size_cat _ (restore_sp _)).
  exact: hsem4.
Qed.

End STACK_ZERO_UNROLLED.

End RSP.

Lemma sz_init_no_ext_lbl rsp ws_align stk_max :
  label_in_lcmd (sz_init rsp ws_align stk_max) = [::].
Proof. done. Qed.

Lemma store_zero_no_ext_lbl ii rsp ws off :
  get_label (MkLI ii (store_zero rsp ws off)) = None.
Proof. by rewrite /store_zero; case: store_mn_of_wsize. Qed.

Lemma arm_stack_zero_cmd_not_ext_lbl szs rspn lbl ws_align ws stk_max cmd vars :
  stack_zeroization_cmd szs rspn lbl ws_align ws stk_max = ok (cmd, vars) ->
  label_in_lcmd cmd = [::].
Proof.
  rewrite /stack_zeroization_cmd.
  t_xrbindP=> _.
  case: szs => //.
  + move=> [<- _].
    rewrite /stack_zero_loop !label_in_lcmd_cat sz_init_no_ext_lbl.
    by rewrite /= store_zero_no_ext_lbl.
  + move=> [<- _].
    rewrite /stack_zero_unrolled !label_in_lcmd_cat sz_init_no_ext_lbl.
    rewrite /= cats0.
    rewrite /sz_unrolled.
    by elim: rev => [//|?? ih] /=; rewrite store_zero_no_ext_lbl.
Qed.

Lemma arm_stack_zero_cmdP szs rspn lbl ws_align ws stk_max cmd vars :
  stack_zeroization_cmd szs rspn lbl ws_align ws stk_max = ok (cmd, vars) ->
  stack_zeroization_proof.sz_cmd_spec rspn lbl ws_align ws stk_max cmd vars.
Proof.
  move=> hcmd rsp_nin lt_0_stk_max halign le_ws_ws_align lp fn lfd lc
    /negP hlabel hlfd hbody ls ptr hfn hpc hstack hrsp top hvalid.
  have [s2 [hsem hsr]]: [elaborate
    exists s2,
      lsem lp ls (of_estate s2 fn (size lc + size cmd))
      /\ state_rel_unrolled
          rspn ws_align ws stk_max ptr vars (to_estate ls) s2 0 ptr].
  + move: hcmd; rewrite /stack_zeroization_cmd.
    t_xrbindP=> ws_small.
    case: szs => //.
    + move=> [??]; subst cmd vars.
      have hlinear: [elaborate
        is_linear_of lp fn
          (lc
          ++ stack_zero_loop (vid rspn) lbl ws_align ws stk_max
          ++ [::])].
      + by rewrite cats0; exists lfd.
        subst top.
      have := stack_zero_loopP
          lt_0_stk_max halign le_ws_ws_align hstack ws_small hlinear rsp_nin
          hlabel (s1 := to_estate _) hvalid hrsp.
      by rewrite -{1}hfn -{1}hpc of_estate_to_estate.
    + move=> [??]; subst cmd vars.
      have hlinear: [elaborate
        is_linear_of lp fn
          (lc
          ++ stack_zero_unrolled (vid rspn) ws_align ws stk_max
          ++ [::])].
      + by rewrite cats0; exists lfd.
      have := stack_zero_unrolledP
          lt_0_stk_max halign le_ws_ws_align hstack ws_small hlinear rsp_nin
          (s1 := to_estate _) hvalid hrsp.
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
