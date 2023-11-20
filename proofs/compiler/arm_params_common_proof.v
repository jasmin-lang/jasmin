From Coq Require Import Lia.
From mathcomp Require Import
  all_ssreflect
  all_algebra.

From mathcomp Require Import word_ssrZ.

Require Import
  arch_params
  compiler_util
  expr
  fexpr
  fexpr_sem
  linear
  linear_sem
  linear_facts
  psem.
Require Import
  arch_decl
  arch_extra
  sem_params_of_arch_extra.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl.
Require Export arm_params_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Section.

Context
  {atoI  : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {call_conv : calling_convention}.

#[local] Existing Instance withsubword.

Section ARM_OP.

(* Linear state after executing a linear instruction [Lopn]. *)
Notation next_ls ls m vm :=
  {|
    lscs := lscs ls;
    lmem := m;
    lvm := vm;
    lfn := lfn ls;
    lpc := lpc ls + 1;
  |}
  (only parsing).

Notation next_vm_ls ls vm := (next_ls ls (lmem ls) vm) (only parsing).
Notation next_mem_ls ls m := (next_ls ls m (lvm ls)) (only parsing).

Context
  (xname : Ident.ident)
  (vi : var_info).

Notation x :=
  {|
    v_var := {| vname := xname; vtype := sword reg_size; |};
    v_info := vi;
  |}.

(* Most ARM instructions with default options are executed as follows:
   1. Unfold instruction execution definitions, e.g. [eval_instr].
   2. Rewrite argument hypotheses, i.e. [sem_pexpr].
   3. Unfold casting definitions in result, e.g. [zero_extend] and
      [pword_of_word].
   4. Rewrite result hypotheses, i.e. [write_lval].
 *)

Ltac t_arm_op :=
  rewrite /eval_instr /= /sem_sopn /= /exec_sopn /get_gvar /=;
  t_simpl_rewrites;
  rewrite /of_estate /= /with_vm /=;
  repeat rewrite truncate_word_u /=;
  rewrite ?zero_extend_u addn1;
  t_simpl_rewrites.

Lemma arm_op_addi_eval_instr lp ls ii y imm wy :
  get_var true (lvm ls) (v_var y) = ok (Vword wy)
  -> let: li := li_of_fopn_args ii (arm_op_addi x y imm) in
     let: wx' := Vword (wy + wrepr reg_size imm)in
     let: vm' := (lvm ls).[v_var x <- wx'] in
     eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof. move=> ?. by t_arm_op. Qed.

Lemma arm_op_subi_eval_instr lp ls ii y imm wy :
  get_var true (lvm ls) (v_var y) = ok (Vword wy)
  -> let: li := li_of_fopn_args ii (arm_op_subi x y imm) in
     let: wx' := Vword (wy - wrepr reg_size imm)in
     let: vm' := (lvm ls).[v_var x <- wx'] in
     eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof. move=> ?. t_arm_op. by rewrite wsub_wnot1. Qed.

Lemma arm_op_align_eval_instr lp ls ii y al (wy:word Uptr) :
  get_var true (lvm ls) (v_var y) = ok (Vword wy)
  -> let: li := li_of_fopn_args ii (arm_op_align x y al) in
     let: wx' := Vword (align_word al wy) in
     let: vm' := (lvm ls).[v_var x <- wx'] in
     eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=> hgety.
  Opaque wsize_size.
  t_arm_op.
  Transparent wsize_size.
  by rewrite wrepr_wnot ZlnotE Z.sub_1_r Z.add_1_r Z.succ_pred.
Qed.

Lemma arm_op_sub_eval_instr lp ls ii y (wy : word Uptr) z (wz : word Uptr) :
  get_var true (lvm ls) (v_var y) = ok (Vword wy)
  -> get_var true (lvm ls) (v_var z) = ok (Vword wz)
  -> let: li := li_of_fopn_args ii (arm_op_sub x y z) in
     let: wx' := Vword (wy - wz)in
     let: vm' := (lvm ls).[v_var x <- wx'] in
     eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof. move=> ??. t_arm_op. by rewrite wsub_wnot1. Qed.

Lemma arm_op_mov_eval_instr lp ls ii y (wy: word Uptr) :
  get_var true (lvm ls) (v_var y) = ok (Vword wy)
  -> let: li := li_of_fopn_args ii (arm_op_mov x y) in
     let: vm' := (lvm ls).[v_var x <- Vword wy] in
     eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof. move=> hgety. by t_arm_op. Qed.

Lemma arm_op_movi_eval_instr lp ls ii imm :
  (is_expandable imm \/ is_w16_encoding imm) ->
  let: li := li_of_fopn_args ii (arm_op_movi x imm) in
  let: vm' := (lvm ls).[v_var x <- Vword (wrepr U32 imm)] in
  eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof. move=> _. by t_arm_op. Qed.

Lemma arm_op_str_off_eval_instr lp ls m' ii y off wx (wy : word reg_size) :
  get_var true (lvm ls) (v_var x) = ok (Vword wx)
  -> get_var true (lvm ls) (v_var y) = ok (Vword wy)
  -> write (lmem ls) (wx + wrepr Uptr off)%R wy = ok m'
  -> let: li := li_of_fopn_args ii (arm_op_str_off y x off) in
     eval_instr lp li ls = ok (next_mem_ls ls m').
Proof. move=> hgety hgetx hwrite. by t_arm_op. Qed.

End ARM_OP.

Lemma wbit_n_add_aux x y z :
  (0 < x)%Z
  -> (y < x)%Z
  -> (z < x)%Z
  -> (x * y + z < x * x)%Z.
Proof. nia. Qed.

Lemma wbit_n_add ws n lbs hbs (i : nat) :
  let: n2 := (2 ^ n)%Z in
  (n2 * n2 <= wbase ws)%Z
  -> (0 <= lbs < n2)%Z
  -> (0 <= hbs < n2)%Z
  -> let b :=
       if (i <? n)%Z
       then wbit_n (wrepr ws lbs) i
       else wbit_n (wrepr ws hbs) (i - Z.to_nat n)
     in
     wbit_n (wrepr ws (2 ^ n * hbs + lbs)) i = b.
Proof.
  move=> hn hlbs hhbs.

  have h0i : (0 <= i)%Z.
  - exact: Zle_0_nat.

  have h0n : (0 <= n)%Z.
  - case: (Z.le_gt_cases 0 n) => h; first done.
    rewrite (Z.pow_neg_r _ _  h) in hlbs.
    lia.

  have hrange : (0 <= 2 ^ n * hbs + lbs < wbase ws)%Z.
  - split; first lia.
    apply: (Z.lt_le_trans _ _ _ _ hn).
    apply: wbit_n_add_aux; lia.

  case: ZltP => hi /=.

  all: rewrite wbit_nE.
  all: rewrite (wunsigned_repr_small hrange).

  - rewrite -(Zplus_minus i n).
    rewrite Z.pow_add_r; last lia; last done.
    rewrite Z.add_comm -Z.mul_assoc Z.mul_comm.
    rewrite Z_div_plus; first last.
    + apply/Z.lt_gt. by apply: Z.pow_pos_nonneg.

    rewrite Z.odd_add.
    rewrite Z_odd_pow_2; last lia.
    rewrite Bool.xorb_false_r.

    rewrite wbit_nE.
    rewrite wunsigned_repr_small; first done.
    lia.

  rewrite -(Zplus_minus n i).
  rewrite (Z.pow_add_r _ _ _ h0n); last lia.
  rewrite -Z.div_div; last lia; last lia.
  rewrite Z.add_comm Z.mul_comm.
  rewrite Z_div_plus; last lia.
  rewrite (Zdiv_small _ _ hlbs) /=.

  rewrite wbit_nE.
  rewrite wunsigned_repr_small; first last.
  - split; first lia.
    apply: (Z.lt_le_trans _ _ _ _ hn).
    rewrite -Z.pow_twice_r.
    apply: (Z.lt_le_trans _ (2 ^ n)); first lia.
    apply: Z.pow_le_mono_r; lia.

  rewrite int_of_Z_PoszE.
  rewrite Nat2Z.n2zB; first by rewrite Z2Nat.id.
  apply/ZNleP.
  rewrite (Z2Nat.id _ h0n).
  by apply/Z.nlt_ge.
Qed.

Lemma mov_movt_aux n x y :
  (0 < n)%Z
  -> (0 <= y < n)%Z
  -> (0 <= n * x + y < n * n)%Z
  -> (0 <= x < n)%Z.
Proof. nia. Qed.

Lemma mov_movt n hbs lbs :
  (0 <= n < wbase reg_size)%Z
  -> Z.div_eucl n (wbase U16) = (hbs, lbs)
  -> let: h := wshl (zero_extend U32 (wrepr U16 hbs)) 16 in
     let: l := wand (wrepr U32 lbs) (zero_extend U32 (wrepr U16 (-1))) in
     wor h l = wrepr U32 n.
Proof.
  move=> hn.

  have := Z_div_mod n (wbase U16) (wbase_pos U16).
  case: Z.div_eucl => [h l] [? hlbs] [? ?]; subst n h l.

  rewrite wshl_sem; last done.
  rewrite (wand_small hlbs).
  rewrite -wrepr_mul.

  have hhbs : (0 <= hbs < wbase U16)%Z.
  - exact: (mov_movt_aux _ hlbs hn).

  rewrite (wunsigned_repr_small hhbs).
  Opaque Z.pow.
  rewrite wbaseE /=.

  apply/eqP/eq_from_wbit_n.
  move=> [i hrangei] /=.
  rewrite worE.

  rewrite wbit_n_add; first last.
  - by rewrite wbaseE /= in hhbs.
  - by rewrite wbaseE /= in hlbs.
  - done.

  case: ZltP => h.

  - rewrite wbit_lower_bits_0 /=; first done.
    + by have := Zle_0_nat i.
    rewrite wbaseE /= /arm_reg_size in hn.
    lia.

  rewrite (wbit_higher_bits_0 (n := 16) _ hlbs); first last.
  - split; last by apply/ZNltP. by apply/Z.nlt_ge.
  - done.

  rewrite orbF.
  rewrite wbit_pow_2; first done; first done.
  move: h => /Z.nlt_ge h.
  apply/andP.
  split.
  - apply/ZNleP. by rewrite Z2Nat.id.

  by apply: ltnSE.
Qed.

Lemma arm_cmd_load_large_imm_lsem lp fn s ii P Q xname imm :
  let: x := {| vname := xname; vtype := sword reg_size; |} in
  let: xi := mk_var_i x in
  let: lcmd := map (li_of_fopn_args ii) (arm_cmd_load_large_imm xi imm) in
  is_linear_of lp fn (P ++ lcmd ++ Q)
  -> (0 <= imm < wbase reg_size)%Z
  -> exists vm',
       let: ls := of_estate s fn (size P) in
       let: ls' :=
         {|
           lscs := lscs ls;
           lmem := lmem ls;
           lvm := vm';
           lfn := fn;
           lpc := size P + size lcmd;
         |}
       in
       [/\ lsem lp ls ls'
         , vm' =[\ Sv.singleton x ] lvm ls
         & get_var true vm' x = ok (Vword (wrepr reg_size imm))
       ].
Proof.
  set x := {| vname := _; |}.
  rewrite /arm_cmd_load_large_imm /=.

  case: orP => [himm | _].
  - move=> hbody _.
    eexists; split.
    + apply: LSem_step.
      rewrite -(addn0 (size P)) /lsem1 /step (find_instr_skip hbody) /=.
      exact: arm_op_movi_eval_instr.
    + move=> v /Sv.singleton_spec ?. by t_vm_get.
    by t_get_var.

  case hdivmod: Z.div_eucl => [hbs lbs] /=.
  move=> hbody himm.

  eexists; split.
  - apply: lsem_step2; rewrite /lsem1 /step /of_estate.
    + rewrite -(addn0 (size P)).
      rewrite (find_instr_skip hbody) /=.
      rewrite /eval_instr /= /with_vm /= /of_estate /=.
      rewrite /exec_sopn /= truncate_word_u /= addn0.
      reflexivity.

    rewrite -addn1.
    rewrite (find_instr_skip hbody) /=.
    rewrite /eval_instr /=.
    rewrite /sem_sopn /= /get_gvar /=.
    rewrite get_var_eq //=.
    rewrite /with_vm /= /of_estate /=.
    rewrite /exec_sopn /= !truncate_word_u /=.
    rewrite (mov_movt himm hdivmod).
    rewrite addn1 -addn2.
    reflexivity.

  - move=> v /Sv.singleton_spec ?. by t_vm_get.

  by t_get_var.
Qed.

Lemma arm_cmd_large_subi_lsem lp fn s ii P Q xname y imm wy :
  let: x := {| vname := xname; vtype := sword Uptr; |} in
  let: xi := mk_var_i x in
  let: lcmd := map (li_of_fopn_args ii) (arm_cmd_large_subi xi y imm) in
  is_linear_of lp fn (P ++ lcmd ++ Q)
  -> x <> v_var y
  -> get_var true (evm s) (v_var y) = ok (Vword wy)
  -> (0 <= imm < wbase reg_size)%Z
  -> exists vm',
       let: ls := of_estate s fn (size P) in
       let: ls' :=
         {|
           lscs := lscs ls;
           lmem := lmem ls;
           lvm := vm';
           lfn := fn;
           lpc := size P + size lcmd;
         |}
       in
       [/\ lsem lp ls ls'
         , vm' =[\ Sv.singleton x ] evm s
         & get_var true vm' x = ok (Vword (wy - wrepr reg_size imm)%R)
       ].
Proof.
  set x := {| vname := _; |}.
  move=> hbody hxy hgety himm.
  move: hbody.
  rewrite /arm_cmd_large_subi /arm_cmd_large_arith_imm /=.

  case: ZeqbP => [? | _].
  - subst imm.
    move=> hbody.
    eexists; split.
    + apply: LSem_step.
      rewrite -(addn0 (size P)) /lsem1 /step (find_instr_skip hbody) /=.
      apply: arm_op_mov_eval_instr.
      exact: hgety.
    + move=> v /Sv.singleton_spec ?. by t_vm_get.
    rewrite wrepr0 GRing.subr0 /=.
    by t_get_var.

  case hexp: is_expandable.
  - move=> hbody.
    eexists; split.
    + apply: LSem_step.
      rewrite -(addn0 (size P)) /lsem1 /step (find_instr_skip hbody) /=.
      apply: arm_op_subi_eval_instr.
      exact: hgety.
    + move=> v /Sv.singleton_spec ?. by t_vm_get.
    by t_get_var.

  clear hexp.
  rewrite map_cat.
  rewrite -(catA _ _ Q).
  move=> hbody.

  have [vm' [hsem hvm hgetx]] := arm_cmd_load_large_imm_lsem s hbody himm.

  eexists.
  split.
  - apply: (lsem_trans hsem).
    rewrite /of_estate /= -/x.
    apply: LSem_step.
    rewrite /lsem1 /step /=.

    rewrite catA in hbody.
    rewrite -!size_cat.
    rewrite -(addn0 (size _)).
    rewrite (find_instr_skip hbody) /=.

    have {hgety} hgety :
      get_var true vm' y = ok (Vword wy).
    + rewrite (get_var_eq_ex _ _ hvm) /=; first exact: hgety.
      exact: (Sv_neq_not_in_singleton hxy).

    rewrite /eval_instr /=.
    rewrite /sem_sopn /=.
    rewrite /get_gvar /=.
    rewrite hgetx hgety {hgetx hgety} /=.
    rewrite /exec_sopn /= !truncate_word_u /=.
    rewrite /of_estate /with_vm /=.
    rewrite wsub_wnot1.
    rewrite !size_cat addn0 -addn1 addnA /=.
    reflexivity.

  - move=> z hz.
    rewrite Vm.setP_neq.
    + rewrite -(hvm z hz) /=; first done.
    apply/eqP.
    SvD.fsetdec.

  by t_get_var.
Qed.

Lemma store_mn_of_wsizeP ws ws' mn (w : word ws) (w' : word ws') :
  store_mn_of_wsize ws = Some mn
  -> truncate_word ws w' = ok w
  -> exec_sopn (Oarm (ARM_op mn default_opts)) [:: Vword w' ]
     = ok [:: Vword w ].
Proof.
  case: ws w => w // [?]; subst mn.
  all: rewrite /exec_sopn /=.
  all: move=> -> /=.
  all: by rewrite zero_extend_u.
Qed.

End Section.
