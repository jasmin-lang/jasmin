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

(* Most ARM instructions with default options are executed as follows:
   1. Unfold instruction execution definitions, e.g. [eval_instr].
   2. Rewrite argument hypotheses, i.e. [sem_pexpr].
   3. Unfold casting definitions in result, e.g. [zero_extend] and
      [pword_of_word].
   4. Rewrite result hypotheses, i.e. [write_lval]. *)
Ltac t_arm_op :=
  rewrite /eval_instr /= /sem_sopn /= /exec_sopn /get_gvar /=;
  t_simpl_rewrites;
  rewrite /of_estate /= /with_vm /=;
  repeat rewrite truncate_word_u /=;
  rewrite ?zero_extend_u ?addn1;
  t_simpl_rewrites.


Module ARMFopnP.

Section WITH_PARAMS.

Context
  {atoI  : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {call_conv : calling_convention}.

#[local] Existing Instance withsubword.

Let mkv xname vi :=
  let: x := {| vname := xname; vtype := sword arm_reg_size; |} in
  let: xi := {| v_var := x; v_info := vi; |} in
  (xi, x).

Section ARM_OP.

(* Linear state after executing a linear instruction [Lopn]. *)
Notation next_ls ls m vm := (lnext_pc (lset_mem_vm ls m vm)) (only parsing).
Notation next_vm_ls ls vm := (lnext_pc (lset_vm ls vm)) (only parsing).
Notation next_mem_ls ls m := (lnext_pc (lset_mem ls m)) (only parsing).

Lemma add_sem_fopn_args {s xname vi y} {wy : word Uptr} {z} {wz : word Uptr} :
  let: (xi, x) := mkv xname vi in
  get_var true (evm s) (v_var y) = ok (Vword wy)
  -> get_var true (evm s) (v_var z) = ok (Vword wz)
  -> let: wx' := Vword (wy + wz)in
     let: vm' := (evm s).[x <- wx'] in
     sem_fopn_args (ARMFopn.add xi y z) s = ok (with_vm s vm').
Proof. move=> ??. by t_arm_op. Qed.

Lemma addi_sem_fopn_args {s xname vi y imm wy} :
  let: (xi, x) := mkv xname vi in
  get_var true (evm s) (v_var y) = ok (Vword wy)
  -> let: wx' := Vword (wy + wrepr reg_size imm)in
     let: vm' := (evm s).[x <- wx'] in
     sem_fopn_args (ARMFopn.addi xi y imm) s = ok (with_vm s vm').
Proof. move=> ?. by t_arm_op. Qed.

Lemma sub_sem_fopn_args {s xname vi y} {wy : word Uptr} {z} {wz : word Uptr} :
  let: (xi, x) := mkv xname vi in
  get_var true (evm s) (v_var y) = ok (Vword wy)
  -> get_var true (evm s) (v_var z) = ok (Vword wz)
  -> let: wx' := Vword (wy - wz)in
     let: vm' := (evm s).[x <- wx'] in
     sem_fopn_args (ARMFopn.sub xi y z) s = ok (with_vm s vm').
Proof. move=> ??. t_arm_op. by rewrite wsub_wnot1. Qed.

Lemma subi_sem_fopn_args {s xname vi y imm wy} :
  let: (xi, x) := mkv xname vi in
  get_var true (evm s) (v_var y) = ok (Vword wy)
  -> let: wx' := Vword (wy - wrepr reg_size imm)in
     let: vm' := (evm s).[x <- wx'] in
     sem_fopn_args (ARMFopn.subi xi y imm) s = ok (with_vm s vm').
Proof. move=> ?. t_arm_op. by rewrite wsub_wnot1. Qed.

Lemma mov_sem_fopn_args {s xname vi y} {wy : word Uptr} :
  let: (xi, x) := mkv xname vi in
  get_var true (evm s) (v_var y) = ok (Vword wy)
  -> let: vm' := (evm s).[x <- Vword wy] in
     sem_fopn_args (ARMFopn.mov xi y) s = ok (with_vm s vm').
Proof. move=> ?. by t_arm_op. Qed.

Lemma movi_sem_fopn_args {s imm xname vi} :
  let: (xi, x) := mkv xname vi in
  (is_expandable imm \/ is_w16_encoding imm)
  -> let: vm' := (evm s).[x <- Vword (wrepr U32 imm)] in
     sem_fopn_args (ARMFopn.movi xi imm) s = ok (with_vm s vm').
Proof. by t_arm_op. Qed.

Lemma add_eval_instr {lp ls ii xname vi y z} {wy wz : word Uptr} :
  let: (xi, x) := mkv xname vi in
  get_var true (lvm ls) (v_var y) = ok (Vword wy)
  -> get_var true (lvm ls) (v_var z) = ok (Vword wz)
  -> let: li := li_of_fopn_args ii (ARMFopn.add xi y z) in
     let: wx' := Vword (wy + wz)in
     let: vm' := (lvm ls).[x <- wx'] in
     eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=>
    /(add_sem_fopn_args (s := to_estate _))
    /[apply]
    /(_ xname vi)
    /(sem_fopn_args_eval_instr ls).
  by eauto.
Qed.

Lemma addi_eval_instr {lp ls ii xname vi y imm wy} :
  let: (xi, x) := mkv xname vi in
  get_var true (lvm ls) (v_var y) = ok (Vword wy)
  -> let: li := li_of_fopn_args ii (ARMFopn.addi xi y imm) in
     let: wx' := Vword (wy + wrepr reg_size imm)in
     let: vm' := (lvm ls).[x <- wx'] in
     eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=>
    /(addi_sem_fopn_args (s := to_estate _))
    /(sem_fopn_args_eval_instr ls).
  by eauto.
Qed.

Lemma align_eval_instr {lp ls ii xname vi y al} {wy : word Uptr} :
  let: (xi, x) := mkv xname vi in
  get_var true (lvm ls) (v_var y) = ok (Vword wy)
  -> let: li := li_of_fopn_args ii (ARMFopn.align xi y al) in
     let: wx' := Vword (align_word al wy) in
     let: vm' := (lvm ls).[x <- wx'] in
     eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=> hgety.
  Opaque wsize_size.
  t_arm_op.
  Transparent wsize_size.
  by rewrite wrepr_wnot ZlnotE Z.sub_1_r Z.add_1_r Z.succ_pred.
Qed.

Lemma sub_eval_instr {lp ls ii xname vi y z} {wy wz : word Uptr} :
  let: (xi, x) := mkv xname vi in
  get_var true (lvm ls) (v_var y) = ok (Vword wy)
  -> get_var true (lvm ls) (v_var z) = ok (Vword wz)
  -> let: li := li_of_fopn_args ii (ARMFopn.sub xi y z) in
     let: wx' := Vword (wy - wz)in
     let: vm' := (lvm ls).[x <- wx'] in
     eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=>
    /(sub_sem_fopn_args (s := to_estate _))
    /[apply]
    /(_ xname vi)
    /(sem_fopn_args_eval_instr ls).
  by eauto.
Qed.

Lemma subi_eval_instr {lp ls ii xname vi y imm wy} :
  let: (xi, x) := mkv xname vi in
  get_var true (lvm ls) (v_var y) = ok (Vword wy)
  -> let: li := li_of_fopn_args ii (ARMFopn.subi xi y imm) in
     let: wx' := Vword (wy - wrepr reg_size imm)in
     let: vm' := (lvm ls).[x <- wx'] in
     eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=>
    /(subi_sem_fopn_args (s := to_estate _))
    /(sem_fopn_args_eval_instr ls).
  by eauto.
Qed.

Lemma mov_eval_instr {lp ls ii xname vi y} {wy : word Uptr} :
  let: (xi, x) := mkv xname vi in
  get_var true (lvm ls) (v_var y) = ok (Vword wy)
  -> let: li := li_of_fopn_args ii (ARMFopn.mov xi y) in
     let: vm' := (lvm ls).[x <- Vword wy] in
     eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=>
    /(mov_sem_fopn_args (s := to_estate _))
    /(sem_fopn_args_eval_instr ls).
  by eauto.
Qed.

Lemma movi_eval_instr {lp ls ii imm xname vi} :
  let: (xi, x) := mkv xname vi in
  (is_expandable imm \/ is_w16_encoding imm) ->
  let: li := li_of_fopn_args ii (ARMFopn.movi xi imm) in
  let: vm' := (lvm ls).[x <- Vword (wrepr U32 imm)] in
  eval_instr lp li ls = ok (next_vm_ls ls vm').
Proof.
  move=>
    /(movi_sem_fopn_args (s := to_estate ls))
    /(sem_fopn_args_eval_instr ls).
  by eauto.
Qed.

Lemma str_eval_instr {lp ls m' ii xname vi y off wx} {wy : word reg_size} :
  let: (xi, x) := mkv xname vi in
  get_var true (lvm ls) x = ok (Vword wx)
  -> get_var true (lvm ls) (v_var y) = ok (Vword wy)
  -> write (lmem ls) (wx + wrepr Uptr off)%R wy = ok m'
  -> let: li := li_of_fopn_args ii (ARMFopn.str y xi off) in
     eval_instr lp li ls = ok (next_mem_ls ls m').
Proof. move=> ???. by t_arm_op. Qed.

End ARM_OP.

Opaque ARMFopn.add.
Opaque ARMFopn.addi.
Opaque ARMFopn.mov.
Opaque ARMFopn.movi.
Opaque ARMFopn.sub.
Opaque ARMFopn.subi.

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

Lemma li_lsem_1 s xname vi imm :
  let: (xi, x) := mkv xname vi in
  let: lcmd := ARMFopn.li xi imm in
  (0 <= imm < wbase reg_size)%Z
  -> exists vm',
       [/\ sem_fopns_args s lcmd = ok (with_vm s vm')
         , vm' =[\ Sv.singleton x ] evm s
         & get_var true vm' x = ok (Vword (wrepr reg_size imm))
       ].
Proof.
  move=> himm.
  rewrite /ARMFopn.li; case: orP => [himm' | _] /=.
  + rewrite (movi_sem_fopn_args himm') /with_vm /=.
    eexists; split; first reflexivity; last by t_get_var.
    move=> v /Sv.singleton_spec ?.
    by t_vm_get.
  case hdivmod: Z.div_eucl => [hbs lbs] /=.
  rewrite movi_sem_fopn_args /=; first last.
  + have := Z_div_mod imm (wbase U16).
    rewrite hdivmod.
    move=> []; first done.
    rewrite wbaseE /= => _ [??].
    right.
    by apply/ZltP.
  t_arm_op.
  t_get_var => /=; t_arm_op => //.
  eexists; split; first reflexivity.
  + by move=> v /Sv.singleton_spec ?; t_vm_get.
  t_get_var=> //=.
  by rewrite (mov_movt himm hdivmod).
Qed.
Opaque ARMFopn.movt.

Lemma li_lsem lp fn ls ii P Q xname vi imm :
  let: (xi, x) := mkv xname vi in
  let: lcmd := map (li_of_fopn_args ii) (ARMFopn.li xi imm) in
  is_linear_of lp fn (P ++ lcmd ++ Q)
  -> lpc ls = size P
  -> lfn ls = fn
  -> (0 <= imm < wbase reg_size)%Z
  -> exists vm',
       let: ls' := setpc (lset_vm ls vm') (size P + size lcmd) in
       [/\ lsem lp ls ls'
         , vm' =[\ Sv.singleton x ] lvm ls
         & get_var true vm' x = ok (Vword (wrepr reg_size imm))
       ].
Proof.
  move=> hlin hpc hfn himm.
  have [vm' [h1 h2 h3]] := li_lsem_1 (to_estate ls) xname vi himm.
  exists vm'; split => //.
  assert (h := sem_fopns_args_lsem h1 hlin); rewrite size_map.
  by case: (ls) hfn hpc h => //= *; subst.
Qed.
Opaque ARMFopn.li.

Lemma smart_mov_sem_fopns_args s (w : wreg) xname vi y :
  let: (xi, x) := mkv xname vi in
  let: lc := ARMFopn.smart_mov xi y in
  get_var true (evm s) y = ok (Vword w)
  -> exists vm,
       [/\ sem_fopns_args s lc = ok (with_vm s vm)
          , vm =[\ Sv.singleton x ] evm s
          & get_var true vm x = ok (Vword w)
       ].
Proof.
  move=> hgety.
  rewrite /ARMFopn.smart_mov /=.
  case: eqP => [-> | hne] /=.
  - rewrite -hgety -{1}(with_vm_same s). by eexists.
  rewrite (mov_sem_fopn_args hgety) /=.
  eexists; split; first reflexivity; last by rewrite get_var_eq.
  move=> z /Sv.singleton_spec hz.
  by t_vm_get.
Qed.

Lemma smart_mov_lsem lp fn pre pos ls ii xname vi y (w : wreg) :
  let: (xi, x) := mkv xname vi in
  let: lc := map (li_of_fopn_args ii) (ARMFopn.smart_mov xi y) in
  is_linear_of lp fn (pre ++ lc ++ pos)
  -> lpc ls = size pre
  -> lfn ls = fn
  -> get_var true (lvm ls) (v_var y) = ok (Vword w)
  -> exists vm',
       let: ls' := setpc (lset_vm ls vm') (size pre + size lc) in
       [/\ lsem lp ls ls'
         , vm' =[\ Sv.singleton x ] lvm ls
         & get_var true vm' x = ok (Vword w)
       ].
Proof.
  move=> hbody hpc hfn hgety.
  have [vm [hsem hvm hgetx]] :=
    smart_mov_sem_fopns_args (s := to_estate _) xname vi hgety.
  exists vm; split=> //.
  have := [elaborate sem_fopns_args_lsem hsem hbody].
  by rewrite -hfn -hpc of_estate_to_estate size_map.
Qed.

Lemma smart_subi_sem_fopn_args xname vi y imm s (w : wreg) :
  let: (xi, x) := mkv xname vi in
  let: lc := ARMFopn.smart_subi xi y imm in
  ARMFopn.is_arith_small imm \/ x <> v_var y
  -> (0 <= imm < wbase reg_size)%Z
  -> get_var true (evm s) (v_var y) = ok (Vword w)
  -> exists vm',
       [/\ sem_fopns_args s lc = ok (with_vm s vm')
         , vm' =[\ Sv.singleton x ] evm s
         & get_var true vm' x = ok (Vword (w - wrepr reg_size imm)%R)
       ].
Proof.
  rewrite /=; set x := {| vname := _; |}; set xi := {| v_var := _; |}.
  move=> hcond himm hgety.
  rewrite /ARMFopn.smart_subi.
  case: ZeqbP => [? | _].
  - subst imm.
    have [vm [-> hvm hgetx]] := smart_mov_sem_fopns_args xname vi hgety.
    eexists; split; first reflexivity; first done.
    by rewrite hgetx wrepr0 GRing.subr0.

  case: ifP hcond => [_ _ | _ [_|hxy]] //=.
  - rewrite (subi_sem_fopn_args hgety) /=.
    eexists; split; first reflexivity; last by t_get_var.
    move=> ? /Sv.singleton_spec ?.
    by t_vm_get.

  have [vm [hsem hvm hgetx]] := li_lsem_1 s xname vi himm.
  rewrite /sem_fopns_args -cats1 foldM_cat -!/sem_fopns_args hsem /=.
  rewrite -(get_var_eq_ex _ _ hvm) in hgety; last SvD.fsetdec.
  rewrite
    (sub_sem_fopn_args (s := with_vm s vm) (z := xi) hgety hgetx) /with_vm /=.
  eexists; split; first reflexivity; last by t_get_var.
  move=> ? /Sv.singleton_spec ?.
  t_vm_get.
  rewrite hvm; first done.
  by apply/Sv.singleton_spec.
Qed.

Lemma smart_subi_lsem lp fn ls ii P Q xname vi y imm wy :
  let: (xi, x) := mkv xname vi in
  let: lc := map (li_of_fopn_args ii) (ARMFopn.smart_subi xi y imm) in
  is_linear_of lp fn (P ++ lc ++ Q)
  -> lpc ls = size P
  -> lfn ls = fn
  -> ARMFopn.is_arith_small imm \/ x <> v_var y
  -> get_var true (lvm ls) (v_var y) = ok (Vword wy)
  -> (0 <= imm < wbase reg_size)%Z
  -> exists vm',
       let: ls' := setpc (lset_vm ls vm') (size P + size lc) in
       [/\ lsem lp ls ls'
         , vm' =[\ Sv.singleton x ] lvm ls
         & get_var true vm' x = ok (Vword (wy - wrepr reg_size imm)%R)
       ].
Proof.
  rewrite /=; set x := {| vname := _; |}; set xi := {| v_var := _; |}.
  move=> hbody hpc hfn hcond hgety himm.
  have [vm [hsem hvm hgetx]] :=
    smart_subi_sem_fopn_args (s := to_estate _) vi hcond himm hgety.
  exists vm; split=> //.
  have := [elaborate sem_fopns_args_lsem hsem hbody].
  by rewrite -hfn -hpc of_estate_to_estate size_map.
Qed.

Lemma smart_subi_tmp_lsem s (tmp : var_i) xname vi imm w :
  let: (xi, x) := mkv xname vi in
  let: lcmd := ARMFopn.smart_subi_tmp xi tmp imm in
  x <> v_var tmp
  -> vtype tmp = sword U32
  -> get_var true (evm s) x = ok (Vword w)
  -> exists vm',
       [/\ sem_fopns_args s lcmd = ok (with_vm s vm')
         , evm s =[\ Sv.add x (Sv.singleton tmp) ] vm'
         & get_var true vm' x = ok (Vword (w - wrepr reg_size imm)%R)
       ].
Proof.
  rewrite /=; set x := {| vname := _; |}; set xi := {| v_var := _; |}.
  move: tmp => -[[[|||[]] tname] itmp] //.
  set tmp := {| vname := _; |}; set tmpi := {| v_var := _; |}.
  case: s => scs mem vm /= hxy _ hget.
  rewrite /ARMFopn.smart_subi_tmp /with_vm -wrepr_mod /=.
  case: ZeqbP => [heq | _].
  + rewrite /ARMFopn.smart_mov eqxx.
    eexists; split => /=; [ reflexivity | done |].
    by rewrite heq wrepr0 GRing.subr0.
  case: ifP => _ /=.
  + rewrite (subi_sem_fopn_args (s := {| evm := _; |}) (y := xi) hget).
    eexists; split; first reflexivity; last by t_get_var.
    move=> z hz.
    rewrite Vm.setP_neq //.
    apply /eqP.
    SvD.fsetdec.
  rewrite /sem_fopns_args -cats1 foldM_cat -/sem_fopns_args /=.
  set s := {| escs := scs |}.
  have himm : (0 <= (imm mod wbase U32) < wbase U32)%Z by apply Z.mod_pos_bound.
  have [vm1 [-> h2 h3]]:= li_lsem_1 s tname itmp himm.
  rewrite -(get_var_eq_ex _ _ h2) in hget; last by rewrite -/tmp; SvD.fsetdec.
  rewrite /=
    (sub_sem_fopn_args (s := {| evm := vm1; |}) (y := xi) (z := tmpi) hget h3)
    /with_vm /=.
  eexists; split; first reflexivity; last by t_get_var.
  move=> z hz.
  rewrite Vm.setP_neq; last by apply/eqP; SvD.fsetdec.
  rewrite h2 // -/tmp.
  SvD.fsetdec.
Qed.

Lemma smart_addi_tmp_lsem s (tmp : var_i) xname vi imm w :
  let: (xi, x) := mkv xname vi in
  let: lcmd := ARMFopn.smart_addi_tmp xi tmp imm in
  x <> v_var tmp
  -> vtype tmp = sword U32
  -> get_var true (evm s) x = ok (Vword w)
  -> exists vm',
       [/\ sem_fopns_args s lcmd = ok (with_vm s vm')
         , evm s =[\ Sv.add x (Sv.singleton tmp) ] vm'
         & get_var true vm' x = ok (Vword (w + wrepr reg_size imm)%R)
       ].
Proof.
  rewrite /=; set x := {| vname := _; |}; set xi := {| v_var := _; |}.
  move: tmp => -[[[|||[]] tname] itmp] //.
  set tmp := {| vname := _; |}; set tmpi := {| v_var := _; |}.
  case: s => scs mem vm /= hxy _ hget.
  rewrite /ARMFopn.smart_addi_tmp /with_vm -wrepr_mod /=.
  case: ZeqbP => [heq | _].
  + rewrite /ARMFopn.smart_mov eqxx.
    eexists; split => /=; [ reflexivity | done |].
    by rewrite heq wrepr0 GRing.addr0.
  case: ifP => _ /=.
  + rewrite (addi_sem_fopn_args (s := {| evm := _; |}) (y := xi) hget).
    eexists; split; first reflexivity; last by t_get_var.
    move=> z hz.
    rewrite Vm.setP_neq //.
    apply /eqP.
    SvD.fsetdec.
  rewrite /sem_fopns_args -cats1 foldM_cat -/sem_fopns_args /=.
  set s := {| escs := scs |}.
  have himm : (0 <= (imm mod wbase U32) < wbase U32)%Z by apply Z.mod_pos_bound.
  have [vm1 [-> h2 h3]]:= li_lsem_1 s tname itmp himm.
  rewrite -(get_var_eq_ex _ _ h2) in hget; last by rewrite -/tmp; SvD.fsetdec.
  rewrite /=
    (add_sem_fopn_args (s := {| evm := vm1; |}) (y := xi) (z := tmpi) hget h3)
    /with_vm /=.
  eexists; split; first reflexivity; last by t_get_var.
  move=> z hz.
  rewrite Vm.setP_neq; last by apply/eqP; SvD.fsetdec.
  rewrite h2 // -/tmp.
  SvD.fsetdec.
Qed.

End WITH_PARAMS.

End ARMFopnP.

Section WITH_PARAMS.

Context
  {atoI  : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {call_conv : calling_convention}
.

#[local] Existing Instance withsubword.

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

End WITH_PARAMS.
