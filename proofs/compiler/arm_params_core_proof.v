From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
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
  arch_sem.

Require Import
  arm_decl
  arm_instr_decl
  arm_params_core.

Module ARMFopn_coreP.

Section Section.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}.

#[local] Existing Instance withsubword.

Definition sem_fopn_args (p : seq lexpr * arm_op * seq rexpr) (s : estate) :=
  let: (xs,o,es) := p in
  Let args := sem_rexprs s es in
  let op := instr_desc_op o in
  Let _ := assert (id_valid op) ErrType in
  Let t := app_sopn (map eval_ltype (id_tin op)) (id_semi op) args in
  let res := list_ltuple t in
  write_lexprs xs res s.

Definition sem_fopns_args := foldM sem_fopn_args.

Ltac t_arm_op :=
  rewrite /sem_fopn_args /get_gvar /=;
  t_simpl_rewrites;
  rewrite /= /with_vm /=;
  repeat rewrite truncate_word_u /=;
  rewrite ?zero_extend_u ?addn1;
  t_simpl_rewrites.

Lemma add_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} {z} {wz : word Uptr} :
  convertible xi.(vtype) (aword arm_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  get_var true (evm s) (v_var z) >>= to_word Uptr = ok wz ->
  let: wx' := Vword (wy + wz)in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMFopn_core.add xi y z) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_arm_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma addi_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword arm_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (wy + wrepr reg_size imm)in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMFopn_core.addi xi y imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_arm_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma sub_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} {z} {wz : word Uptr} :
  convertible xi.(vtype) (aword arm_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  get_var true (evm s) (v_var z) >>= to_word Uptr = ok wz ->
  let: wx' := Vword (wy - wz)in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMFopn_core.sub xi y z) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_arm_op.
  by rewrite /= !add_wordE wsub_wnot1 set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma subi_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword arm_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (wy - wrepr reg_size imm)in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMFopn_core.subi xi y imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_arm_op.
  by rewrite /= !add_wordE wsub_wnot1 set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma mov_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} :
  convertible xi.(vtype) (aword arm_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: vm' := (evm s).[xi <- Vword wy] in
  sem_fopn_args (ARMFopn_core.mov xi y) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_arm_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma movi_sem_fopn_args {s imm} {xi:var_i} :
  convertible xi.(vtype) (aword arm_reg_size) ->
  (is_expandable imm \/ is_w16_encoding imm) ->
  let: vm' := (evm s).[xi <- Vword (wrepr U32 imm)] in
  sem_fopn_args (ARMFopn_core.movi xi imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  t_arm_op.
  by rewrite set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma mvni_sem_fopn_args {s imm} {xi:var_i} :
  convertible xi.(vtype) (aword arm_reg_size) ->
  is_expandable imm ->
  let: vm' := (evm s).[xi <- Vword (wnot (wrepr U32 imm))] in
  sem_fopn_args (ARMFopn_core.mvni xi imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  t_arm_op.
  by rewrite set_var_truncate // (convertible_eval_atype hc).
Qed.

Opaque ARMFopn_core.add.
Opaque ARMFopn_core.addi.
Opaque ARMFopn_core.mov.
Opaque ARMFopn_core.movi.
Opaque ARMFopn_core.mvni.
Opaque ARMFopn_core.sub.
Opaque ARMFopn_core.subi.

Lemma wbit_n_add ws n lbs hbs (i : nat) :
  let: n2 := (2 ^ n)%Z in
  (n2 * n2 <= wbase ws)%Z ->
  (0 <= lbs < n2)%Z ->
  (0 <= hbs < n2)%Z ->
  let b :=
    if (Z.of_nat i <? n)%Z
    then wbit_n (wrepr ws lbs) i
    else wbit_n (wrepr ws hbs) (i - Z.to_nat n)
  in
  wbit_n (wrepr ws (2 ^ n * hbs + lbs)) i = b.
Proof.
  move=> hn hlbs hhbs.

  have h0i := Zle_0_nat i.

  have h0n : (0 <= n)%Z.
  - case: (Z.le_gt_cases 0 n) => h; first done.
    rewrite (Z.pow_neg_r _ _  h) in hlbs.
    lia.

  have hrange : (0 <= 2 ^ n * hbs + lbs < wbase ws)%Z.
  - nia.

  case: ZltP => hi /=.

  all: rewrite wbit_nE.
  all: rewrite (wunsigned_repr_small hrange).

  - rewrite -(Zplus_minus (Z.of_nat i) n) Z.pow_add_r; last lia; last done.
    rewrite Z.add_comm -Z.mul_assoc Z.mul_comm Z_div_plus; first last.
    + apply/Z.lt_gt. by apply: Z.pow_pos_nonneg.

    rewrite Z.odd_add Z_odd_pow_2; last lia.
    rewrite Bool.xorb_false_r wbit_nE.
    rewrite wunsigned_repr_small; first done.
    lia.

  rewrite -(Zplus_minus n (Z.of_nat i)) (Z.pow_add_r _ _ _ h0n); last lia.
  rewrite -Z.div_div; last lia; last lia.
  rewrite Z.add_comm Z.mul_comm Z_div_plus; last lia.
  rewrite (Zdiv_small _ _ hlbs) /= wbit_nE.
  rewrite wunsigned_repr_small; first last.
  - split; first lia.
    apply: (Z.lt_le_trans _ _ _ _ hn).
    rewrite -Z.pow_twice_r.
    apply: (Z.lt_le_trans _ (2 ^ n)); first lia.
    apply: Z.pow_le_mono_r; lia.

  rewrite Nat2Z.n2zB; first by rewrite Z2Nat.id.
  by apply/ZNleP; rewrite (Z2Nat.id _ h0n); apply/Z.nlt_ge.
Qed.

Lemma mov_movt_aux n x y :
  (0 < n)%Z ->
  (0 <= y < n)%Z ->
  (0 <= n * x + y < n * n)%Z ->
  (0 <= x < n)%Z.
Proof. nia. Qed.

Lemma mov_movt_aux1 n hbs lbs :
  (0 <= n < wbase reg_size)%Z ->
  Z.div_eucl n (wbase U16) = (hbs, lbs) ->
  let: h := wshl (zero_extend U32 (wrepr U16 hbs)) 16 in
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

Lemma mov_movt n hbs lbs :
  Z.div_eucl n (wbase U16) = (hbs, lbs) ->
  let: h := wshl (zero_extend U32 (wrepr U16 hbs)) 16 in
  let: l := wand (wrepr U32 lbs) (zero_extend U32 (wrepr U16 (-1))) in
  wor h l = wrepr U32 n.
Proof.
  move=> hn;
  have := @mov_movt_aux1 (n mod wbase U32)%Z (hbs mod wbase U16)%Z lbs; rewrite !wrepr_mod.
  apply; first by apply/Z_mod_lt/wbase_pos.
  have : (wbase U32 = wbase U16 * wbase U16)%Z by done.
  have := Z_div_mod n (wbase U16) (wbase_pos _); rewrite hn => {hn}.
  have := Z_div_mod (n mod wbase U32) (wbase U16) (wbase_pos _).
  case: Z.div_eucl => q1 r1.
  move: (wbase U16) (wbase U32) (wbase_pos U16) (wbase_pos U32).
  move=> B B2 hB hB2 [h1 h2] [? h3] ?; subst n B2.
  have []:= Zdiv_mod_unique B q1 (hbs mod B) r1 lbs; last by move=> -> ->.
  + lia. + lia.
  rewrite -h1 {1}(Z_div_mod_eq_full hbs B).
  have -> : (B * (B * (hbs / B) + hbs mod B) + lbs)%Z =
            ( (B * (hbs mod B) + lbs) + (hbs / B) * (B * B) )%Z by ring.
  rewrite Z_mod_plus_full Zmod_small //.
  have := Z_mod_lt hbs B hB; nia.
Qed.

Lemma li_lsem_1 s (xi:var_i) imm :
  convertible xi.(vtype) (aword arm_reg_size) ->
  let: lcmd := ARMFopn_core.li xi imm in
  exists vm',
    [/\ sem_fopns_args s lcmd = ok (with_vm s vm')
      , vm' =[\ Sv.singleton xi ] evm s
      & get_var true vm' xi = ok (Vword (wrepr reg_size imm)) ].
Proof.
  move=> hc.
  rewrite /ARMFopn_core.li; case: orP => [himm' | _] /=.

  (* Case: small immediate. *)
  + rewrite (movi_sem_fopn_args hc himm') /with_vm /=.
    eexists; split; first reflexivity; last by t_get_var; rewrite (convertible_eval_atype hc).
    move=> v /Sv.singleton_spec ?.
    by t_vm_get.

  case: ifP => [himm' | _] /=.

  (* Case: negated immediate. *)
  + rewrite (mvni_sem_fopn_args hc himm') /with_vm /=.
    eexists; split; first reflexivity.
    * move=> v /Sv.singleton_spec ?.
      by t_vm_get.
    by rewrite wrepr_mod -wrepr_wnot /= wnot_wnot wrepr_mod get_var_eq (convertible_eval_atype hc).

  (* Case: large immediate. *)
  case hdivmod: Z.div_eucl => [hbs lbs] /=.
  rewrite (movi_sem_fopn_args hc) /=; first last.
  + have := Z_div_mod imm (wbase U16).
    rewrite hdivmod.
    move=> []; first done.
    rewrite wbaseE /= => _ [??].
    right.
    by apply/ZltP.
  t_arm_op.
  t_get_var; rewrite (convertible_eval_atype hc) //=.
  t_arm_op; rewrite set_var_truncate //; last by rewrite (convertible_eval_atype hc).
  eexists; split; first reflexivity.
  + by move=> v /Sv.singleton_spec ?; t_vm_get.
  t_get_var; rewrite (convertible_eval_atype hc) //=.
  by rewrite /arm_MOVT_semi (mov_movt hdivmod).
Qed.
Opaque ARMFopn_core.movt.
Opaque ARMFopn_core.li.

Lemma smart_mov_sem_fopns_args s (w : wreg) (xi:var_i) y :
  convertible xi.(vtype) (aword arm_reg_size) ->
  let: lc := ARMFopn_core.smart_mov xi y in
  get_var true (evm s) y >>= to_word Uptr = ok w ->
  exists vm,
    [/\ sem_fopns_args s lc = ok (with_vm s vm)
      , vm =[\ Sv.singleton xi ] evm s
      & get_var true vm xi >>= to_word Uptr = ok w ].
Proof.
  move=> hc hgety.
  rewrite /ARMFopn_core.smart_mov /=.
  case: eqP => heq /=.
  - case : y heq hgety=> y yi /= *; subst y.
    rewrite -{1}(with_vm_same s); eexists; split; eauto.
  rewrite (mov_sem_fopn_args _ hgety) //=.
  eexists; split; first reflexivity. 
  + by move=> z /Sv.singleton_spec hz; t_vm_get.
  by rewrite get_var_eq /= (convertible_eval_atype hc) //= truncate_word_u.
Qed.

Lemma gen_smart_opi_sem_fopn_args
  (op : word reg_size -> word reg_size -> word reg_size)
  (on_reg : var_i -> var_i -> var_i -> ARMFopn_core.opn_args)
  (on_imm : var_i -> var_i -> Z -> ARMFopn_core.opn_args)
  (is_small : Z -> bool)
  (neutral : option Z)
  (op_sem_fopn_args :
    forall {s} {xi:var_i} {y} {wy : word Uptr} {z} {wz : word Uptr},
      convertible xi.(vtype) (aword arm_reg_size) ->
      get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy
      -> get_var true (evm s) (v_var z) >>= to_word Uptr = ok wz
      -> let: wx' := Vword (op wy wz)in
      let: vm' := (evm s).[xi <- wx'] in
      sem_fopn_args (on_reg xi y z) s = ok (with_vm s vm'))
  (opi_sem_fopn_args :
    forall {s} {xi:var_i} {y imm wy},
      convertible xi.(vtype) (aword arm_reg_size) ->
      get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy
      -> let: wx' := Vword (op wy (wrepr reg_size imm)) in
     let: vm' := (evm s).[xi <- wx'] in
     sem_fopn_args (on_imm xi y imm) s = ok (with_vm s vm'))
  (neutral_ok : if neutral is Some z then forall w, op w (wrepr _ z) = w else true)
  (tmp : var_i) (xi : var_i) y imm s (w : wreg) :
  convertible (vtype tmp) (aword Uptr) ->
  convertible xi.(vtype) (aword arm_reg_size) ->
  let: lc := ARMFopn_core.gen_smart_opi on_reg on_imm is_small neutral tmp xi y imm in
  is_small imm \/ v_var tmp <> v_var y -> 
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok w -> 
  exists vm',
    [/\ sem_fopns_args s lc = ok (with_vm s vm')
      , vm' =[\ Sv.add xi (Sv.singleton tmp) ] evm s
      & get_var true vm' xi = ok (Vword (op w (wrepr reg_size imm))) ].
Proof.
  move=> hc1 hc2 hcond hgety.
  rewrite /ARMFopn_core.gen_smart_opi.
  case (neutral =P Some imm).
  + move=> heq; move: neutral_ok; rewrite heq Z.eqb_refl => ->.
    have [vm [-> hvm hgetx]] := smart_mov_sem_fopns_args hc2 hgety.
    eexists; split; first reflexivity.
    + by apply: eq_exI hvm; clear; SvD.fsetdec.
    by apply get_var_to_word.
  move=> hne; have -> : (if neutral is Some n then (imm =? n)%Z else false) = false.
  + by case: (neutral) hne => // n; case: ZeqbP => [->|].
  case: ifP hcond => [_ _ | _ [_|hxy]] //=.
  - rewrite (opi_sem_fopn_args _ _ _ _ _ hc2 hgety) /=.
    eexists; split; first reflexivity; last by t_get_var; rewrite (convertible_eval_atype hc2).
    by move=> z hin; rewrite Vm.setP_neq //; apply/eqP; clear -hin; SvD.fsetdec.
  have [vm [hsem hvm hgett]] := li_lsem_1 s (xi:=tmp) imm hc1.
  rewrite /sem_fopns_args -cats1 foldM_cat -!/sem_fopns_args hsem /=.
  rewrite -(get_var_eq_ex _ _ hvm) in hgety; last by move=> /=; SvD.fsetdec.
  rewrite
    (op_sem_fopn_args (with_vm s vm) _ _ _ _ (wrepr reg_size imm) hc2 hgety) /with_vm /=;
    last by rewrite hgett /= truncate_word_u.
  eexists; split; first reflexivity; last by t_get_var; rewrite (convertible_eval_atype hc2).
  move=> z hin.
  rewrite Vm.setP_neq; last by apply/eqP; SvD.fsetdec.
  by rewrite hvm //; clear -hin; SvD.fsetdec.
Qed.

End Section.

End ARMFopn_coreP.
