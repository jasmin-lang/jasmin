(* Semantic correctness of the ARMv8-A core operation builders
   ([ARMv8AFopn_core], armv8a_params_core.v), mirroring
   [arm_params_core_proof.v].

   Proven here: the [sem_fopn_args] lemmas for the single-instruction builders
   used by the compiler's stack handling and immediate materialization —
   [add], [addi], [sub], [subi], [mov], [andi] (the AND behind [align]),
   [movz], [movn], [movk] — the [smart_mov] combinator, the immediate
   materialization [li] (at register size, the form the compiler emits
   through [gen_smart_opi]) and the [gen_smart_opi] combinator.

   Unlike ARMv7-M, which materializes a 32-bit immediate with a fixed
   MOV/MOVT pair, the AArch64 [li] emits a variable-length MOVZ/MOVN/MOVK
   sequence over up to four 16-bit chunks of a 64-bit register. Its proof
   goes through an invariant on the chunk chain — after inserting chunk [k],
   the register holds [wrepr U64 (imm mod 2 ^ (16 * (k + 1)))] — so the
   chunks skipped because they are zero preserve the invariant for free.
   The word-level facts about the decomposition ([armv8a_MOVK_semiE] and
   friends) are stated for any operand width, so the assembly-generation
   proof of [Oarmv8a_smart_li] can reuse them at U32. *)

From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype fintype ssralg.
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
  armv8a_decl
  armv8a_instr_decl
  armv8a_params_core.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Module ARMv8AFopn_coreP.

Section Section.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}.

#[local] Existing Instance withsubword.

Definition sem_fopn_args (p : seq lexpr * armv8a_asm_op * seq rexpr) (s : estate) :=
  let: (xs,o,es) := p in
  Let args := sem_rexprs s es in
  let op := instr_desc_op o in
  Let _ := assert (id_valid op) ErrType in
  Let t := app_sopn (map eval_ltype (id_tin op)) (id_semi op) args in
  let res := list_ltuple t in
  write_lexprs xs res s.

Definition sem_fopns_args := foldM sem_fopn_args.

Ltac t_armv8a_op :=
  rewrite /sem_fopn_args /get_gvar /=;
  t_simpl_rewrites;
  rewrite /= /with_vm /=;
  repeat rewrite truncate_word_u /=;
  rewrite ?zero_extend_u ?addn1;
  t_simpl_rewrites.

Lemma add_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} {z} {wz : word Uptr} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  get_var true (evm s) (v_var z) >>= to_word Uptr = ok wz ->
  let: wx' := Vword (wy + wz)in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMv8AFopn_core.add xi y z) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_armv8a_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma addi_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (wy + wrepr reg_size imm)in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMv8AFopn_core.addi xi y imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_armv8a_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma sub_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} {z} {wz : word Uptr} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  get_var true (evm s) (v_var z) >>= to_word Uptr = ok wz ->
  let: wx' := Vword (wy - wz)in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMv8AFopn_core.sub xi y z) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_armv8a_op.
  by rewrite /= /armv8a_SUB_semi sub_wordE set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma subi_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (wy - wrepr reg_size imm)in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMv8AFopn_core.subi xi y imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_armv8a_op.
  by rewrite /= /armv8a_SUB_semi sub_wordE set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma mov_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: vm' := (evm s).[xi <- Vword wy] in
  sem_fopn_args (ARMv8AFopn_core.mov xi y) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_armv8a_op.
  by rewrite /= /armv8a_MOV_semi set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma andi_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (wand wy (wrepr reg_size imm)) in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMv8AFopn_core.andi xi y imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_armv8a_op.
  by rewrite /= /armv8a_bitwise_semi set_var_truncate // (convertible_eval_atype hc).
Qed.

Opaque ARMv8AFopn_core.add.
Opaque ARMv8AFopn_core.addi.
Opaque ARMv8AFopn_core.mov.
Opaque ARMv8AFopn_core.sub.
Opaque ARMv8AFopn_core.subi.
Opaque ARMv8AFopn_core.andi.

(* -------------------------------------------------------------------- *)
(* Word-level facts about the MOVZ/MOVN/MOVK immediate decomposition.
   Stated for any operand width [ws] (with the shift position bounded by
   [wsize_bits ws]) so they serve both the register-size [li] below and
   the U32 form of [Oarmv8a_smart_li] at assembly generation. *)

Lemma wsize_bits_Zof ws :
  wsize_bits ws = Z.of_nat (wsize_size_minus_1 ws).+1.
Proof. by case: ws. Qed.

Lemma wbase_pow_bits ws : wbase ws = (2 ^ wsize_bits ws)%Z.
Proof. by rewrite wbaseE wsize_bits_Zof. Qed.

Lemma wsize_bits_le_256 ws : (wsize_bits ws <= 256)%Z.
Proof. by case: ws. Qed.

(* Splitting an [n]-aligned sum bit by bit: below [n] the bits come from
   [lbs], from [n] up they come from [hbs]. The ARMv7-M analog
   [arm_params_core_proof.wbit_n_add] requires [2 ^ n * 2 ^ n <= wbase ws],
   which fails for the high chunks of a 64-bit word; here the sum is only
   required to fit the word. *)
Lemma wbit_n_add ws (n lbs hbs : Z) (i : nat) :
  (0 <= n)%Z ->
  (0 <= lbs < 2 ^ n)%Z ->
  (0 <= hbs)%Z ->
  (2 ^ n * hbs + lbs < wbase ws)%Z ->
  wbit_n (wrepr ws (2 ^ n * hbs + lbs)) i
  = if (Z.of_nat i <? n)%Z
    then wbit_n (wrepr ws lbs) i
    else wbit_n (wrepr ws hbs) (i - Z.to_nat n).
Proof.
  move=> h0n hlbs hhbs hsum.
  have h0i := Zle_0_nat i.
  have h2n : (0 < 2 ^ n)%Z by apply: Z.pow_pos_nonneg.
  have hmul : (0 <= 2 ^ n * hbs)%Z by nia.
  have hrange : (0 <= 2 ^ n * hbs + lbs < wbase ws)%Z by lia.

  case: ZltP => hi /=.

  all: rewrite wbit_nE.
  all: rewrite (wunsigned_repr_small hrange).

  - rewrite -(Zplus_minus (Z.of_nat i) n) Z.pow_add_r; last lia; last done.
    rewrite Z.add_comm -Z.mul_assoc Z.mul_comm Z_div_plus; first last.
    + by apply/Z.lt_gt/Z.pow_pos_nonneg; lia.
    rewrite Z.odd_add Z_odd_pow_2; last lia.
    rewrite Bool.xorb_false_r wbit_nE.
    rewrite wunsigned_repr_small; first done.
    lia.

  rewrite -(Zplus_minus n (Z.of_nat i)) (Z.pow_add_r _ _ _ h0n); last lia.
  rewrite -Z.div_div; last lia; last lia.
  rewrite Z.add_comm Z.mul_comm Z_div_plus; last lia.
  rewrite (Zdiv_small _ _ hlbs) /= wbit_nE.
  rewrite wunsigned_repr_small; first last.
  - nia.
  rewrite Nat2Z.n2zB; first by rewrite Z2Nat.id.
  by apply/ZNleP; rewrite (Z2Nat.id _ h0n); apply/Z.nlt_ge.
Qed.

(* OR-ing an [n]-aligned value with a value below [2 ^ n] is addition. *)
Lemma wor_wrepr_add ws (n lbs hbs : Z) :
  (0 <= n)%Z ->
  (0 <= lbs < 2 ^ n)%Z ->
  (0 <= hbs)%Z ->
  (2 ^ n * hbs + lbs < wbase ws)%Z ->
  wor (wrepr ws (2 ^ n * hbs)) (wrepr ws lbs) = wrepr ws (2 ^ n * hbs + lbs).
Proof.
  move=> h0n hlbs hhbs hsum.
  have h2n : (0 < 2 ^ n)%Z by apply: Z.pow_pos_nonneg.
  have hmul : (0 <= 2 ^ n * hbs)%Z by nia.
  apply/eqP/eq_from_wbit_n => i.
  rewrite worE (wbit_n_add _ h0n hlbs hhbs hsum).
  have hi_bits : (Z.of_nat i < Z.of_nat (wsize_size_minus_1 ws).+1)%Z.
  - by apply/Nat2Z.inj_lt/ltP/ltn_ord.
  case: ZltP => hi.
  - rewrite (wbit_lower_bits_0 (x := hbs) (n := n)); first done.
    + lia.
    lia.
  rewrite (wbit_higher_bits_0 (x := lbs) (n := n)) //; last lia.
  rewrite orbF wbit_pow_2 //.
  apply/andP; split.
  - by apply/leP; lia.
  by rewrite -ltnS ltn_ord.
Qed.

(* The MOVK mask keeps a value whose bits from [sh] up are zero: the mask
   clears exactly bits [sh, sh + 16). *)
Lemma wand_movk_mask_id ws (m sh : Z) :
  (0 <= sh)%Z ->
  (sh + 16 <= wsize_bits ws)%Z ->
  (0 <= m < 2 ^ sh)%Z ->
  wand (wrepr ws m) (wnot (wshl (zero_extend ws (wrepr U16 (-1))) sh))
  = wrepr ws m.
Proof.
  move=> h0sh hsh hm.
  have -> : zero_extend ws (wrepr U16 (-1)) = wrepr ws (2 ^ 16 - 1).
  - by apply/wunsigned_inj; rewrite /zero_extend !wunsigned_repr.
  rewrite wshl_sem // -wrepr_mul.
  have hmask : (0 <= 2 ^ sh * (2 ^ 16 - 1) < wbase ws)%Z.
  - split; first nia.
    rewrite wbase_pow_bits.
    apply: (Z.lt_le_trans _ (2 ^ (sh + 16))); last by apply: Z.pow_le_mono_r; lia.
    rewrite Z.pow_add_r //; nia.
  apply/eqP/eq_from_wbit_n => i.
  rewrite wandE wnotE.
  have hi_bits : (Z.of_nat i < Z.of_nat (wsize_size_minus_1 ws).+1)%Z.
  - by apply/Nat2Z.inj_lt/ltP/ltn_ord.
  case: (ZltP (Z.of_nat i) sh) => hi.
  - rewrite (wbit_lower_bits_0 (x := 2 ^ 16 - 1) (n := sh)); first last.
    + done.
    + lia.
    by rewrite andbT.
  rewrite (wbit_higher_bits_0 (x := m) (n := sh)) //.
  lia.
Qed.

Lemma armv8a_MOVZ_semiE ws (c : Z) :
  (16 <= wsize_bits ws)%Z ->
  (0 <= c < 2 ^ 16)%Z ->
  armv8a_MOVZ_semi (ws := ws) (wrepr U16 c) (wrepr U8 0) = wrepr ws c.
Proof.
  move=> hws hc.
  rewrite /armv8a_MOVZ_semi.
  have -> : wunsigned (wrepr U8 0) = 0%Z by rewrite wunsigned_repr.
  rewrite wshl0.
  have hc' : (0 <= c < wbase U16)%Z by rewrite wbase_pow_bits; exact: hc.
  by rewrite /zero_extend (wunsigned_repr_small hc').
Qed.

Lemma armv8a_MOVN_semiE ws (c : Z) :
  (16 <= wsize_bits ws)%Z ->
  (0 <= c < 2 ^ 16)%Z ->
  armv8a_MOVN_semi (ws := ws) (wrepr U16 c) (wrepr U8 0)
  = wnot (wrepr ws c).
Proof.
  move=> hws hc.
  rewrite /armv8a_MOVN_semi.
  have -> : wunsigned (wrepr U8 0) = 0%Z by rewrite wunsigned_repr.
  rewrite wshl0.
  have hc' : (0 <= c < wbase U16)%Z by rewrite wbase_pow_bits; exact: hc.
  by rewrite /zero_extend (wunsigned_repr_small hc').
Qed.

(* Inserting the 16-bit chunk [c] at position [sh] of a register holding a
   value below [2 ^ sh] recombines them by addition. *)
Lemma armv8a_MOVK_semiE ws (m c sh : Z) :
  (0 <= sh)%Z ->
  (sh + 16 <= wsize_bits ws)%Z ->
  (0 <= m < 2 ^ sh)%Z ->
  (0 <= c < 2 ^ 16)%Z ->
  armv8a_MOVK_semi (wrepr ws m) (wrepr U16 c) (wrepr U8 sh)
  = wrepr ws (2 ^ sh * c + m).
Proof.
  move=> h0sh hsh hm hc.
  have hbits := @wsize_bits_le_256 ws.
  rewrite /armv8a_MOVK_semi.
  have -> : wunsigned (wrepr U8 sh) = sh.
  - apply: wunsigned_repr_small.
    rewrite wbase_pow_bits /=.
    lia.
  rewrite (wand_movk_mask_id h0sh hsh hm).
  have hc' : (0 <= c < wbase U16)%Z by rewrite wbase_pow_bits; exact: hc.
  have -> : zero_extend ws (wrepr U16 c) = wrepr ws c.
  - by rewrite /zero_extend (wunsigned_repr_small hc').
  rewrite wshl_sem // -wrepr_mul.
  have hsum : (2 ^ sh * c + m < wbase ws)%Z.
  - rewrite wbase_pow_bits.
    apply: (Z.lt_le_trans _ (2 ^ (sh + 16))); last by apply: Z.pow_le_mono_r; lia.
    rewrite Z.pow_add_r //; nia.
  by apply: wor_wrepr_add => //; lia.
Qed.

(* [a mod (b * c)] recombines from the chunks [a mod b] and [(a / b) mod c]. *)
Lemma z_mod_recombine (a b c : Z) :
  (0 < b)%Z ->
  (0 < c)%Z ->
  (a mod (b * c))%Z = (b * ((a / b) mod c) + a mod b)%Z.
Proof.
  move=> hb hc.
  have hmodb := Z_mod_lt a b (Z.lt_gt _ _ hb).
  have hmodc := Z_mod_lt (a / b) c (Z.lt_gt _ _ hc).
  rewrite {1}(Z_div_mod_eq_full a b) {1}(Z_div_mod_eq_full (a / b) c).
  set q := ((a / b) / c)%Z.
  have -> : (b * (c * q + (a / b) mod c) + a mod b
             = (b * ((a / b) mod c) + a mod b) + q * (b * c))%Z.
  - ring.
  rewrite Z_mod_plus_full Zmod_small //.
  nia.
Qed.

(* -------------------------------------------------------------------- *)
(* Semantics of the MOVZ/MOVN/MOVK builders at register size. *)

Lemma movz_sem_fopn_args {s} {xi : var_i} {imm sh : Z} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  let: w := armv8a_MOVZ_semi (ws := U64) (wrepr U16 imm) (wrepr U8 sh) in
  let: vm' := (evm s).[xi <- Vword w] in
  sem_fopn_args (ARMv8AFopn_core.movz U64 xi imm sh) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_armv8a_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma movn_sem_fopn_args {s} {xi : var_i} {imm sh : Z} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  let: w := armv8a_MOVN_semi (ws := U64) (wrepr U16 imm) (wrepr U8 sh) in
  let: vm' := (evm s).[xi <- Vword w] in
  sem_fopn_args (ARMv8AFopn_core.movn U64 xi imm sh) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_armv8a_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma movk_sem_fopn_args {s} {xi : var_i} {imm sh : Z} {wx : word Uptr} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var xi) >>= to_word Uptr = ok wx ->
  let: w := armv8a_MOVK_semi wx (wrepr U16 imm) (wrepr U8 sh) in
  let: vm' := (evm s).[xi <- Vword w] in
  sem_fopn_args (ARMv8AFopn_core.movk U64 xi imm sh) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_armv8a_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

Opaque ARMv8AFopn_core.movz.
Opaque ARMv8AFopn_core.movn.
Opaque ARMv8AFopn_core.movk.

(* -------------------------------------------------------------------- *)
(* Immediate materialization. *)

Lemma li_lsem_1 s (xi : var_i) imm :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  let: lcmd := ARMv8AFopn_core.li U64 xi imm in
  exists vm',
    [/\ sem_fopns_args s lcmd = ok (with_vm s vm')
      , vm' =[\ Sv.singleton xi ] evm s
      & get_var true vm' xi = ok (Vword (wrepr reg_size imm)) ].
Proof.
  move=> hc.
  rewrite /ARMv8AFopn_core.li.
  set n := (imm mod wbase U64)%Z.
  have hn : (0 <= n < wbase U64)%Z by apply/Z_mod_lt/wbase_pos.
  have hwr : wrepr U64 n = wrepr U64 imm by rewrite /n wrepr_mod.

  case: ZltP => [hsmall | /Z.nlt_ge hbig] /=.

  (* Case: 16-bit immediate, single MOVZ. *)
  - rewrite (movz_sem_fopn_args hc) /=.
    rewrite armv8a_MOVZ_semiE //; last lia.
    eexists; split; first reflexivity.
    + by move=> v /Sv.singleton_spec ?; t_vm_get.
    by t_get_var; rewrite (convertible_eval_atype hc) hwr.

  case: ZleP => [hones | /Z.nle_gt hmid] /=.

  (* Case: upper chunks all ones, single MOVN. *)
  - have hl := Z.add_lnot_diag n.
    have hlnotmod : (Z.lnot n mod wbase U64 = wbase U64 - 1 - n)%Z.
    + have -> : Z.lnot n = ((wbase U64 - 1 - n) + (-1) * wbase U64)%Z by lia.
      rewrite Z_mod_plus_full.
      apply: Zmod_small; lia.
    have hlnot : Z_mod_lnot n U64 = (wbase U64 - 1 - n)%Z.
    + by rewrite /Z_mod_lnot (Zmod_small _ _ hn) hlnotmod.
    rewrite (movn_sem_fopn_args hc) /=.
    rewrite armv8a_MOVN_semiE //; last first.
    + rewrite hlnot.
      have hwb : wbase U64 = 18446744073709551616%Z by vm_compute.
      lia.
    eexists; split; first reflexivity.
    + by move=> v /Sv.singleton_spec ?; t_vm_get.
    by t_get_var;
      rewrite (convertible_eval_atype hc) hlnot -hlnotmod wrepr_mod
        wrepr_wnot Z.lnot_involutive hwr.

  (* Case: general MOVZ/MOVK chain. Invariant: after treating the chunk at
     position [sh], the register holds [wrepr U64 (n mod 2 ^ (sh + 16))]. *)
  have hstep :
    forall (s' : estate) (sh : Z),
      (16 <= sh)%Z ->
      (sh + 16 <= 64)%Z ->
      get_var true (evm s') (v_var xi)
        = ok (Vword (wrepr U64 (n mod 2 ^ sh))) ->
      exists vm',
        [/\ sem_fopns_args s'
              (if ((n / 2 ^ sh) mod 2 ^ 16 =? 0)%Z
               then [::]
               else [:: ARMv8AFopn_core.movk U64 xi ((n / 2 ^ sh) mod 2 ^ 16) sh ])
            = ok (with_vm s' vm')
          , vm' =[\ Sv.singleton xi ] evm s'
          & get_var true vm' xi
            = ok (Vword (wrepr U64 (n mod 2 ^ (sh + 16)))) ].
  - move=> s' sh hsh16 hsh64 hget.
    have h2sh : (0 < 2 ^ sh)%Z by apply: Z.pow_pos_nonneg; lia.
    have hchunk : (n mod 2 ^ (sh + 16) = 2 ^ sh * ((n / 2 ^ sh) mod 2 ^ 16) + n mod 2 ^ sh)%Z.
    + by rewrite Z.pow_add_r; [ apply: z_mod_recombine | lia | lia ].
    case: Z.eqb_spec => [hz | hnz].
    + exists (evm s'); split.
      * by rewrite /sem_fopns_args /= with_vm_same.
      * done.
      by rewrite hget hchunk hz Z.mul_0_r Z.add_0_l.
    rewrite /sem_fopns_args /=.
    rewrite (movk_sem_fopn_args (wx := wrepr U64 (n mod 2 ^ sh)) hc); first last.
    + by rewrite hget /= truncate_word_u.
    rewrite /= armv8a_MOVK_semiE //; first last.
    + by have := Z_mod_lt (n / 2 ^ sh) (2 ^ 16); lia.
    + by apply: Z_mod_lt; lia.
    + lia.
    eexists; split; first reflexivity.
    + by move=> v /Sv.singleton_spec ?; t_vm_get.
    by t_get_var; rewrite (convertible_eval_atype hc) /= ?hchunk.

  have hc0 : (0 <= n mod 2 ^ 16 < 2 ^ 16)%Z by apply: Z_mod_lt.

  (* MOVZ of the low chunk. *)
  rewrite !orbF (movz_sem_fopn_args hc) /=.
  rewrite armv8a_MOVZ_semiE //.
  set s1 := with_vm s _.
  have hget1 : get_var true (evm s1) (v_var xi)
    = ok (Vword (wrepr U64 (n mod 2 ^ 16))).
  - by t_get_var; rewrite (convertible_eval_atype hc).

  (* Chunk at position 16. *)
  rewrite /sem_fopns_args foldM_cat -!/sem_fopns_args.
  have [vm2 [-> hvm2 hget2]] := hstep s1 16%Z ltac:(lia) ltac:(lia) hget1.
  rewrite /=.
  set s2 := with_vm s1 vm2.

  (* Chunk at position 32. *)
  rewrite /sem_fopns_args foldM_cat -!/sem_fopns_args.
  have [vm3 [-> hvm3 hget3]] := hstep s2 32%Z ltac:(lia) ltac:(lia) hget2.
  rewrite /=.
  set s3 := with_vm s2 vm3.

  (* Chunk at position 48. *)
  have [vm4 [-> hvm4 hget4]] := hstep s3 48%Z ltac:(lia) ltac:(lia) hget3.

  exists vm4; split.
  - done.
  - move=> v hv.
    rewrite (hvm4 _ hv) /s3 /= (hvm3 _ hv) /s2 /= (hvm2 _ hv) /s1 /=.
    have hne : v <> v_var xi.
    + by move=> heq; apply: hv; apply/Sv.singleton_spec.
    by t_vm_get.
  rewrite hget4.
  have h64 : (2 ^ (48 + 16) = wbase U64)%Z by vm_compute.
  by rewrite h64 (Zmod_small _ _ hn) hwr.
Qed.
Opaque ARMv8AFopn_core.li.

(* -------------------------------------------------------------------- *)
(* Immediate materialization at W (32-bit) width, used by the
   [Oarmv8a_smart_li U32] extra op. The destination variable still has
   register type (a W write clears the upper bits at the assembly level);
   at this level the varmap simply holds the 32-bit value, which the
   [withsubword] discipline allows. *)

Transparent ARMv8AFopn_core.movz.
Transparent ARMv8AFopn_core.movn.
Transparent ARMv8AFopn_core.movk.
Transparent ARMv8AFopn_core.li.

Lemma movz_sem_fopn_args_w32 {s} {xi : var_i} {imm sh : Z} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  let: w := armv8a_MOVZ_semi (ws := U32) (wrepr U16 imm) (wrepr U8 sh) in
  let: vm' := (evm s).[xi <- Vword w] in
  sem_fopn_args (ARMv8AFopn_core.movz U32 xi imm sh) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_armv8a_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma movn_sem_fopn_args_w32 {s} {xi : var_i} {imm sh : Z} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  let: w := armv8a_MOVN_semi (ws := U32) (wrepr U16 imm) (wrepr U8 sh) in
  let: vm' := (evm s).[xi <- Vword w] in
  sem_fopn_args (ARMv8AFopn_core.movn U32 xi imm sh) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_armv8a_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma movk_sem_fopn_args_w32 {s} {xi : var_i} {imm sh : Z} {wx : word U32} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var xi) >>= to_word U32 = ok wx ->
  let: w := armv8a_MOVK_semi wx (wrepr U16 imm) (wrepr U8 sh) in
  let: vm' := (evm s).[xi <- Vword w] in
  sem_fopn_args (ARMv8AFopn_core.movk U32 xi imm sh) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_armv8a_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

Opaque ARMv8AFopn_core.movz.
Opaque ARMv8AFopn_core.movn.
Opaque ARMv8AFopn_core.movk.

Lemma li_lsem_1_w32 s (xi : var_i) imm :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  let: lcmd := ARMv8AFopn_core.li U32 xi imm in
  exists vm',
    [/\ sem_fopns_args s lcmd = ok (with_vm s vm')
      , vm' =[\ Sv.singleton xi ] evm s
      & get_var true vm' xi = ok (Vword (wrepr U32 imm)) ].
Proof.
  move=> hc.
  rewrite /ARMv8AFopn_core.li.
  set n := (imm mod wbase U32)%Z.
  have hwb : wbase U32 = 4294967296%Z by vm_compute.
  have hn : (0 <= n < wbase U32)%Z by apply/Z_mod_lt/wbase_pos.
  have hwr : wrepr U32 n = wrepr U32 imm by rewrite /n wrepr_mod.

  case: ZltP => [hsmall | /Z.nlt_ge hbig] /=.

  (* Case: 16-bit immediate, single MOVZ. *)
  - rewrite (movz_sem_fopn_args_w32 hc) /=.
    rewrite armv8a_MOVZ_semiE //; last lia.
    eexists; split; first reflexivity.
    + by move=> v /Sv.singleton_spec ?; t_vm_get.
    by t_get_var; rewrite (convertible_eval_atype hc) hwr.

  case: ZleP => [hones | /Z.nle_gt hmid] /=.

  (* Case: upper chunk all ones, single MOVN. *)
  - have hl := Z.add_lnot_diag n.
    have hlnotmod : (Z.lnot n mod wbase U32 = wbase U32 - 1 - n)%Z.
    + have -> : Z.lnot n = ((wbase U32 - 1 - n) + (-1) * wbase U32)%Z by lia.
      rewrite Z_mod_plus_full.
      apply: Zmod_small; lia.
    have hlnot : Z_mod_lnot n U32 = (wbase U32 - 1 - n)%Z.
    + by rewrite /Z_mod_lnot (Zmod_small _ _ hn) hlnotmod.
    rewrite (movn_sem_fopn_args_w32 hc) /=.
    rewrite armv8a_MOVN_semiE //; last first.
    + rewrite hlnot; lia.
    eexists; split; first reflexivity.
    + by move=> v /Sv.singleton_spec ?; t_vm_get.
    by t_get_var;
      rewrite (convertible_eval_atype hc) hlnot -hlnotmod wrepr_mod
        wrepr_wnot Z.lnot_involutive hwr.

  (* Case: MOVZ of the low chunk plus at most one MOVK. *)
  have hc0 : (0 <= n mod 2 ^ 16 < 2 ^ 16)%Z by apply: Z_mod_lt.
  rewrite !orbT /= cats0.
  rewrite (movz_sem_fopn_args_w32 hc) /=.
  rewrite armv8a_MOVZ_semiE //.
  set s1 := with_vm s _.
  have hget1 : get_var true (evm s1) (v_var xi)
    = ok (Vword (wrepr U32 (n mod 2 ^ 16))).
  - by t_get_var; rewrite (convertible_eval_atype hc).
  have hchunk : (n mod 2 ^ (16 + 16)
                 = 2 ^ 16 * ((n / 2 ^ 16) mod 2 ^ 16) + n mod 2 ^ 16)%Z.
  - by rewrite Z.pow_add_r; [ apply: z_mod_recombine | lia | lia ].
  have hmod32 : (n mod 2 ^ (16 + 16))%Z = n.
  - have -> : (2 ^ (16 + 16) = wbase U32)%Z by vm_compute.
    by rewrite Zmod_small.

  case: Z.eqb_spec => [hz | hnz] /=.

  (* Zero high chunk: the MOVZ already materialized the immediate. *)
  - eexists; split; first reflexivity.
    + by move=> v /Sv.singleton_spec ?; t_vm_get.
    rewrite hget1 -hwr.
    by rewrite -[in RHS]hmod32 hchunk hz Z.mul_0_r Z.add_0_l.

  (* Nonzero high chunk: insert it with MOVK. *)
  rewrite (movk_sem_fopn_args_w32 (wx := wrepr U32 (n mod 2 ^ 16)) hc); first last.
  - by rewrite hget1 /= truncate_word_u.
  have h1 : (0 <= 16)%Z by [].
  have h2 : (16 + 16 <= wsize_bits U32)%Z by [].
  have h3 : (0 <= (n / 2 ^ 16) mod 2 ^ 16 < 2 ^ 16)%Z by apply: Z_mod_lt.
  rewrite /= (armv8a_MOVK_semiE h1 h2 hc0 h3).
  eexists; split; first reflexivity.
  - by move=> v /Sv.singleton_spec ?; t_vm_get.
  t_get_var; rewrite (convertible_eval_atype hc) /=.
  all: by rewrite -?hchunk ?hmod32 ?hwr.
Qed.
Opaque ARMv8AFopn_core.li.

Lemma smart_mov_sem_fopns_args s (w : word armv8a_reg_size) (xi:var_i) y :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  let: lc := ARMv8AFopn_core.smart_mov xi y in
  get_var true (evm s) y >>= to_word Uptr = ok w ->
  exists vm,
    [/\ sem_fopns_args s lc = ok (with_vm s vm)
      , vm =[\ Sv.singleton xi ] evm s
      & get_var true vm xi >>= to_word Uptr = ok w ].
Proof.
  move=> hc hgety.
  rewrite /ARMv8AFopn_core.smart_mov /=.
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
  (on_reg : var_i -> var_i -> var_i -> ARMv8AFopn_core.opn_args)
  (on_imm : var_i -> var_i -> Z -> ARMv8AFopn_core.opn_args)
  (is_small : Z -> bool)
  (neutral : option Z)
  (op_sem_fopn_args :
    forall {s} {xi:var_i} {y} {wy : word Uptr} {z} {wz : word Uptr},
      convertible xi.(vtype) (aword armv8a_reg_size) ->
      get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy
      -> get_var true (evm s) (v_var z) >>= to_word Uptr = ok wz
      -> let: wx' := Vword (op wy wz)in
      let: vm' := (evm s).[xi <- wx'] in
      sem_fopn_args (on_reg xi y z) s = ok (with_vm s vm'))
  (opi_sem_fopn_args :
    forall {s} {xi:var_i} {y imm wy},
      convertible xi.(vtype) (aword armv8a_reg_size) ->
      get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy
      -> let: wx' := Vword (op wy (wrepr reg_size imm)) in
     let: vm' := (evm s).[xi <- wx'] in
     sem_fopn_args (on_imm xi y imm) s = ok (with_vm s vm'))
  (neutral_ok : if neutral is Some z then forall w, op w (wrepr _ z) = w else true)
  (tmp : var_i) (xi : var_i) y imm s (w : word armv8a_reg_size) :
  convertible (vtype tmp) (aword Uptr) ->
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  let: lc := ARMv8AFopn_core.gen_smart_opi on_reg on_imm is_small neutral tmp xi y imm in
  is_small imm \/ v_var tmp <> v_var y ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok w ->
  exists vm',
    [/\ sem_fopns_args s lc = ok (with_vm s vm')
      , vm' =[\ Sv.add xi (Sv.singleton tmp) ] evm s
      & get_var true vm' xi = ok (Vword (op w (wrepr reg_size imm))) ].
Proof.
  move=> hc1 hc2 hcond hgety.
  rewrite /ARMv8AFopn_core.gen_smart_opi.
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

End ARMv8AFopn_coreP.
