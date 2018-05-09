Require Import asmgen.
Import Utf8.
Import all_ssreflect all_algebra.
Import compiler_util psem x86_sem x86_variables x86_variables_proofs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ----------------------------------------------------------------------------- *)
Lemma decode_addr_unset_rflags m f addr:
  decode_addr (mem_unset_rflags f m) addr = decode_addr m addr.
Proof. done. Qed.

Lemma decode_addr_set_rflags m f b addr:
  decode_addr (mem_set_rflags f b m) addr = decode_addr m addr.
Proof. done. Qed.

Lemma decode_addr_update_rflags m f addr:
  decode_addr (mem_update_rflags f m) addr = decode_addr m addr.
Proof. done. Qed.

Instance rflagv_leb_refl : Reflexive rflagv_leb.
Proof. case => // b /=; exact: eqxx. Qed.

Instance rflagv_leb_trans : Transitive rflagv_leb.
Proof. case => // b y z /eqP -> /eqP ->; reflexivity. Qed.

Lemma value_of_boolI x y :
  value_of_bool x = ok (Vbool y) →
  x = ok y.
Proof. by case: x => // [ b | [] // ] [<-]. Qed.

(* -------------------------------------------------------------------- *)
(* Definitions of descriptors                                           *)

Definition implicit_flags :=
  map (ADImplicit \o var_of_flag) [::OF; CF; SF; PF; ZF].

Definition implicit_flags_noCF :=
  map (ADImplicit \o var_of_flag) [::OF; SF; PF; ZF].

Local Coercion Eb n := ADExplicit None n None.
Local Definition E w n := ADExplicit (Some w) n None.
Local Coercion F f := ADImplicit (var_of_flag f).
Local Coercion R f := ADImplicit (var_of_register f).

Notation make_instr_desc gen_sem := (mk_instr_desc gen_sem erefl erefl).

Instance x86_mem_equiv_refl : Reflexive x86_mem_equiv.
Proof. by case => xm xr xx xf; constructor => //= f; case: (xf f) => /=. Qed.

Arguments x86_mem_equiv_refl [_].

Corollary x86_mem_eq_equiv m m' :
  m = m' → x86_mem_equiv m m'.
Proof. move => ->; reflexivity. Qed.

Definition arg_of_oprd_sz sz o :=
  match o with
  | Imm_op x => Aimm x
  | Glo_op x => Aglob x
  | Reg_op x => Areg x
  | Adr_op x => Aaddr sz x
  end.

Lemma arg_of_oprdE sz o :
  arg_of_oprd (Some sz) o = Some (arg_of_oprd_sz sz o).
Proof. by case: o. Qed.

Lemma eval_low_read gd m sz sz' (w: word sz') x :
  (sz ≤ sz')%CMP →
  eval_low gd m (arg_of_oprd_sz sz x) = ok (Vword w) →
  read_oprd gd sz x m = ok (zero_extend sz w) (* ∧ (sz ≤ U64)%CMP *).
Proof.
move => hle; case: x => /=.
- by move => n /ok_word_inj [??]; subst.
- by rewrite /get_global => g; case: get_global_word => // ? /ok_word_inj [??]; subst.
- by move => r /ok_word_inj [??]; subst.
by move => a; apply: rbindP => ? -> /ok_word_inj [??]; subst; rewrite /= zero_extend_u.
Qed.

(* ----------------------------------------------------------------------------- *)
Lemma MOV_gsc sz :
  gen_sem_correct [:: TYoprd; TYoprd] (Ox86_MOV sz) [:: E sz 0] [:: E sz 1] [::] (MOV sz).
Proof.
move => /= x y; split => // gd m m'.
rewrite /low_sem_aux /= arg_of_oprdE /= /sets_low /eval_MOV /eval_MOV_nocheck /x86_MOV.
case: x => // [ x | x ]; t_xrbindP => ??? h <-; t_xrbindP => w' /of_val_word [sz'] [w] [hle ??] ?; subst => -> <- /=; rewrite ?truncate_word_u /=; [ case | ]; rewrite (eval_low_read _ h) //= => ->; eexists; split; reflexivity.
Qed.

Definition MOV_desc sz := make_instr_desc (MOV_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma VMOVDQU_gsc :
  gen_sem_correct [:: TYrm128; TYrm128] Ox86_VMOVDQU [:: E U128 0] [:: E U128 1] [::] VMOVDQU.
Proof.
move => /= x y; split => // gd m m'.
case: y => [ y | y ]; rewrite /low_sem_aux /sets_low /eval_VMOV /=.
+ case: x => //= x; rewrite !zero_extend_u => ->; eexists; split; reflexivity.
t_xrbindP => ???? -> <- <- /= [<-].
case: x => //= x; rewrite !zero_extend_u => ->; eexists; split; reflexivity.
Qed.

Definition VMOVDQU_desc := make_instr_desc VMOVDQU_gsc.

(* ----------------------------------------------------------------------------- *)
Ltac know_it :=
  refine (ex_intro _ _ (conj _ x86_mem_equiv_refl));
  repeat match goal with
  | H : _ = ?a |- _ = ?a => rewrite - H => { H }
  end.

Ltac update_set' :=
  by rewrite /sets_low /= /mem_update_rflags /mem_unset_rflags /mem_set_rflags
             /mem_write_reg /=;
     repeat f_equal; apply /ffunP; case; rewrite !ffunE.

Ltac update_set := know_it; update_set'.

(* ----------------------------------------------------------------------------- *)
Lemma RegMap_set_id rm x : rm = RegMap.set rm x (rm x).
Proof. by apply /ffunP;case;rewrite !ffunE;(case:eqP => [<- | ?]). Qed.

Lemma CMOVcc_gsc sz :
  gen_sem_correct [:: TYcondt; TYoprd; TYoprd]
     (Ox86_CMOVcc sz) [:: E sz 1] [:: Eb 0; E sz 2; E sz 1] [::] (CMOVcc sz).
Proof.
move => ct x y; split => // gd m m'.
rewrite /low_sem_aux /= !arg_of_oprdE /eval_CMOVcc /eval_MOV_nocheck.
case: x => //= [x | x]; t_xrbindP => vs ?? hb ?? hv ; [ | move => ??? hm <- <- ] => <- <-; t_xrbindP => _ -> /=;
case: (eval_cond _ _) hb => [ b | [] // ] [<-] //= _ [<-];
case: vs => // v [] //; case: v => //= sz' w ok_w; [ case | rewrite /sets_low /=; apply: rbindP => w' ok_w' ];
case: b ok_w.
+ apply: rbindP => w' /of_val_word [s'] [w''] [hle ??]; subst => h.
  have {h} /seq_eq_injL [/Vword_inj [? ?] _] := ok_inj h; subst => /= <-.
  rewrite (eval_low_read _ hv) //=. update_set.
+ apply: rbindP => w' /truncate_wordP [hle ?]; subst w' => h.
  have {h} /seq_eq_injL [/Vword_inj [? ?] _] := ok_inj h; subst => /= <-; update_set.
+ apply: rbindP => ? /of_val_word [s'] [w''] [hle ? ?]; subst => h.
  have {h} /seq_eq_injL [/Vword_inj [? h] _] := ok_inj h; move: h; subst => /= ?; subst.
  move: ok_w'; rewrite truncate_word_u => - [<-] {w'}.
  rewrite (eval_low_read _ hv) //= => ->; update_set.
  rewrite truncate_word_u /= => h.
  have {h} /seq_eq_injL [/Vword_inj [? h] _] := ok_inj h; move: h; subst => /= ?; subst.
  move: ok_w'; rewrite truncate_word_u => - [<-] {w'}.
  rewrite hm /= => ->; update_set.
Qed.

Definition CMOVcc_desc sz := make_instr_desc (CMOVcc_gsc sz).

(* ----------------------------------------------------------------------------- *)

Lemma ADD_gsc sz :
   gen_sem_correct [:: TYoprd; TYoprd] (Ox86_ADD sz)
     (implicit_flags ++ [:: E sz 0])
     [:: E sz 0; E sz 1] [::] (ADD sz).
Proof.
move => x y; split => // gd m m'; rewrite /low_sem_aux /= !arg_of_oprdE /= /x86_add /eval_ADD.
case: x => // [ x | x ] /=; t_xrbindP => ???? h <-; [ | move => ?? h' <- ] => <-; t_xrbindP => ? /truncate_wordP [hle ->] ? /of_val_word [sz'] [?] [hle' ??]; subst => _ -> /= [<-].
+ by case => <-; rewrite (eval_low_read _ h) //; update_set.
apply: rbindP => /= m'' [<-] {m''}; rewrite truncate_word_u /= h (eval_low_read _ h') //= !zero_extend_u.
move => ?; update_set.
Qed.

Definition ADD_desc sz := make_instr_desc (ADD_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma SUB_gsc sz :
   gen_sem_correct [:: TYoprd; TYoprd] (Ox86_SUB sz)
      (implicit_flags ++ [:: E sz 0]) [:: E sz 0; E sz 1] [::] (SUB sz).
Proof.
move => x y; split => // gd m m'; rewrite /low_sem_aux /= !arg_of_oprdE /= /x86_sub /eval_SUB.
case: x => // [ x | x ] /=; t_xrbindP => ???? h <-; [ | move => ?? h' <- ] => <-; t_xrbindP => ? /truncate_wordP [hle ->] ? /of_val_word [sz'] [?] [hle' ??]; subst => _ -> /= [<-].
+ by case => <-; rewrite (eval_low_read _ h) //; update_set.
apply: rbindP => /= m'' [<-] {m''}; rewrite truncate_word_u /= h (eval_low_read _ h') //= !zero_extend_u.
move => ?; update_set.
Qed.

Definition SUB_desc sz := make_instr_desc (SUB_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma MUL_gsc sz :
  gen_sem_correct [:: TYoprd] (Ox86_MUL sz)
      (implicit_flags ++ [:: R RDX; R RAX])
      [:: R RAX; E sz 0] [::] (MUL sz).
Proof.
  rewrite /gen_sem_correct /low_sem_aux /= /eval_MUL /x86_mul => x; split => // gd m m'.
  rewrite arg_of_oprdE /=; t_xrbindP => vs ? ? vx ok_vx <- <- /=; t_xrbindP => wa /truncate_wordP [ha ->] {wa}.
  move => wx /of_val_word [sx] [?] [hx ??]; subst => /= _ -> /= <- [<-]; rewrite (eval_low_read _ ok_vx) {ok_vx} //; update_set.
Qed.

Definition MUL_desc sz := make_instr_desc (MUL_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma IMUL_gsc sz :
  gen_sem_correct [:: TYoprd ] (Ox86_IMUL sz) (implicit_flags ++ [:: R RDX; R RAX])
                   [:: R RAX; E sz 0] [::] (λ x, IMUL sz x None).
Proof.
  rewrite /gen_sem_correct /low_sem_aux /= /eval_IMUL /x86_imul => x; split => // gd m m'.
  rewrite arg_of_oprdE /=; t_xrbindP => vs ? ? vx ok_vx <- <- /=; t_xrbindP => wa /truncate_wordP [ha ->] {wa}.
  move => wx /of_val_word [sx] [?] [hx ??]; subst => /= _ -> /= <- [<-]; rewrite (eval_low_read _ ok_vx) {ok_vx} //=.
  update_set.
Qed.

Definition IMUL_desc sz := make_instr_desc (IMUL_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma IMULt_gsc sz :
  gen_sem_correct [:: TYoprd ; TYoprd] (Ox86_IMULt sz)
                   (implicit_flags ++ [:: E sz 0]) [:: E sz 0; E sz 1] [::]
                   (λ x y, IMUL sz x (Some (y, None))).
Proof.
  rewrite /gen_sem_correct /low_sem_aux /= /eval_IMUL /x86_imult => x; split => // gd m m'.
  rewrite !arg_of_oprdE /=.
  case: x => // [ x | x ] /=; t_xrbindP => vs ???; [ | move => -> <- ??] => hx <- <-; t_xrbindP => /= w /truncate_wordP [hsz] -> {w} w /of_val_word [?] [?] [hle ??]; subst => _ -> /= <-; rewrite (eval_low_read _ hx) ?zero_extend_u //=.
  + case => <-; update_set.
  apply: rbindP => wa [<-] /=; rewrite truncate_word_u /=.
  apply: rbindP => m''; rewrite /= /mem_write_mem /decode_addr /=.
  move => -> [<-] /=. update_set.
Qed.

Definition IMULt_desc sz := make_instr_desc (IMULt_gsc sz).

Lemma IMULtimm_gsc sz :
  gen_sem_correct [:: TYoprd ; TYoprd ; TYimm U32] (Ox86_IMULtimm sz)
                   (implicit_flags ++ [:: E sz 0]) [:: E sz 1; E U32 2] [::]
    (λ (x y : interp_ty TYoprd) (z : interp_ty (TYimm U32)), IMUL sz x (Some (y, Some z))).
Proof.
  rewrite /gen_sem_correct /low_sem_aux /= /eval_IMUL /x86_imult => x; split => // gd m m'.
  rewrite arg_of_oprdE /=.
  case: x => // [ x | x ] /=;
    t_xrbindP => ??? h <-;
    t_xrbindP => ? /of_val_word [?] [?] [hle ??];
    subst => /= ? /truncate_wordP => - [hle64] ?; subst => _ -> /= <-;
    rewrite (eval_low_read _ h) // !zero_extend_sign_extend //=.
  - case => <- /=; update_set.
  rewrite /sets_low /= truncate_word_u /= /mem_write_mem /decode_addr /=.
  apply: rbindP => m'' -> [<-] /=; update_set.
Qed.

Definition IMULtimm_desc sz := make_instr_desc (IMULtimm_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma DIV_gsc sz :
  gen_sem_correct [:: TYoprd] (Ox86_DIV sz)
      (implicit_flags ++ [:: R RAX; R RDX])
      [:: R RDX; R RAX; E sz 0] [::] (DIV sz).
Proof.
  rewrite /gen_sem_correct /low_sem_aux /= /eval_DIV /x86_div => x; split => // gd m m'.
  rewrite arg_of_oprdE /=; t_xrbindP => vs ???? h <- <- <-; t_xrbindP => ? /of_val_word [?] [?] [hle /Vword_inj [??] ?]; subst => /=.
  move => ? ; rewrite /truncate_word hle => - [<-] ? /of_val_word [?] [?] [hle' ??]; subst => _ -> /=.
  rewrite (eval_low_read _ h) //=.
  case: ifP => // _ [<-] [<-]; update_set.
Qed.

Definition DIV_desc sz := make_instr_desc (DIV_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma IDIV_gsc sz :
  gen_sem_correct [:: TYoprd] (Ox86_IDIV sz)
      (implicit_flags ++ [:: R RAX; R RDX])
      [:: R RDX; R RAX; E sz 0] [::] (IDIV sz).
Proof.
  rewrite /gen_sem_correct /low_sem_aux /= /eval_IDIV /x86_idiv => x; split => // gd m m'.
  rewrite arg_of_oprdE /=; t_xrbindP => vs ???? hx <- <- <- /=.
  apply: rbindP => ? /truncate_wordP [hle <-].
  rewrite /truncate_word hle /=; t_xrbindP => ? /of_val_word [?][?][hle' ??]; subst => _ -> /=.
  rewrite (eval_low_read _ hx) //=; case: ifP => // _ [<-] [<-].
  update_set.
Qed.

Definition IDIV_desc sz := make_instr_desc (IDIV_gsc sz).

Lemma word_of_b2z sz b :
  Z.b2z b = @wunsigned sz (if b then 1%R else 0%R).
Proof. by case: b. Qed.

(* ----------------------------------------------------------------------------- *)
Lemma ADC_gsc sz :
   gen_sem_correct [:: TYoprd; TYoprd] (Ox86_ADC sz)
       (implicit_flags ++ [:: E sz 0])
       [:: E sz 0; E sz 1; F CF] [::] (ADC sz).
Proof.
move => x y; split => // gd m m'.
rewrite /low_sem_aux /= /eval_ADC /x86_adc !arg_of_oprdE /=.
case: x => //= [ x | x ]; t_xrbindP => ???? hx; [ | move => <- ?? hy ] => ?? hb <- <- <- /=;
t_xrbindP => ? /truncate_wordP [hle ->] ? /of_val_word [?] [?] [hle' ??]; subst;
move => b /to_boolI ? _ -> /= [?]; subst; rewrite (value_of_boolI hb) {hb} !(word_of_b2z sz) /add_carry !wrepr_add !wrepr_unsigned.
- case => <-. rewrite (eval_low_read _ hx) //=. update_set.
rewrite /sets_low /= truncate_word_u /= !decode_addr_set_rflags hx /= (eval_low_read _ hy) //= decode_addr_update_rflags.
rewrite /mem_write_mem /= !zero_extend_u.
apply: rbindP => m'' /= -> [<-] /=. update_set.
Qed.

Definition ADC_desc sz := make_instr_desc (ADC_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma SBB_gsc sz :
   gen_sem_correct [:: TYoprd; TYoprd] (Ox86_SBB sz)
       (implicit_flags ++ [:: E sz 0])
       [:: E sz 0; E sz 1; F CF] [::] (SBB sz).
Proof.
move => x y; split => // gd m m'; rewrite /low_sem_aux /= !arg_of_oprdE /eval_SBB /x86_sbb /=.
case: x => //= [ x | x ]; t_xrbindP => ???; [ | move => ? hptr <- ? ] => ? hy ?? hb <- <- <- /=;
t_xrbindP => ? /truncate_wordP [hle ->] ? /of_val_word [?] [?] [hle' ??];
subst => b /to_boolI ? _ -> /=; subst => - [<-]; rewrite (value_of_boolI hb) {hb} (eval_low_read _ hy) //= !(word_of_b2z sz) /sub_borrow !wrepr_sub !wrepr_unsigned Z.sub_add_distr.
- case => <-. update_set.
rewrite /sets_low /= truncate_word_u /= !decode_addr_set_rflags hptr /= decode_addr_update_rflags.
rewrite /mem_write_mem /= !zero_extend_u !Z.sub_add_distr.
apply: rbindP => m'' /= -> [<-] /=. update_set.
Qed.

Definition SBB_desc sz := make_instr_desc (SBB_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma NEG_gsc sz :
  gen_sem_correct [:: TYoprd] (Ox86_NEG sz)
     (implicit_flags ++ [:: E sz 0])
     [:: E sz 0] [::] (NEG sz).
Proof.
move => x; split => // gd m m'; rewrite /low_sem_aux /= arg_of_oprdE /eval_NEG /x86_neg /=.
case: x => //= [ x | x ].
- t_xrbindP => ?? /truncate_wordP [hle ->] _ -> /= [<-] [<-]; update_set.
t_xrbindP => ???? hx <- <-; rewrite /= truncate_word_u /=.
t_xrbindP => _ -> /= [<-].
rewrite /sets_low /= truncate_word_u hx /= => ?; update_set.
Qed.

Definition NEG_desc sz := make_instr_desc (NEG_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma INC_gsc sz :
  gen_sem_correct [:: TYoprd] (Ox86_INC sz)
     (implicit_flags_noCF ++ [:: E sz 0])
     [:: E sz 0] [::] (INC sz).
Proof.
move => x; split => // gd m m'; rewrite /low_sem_aux /= arg_of_oprdE /eval_INC /x86_inc /=.
case: x => //= [ x | x ].
- t_xrbindP => ?? /truncate_wordP [hle ->] _ -> /= [<-] [<-]; update_set.
t_xrbindP => ???? hx <- <-; rewrite /= truncate_word_u /=.
t_xrbindP => _ -> /= [<-].
rewrite /sets_low /= truncate_word_u hx /= => ?; update_set.
Qed.

Definition INC_desc sz := make_instr_desc (INC_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma DEC_gsc sz :
  gen_sem_correct [:: TYoprd] (Ox86_DEC sz)
     (implicit_flags_noCF ++ [:: E sz 0])
     [:: E sz 0] [::] (DEC sz).
Proof.
move => x; split => // gd m m'; rewrite /low_sem_aux /= arg_of_oprdE /eval_DEC /x86_dec.
case: x => //= [ x | x ].
- t_xrbindP => ?? /truncate_wordP [? ->] _ -> /= [<-] [<-]; update_set.
t_xrbindP => ???? hx <- <-; rewrite /= truncate_word_u /=.
t_xrbindP => _ -> /= [<-].
rewrite /sets_low /= truncate_word_u hx /= => ?; update_set.
Qed.

Definition DEC_desc sz := make_instr_desc (DEC_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma SETcc_gsc :
  gen_sem_correct [:: TYcondt; TYoprd] Ox86_SETcc
     [:: E U8 1]
     [:: Eb 0] [::] SETcc.
Proof.
move => ct x; split => // gd m m'; rewrite /low_sem_aux /= /eval_SETcc /x86_setcc.
case: x => //= [ x | x ]; t_xrbindP => ??? hb <-; t_xrbindP => b /to_boolI ? ?; subst.
- case => <-; rewrite (value_of_boolI hb) {hb} /=; case: b; update_set.
rewrite /sets_low /= zero_extend_u (value_of_boolI hb) {hb}.
case: b => /=.
- replace (wrepr _ _) with (1%R : u8) by by apply/eqP.
  move => ?; update_set.
rewrite wrepr0 => ?; update_set.
Qed.

Definition SETcc_desc := make_instr_desc SETcc_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma BT_gsc sz :
  gen_sem_correct [:: TYoprd; TYireg] (Ox86_BT sz)
     [:: F CF]
     [:: E sz 0; E sz 1] [::] (BT sz).
Proof.
move => x y; split => // gd m m'; rewrite /low_sem_aux /= !arg_of_oprdE /eval_BT /x86_bt /=.
t_xrbindP => ??? hx ?? hy <- <-; t_xrbindP => ? /of_val_word [?] [?] [hle ??];
subst => ? /of_val_word [?] [?] [hle' ??] _ -> /=; subst => <- [<-].
rewrite (eval_low_read _ hx) //=.
case: y hy => ? hy; have /Vword_inj := ok_inj hy => {hy} -[??]; subst => /=; update_set.
Qed.

Definition BT_desc sz := make_instr_desc (BT_gsc sz).

(* ----------------------------------------------------------------------------- *)

Definition scale_of_z sz (z: pointer) :=
  match wunsigned (zero_extend sz z) with
  | 1 => Scale1
  | 2 => Scale2
  | 4 => Scale4
  | 8 => Scale8
  | _ => Scale1
  end%Z.

Definition mk_LEA sz (dest:register) (disp: pointer) (base:ireg) (scale: pointer) (offset:ireg) :=
  let addr :=
    let (disp, base) :=
      match base with
      | Reg_ir r => (disp, Some r)
      | Imm_ir w => (disp + w, None)%R
      end in
    let (disp, offset) :=
      match offset with
      | Reg_ir r => (disp, Some r)
      | Imm_ir w => (disp + scale * w, None)%R
      end in
    let scale := scale_of_z sz scale in
    {| ad_disp := disp; ad_base := base; ad_scale := scale; ad_offset := offset |} in
  LEA sz dest (Adr_op addr).

Lemma eval_low_ireg gd m sz y :
  eval_low gd m (arg_of_oprd_sz sz match y with
                                   | Imm_ir i => Imm_op i
                                   | Reg_ir r => Reg_op r
                                   end) = ok (Vword match y with Imm_ir i => i | Reg_ir r => xreg m r end).
Proof. by case: y. Qed.

Lemma check_scale_of sz (scale: pointer) :
  check_scale (wunsigned (zero_extend sz scale)) →
  zero_extend sz (scale_of_z sz scale) = zero_extend sz scale.
Proof.
move => h; apply: wunsigned_inj; rewrite /scale_of_z.
by case /orP: h => [ /orP [ /orP [] /eqP -> | /eqP -> ] | /eqP ->]; case: sz.
Qed.

Lemma LEA_gsc sz :
  gen_sem_correct [:: TYreg; TYimm Uptr; TYireg; TYimm Uptr; TYireg] (Ox86_LEA sz)
     [:: E sz 0]
     [:: E Uptr 1; E sz 2; E Uptr 3; E sz 4] [::] (mk_LEA sz).
Proof.
move => x /= disp base scale offset; split => // gd m m'.
rewrite /low_sem_aux /= !arg_of_oprdE /= !eval_low_ireg /= /eval_LEA /x86_lea !sign_extend_u.
t_xrbindP => ? _ /truncate_wordP [hle] ->.
rewrite /truncate_word hle => _ [<-] _ [<-] _ [<-] _ -> /=.
case: ifP => // hsc [<-] [<-].
rewrite /decode_addr.
case: base offset => [ base | base ] [ offset | offset ] /=;
rewrite ?(GRing.mulr0, GRing.addr0) -!(wadd_zero_extend, wmul_zero_extend) // ?check_scale_of //;
try update_set.
set α := (_ + _)%R; set β := (_ + _)%R.
replace α with β by ssrring.ssring; update_set.
Qed.

Definition LEA_desc sz := make_instr_desc (LEA_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma TEST_gsc sz :
  gen_sem_correct [:: TYoprd; TYoprd] (Ox86_TEST sz)
     implicit_flags
     [:: E sz 0; E sz 1] [::] (TEST sz).
Proof.
move => x y; split => // gd m m'.
rewrite /low_sem_aux /= !arg_of_oprdE /eval_TEST /x86_test /=; t_xrbindP => ??? hx ?? hy <- <-;
t_xrbindP => ? /of_val_word [?] [?] [hle??]; subst => ? /of_val_word [?] [?] [hle' ??]; subst => _ -> /=.
case => <- [<-]; rewrite (eval_low_read _ hx) // (eval_low_read _ hy) //; update_set.
Qed.

Definition TEST_desc sz := make_instr_desc (TEST_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma CMP_gsc sz :
  gen_sem_correct [:: TYoprd; TYoprd] (Ox86_CMP sz)
     implicit_flags
     [:: E sz 0; E sz 1] [::] (CMP sz).
Proof.
move => x y; split => // gd m m'.
rewrite /low_sem_aux /= !arg_of_oprdE /eval_CMP /x86_cmp /=; t_xrbindP => ??? hx ?? hy <- <-;
t_xrbindP => ? /of_val_word [?] [?] [hle??]; subst => ? /of_val_word [?] [?] [hle' ??]; subst => _ -> /=.
case => <- [<-]; rewrite (eval_low_read _ hx) // (eval_low_read _ hy) //; update_set.
Qed.

Definition CMP_desc sz := make_instr_desc (CMP_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma AND_gsc sz :
  gen_sem_correct [:: TYoprd; TYoprd] (Ox86_AND sz)
     (implicit_flags ++ [:: E sz 0])
     [:: E sz 0; E sz 1] [::] (AND sz).
Proof.
move => x y; split => // gd m m'; rewrite /low_sem_aux /= !arg_of_oprdE /= /x86_and /eval_AND.
case: x => // [ x | x ] /=; t_xrbindP => ???? h <-; [ | move => ?? h' <- ] => <-; t_xrbindP => ? /truncate_wordP [hle ->] ? /of_val_word [sz'] [?] [hle' ??]; subst => _ -> /= [<-].
+ by case => <-; rewrite (eval_low_read _ h) //; update_set.
apply: rbindP => /= m'' [<-] {m''}; rewrite truncate_word_u /= h (eval_low_read _ h') //= !zero_extend_u.
move => ?; update_set.
Qed.

Definition AND_desc sz := make_instr_desc (AND_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma OR_gsc sz :
  gen_sem_correct [:: TYoprd; TYoprd] (Ox86_OR sz)
     (implicit_flags ++ [:: E sz 0])
     [:: E sz 0; E sz 1] [::] (OR sz).
Proof.
move => x y; split => // gd m m'; rewrite /low_sem_aux /= !arg_of_oprdE /= /x86_or /eval_OR.
case: x => // [ x | x ] /=; t_xrbindP => ???? h <-; [ | move => ?? h' <- ] => <-; t_xrbindP => ? /truncate_wordP [hle ->] ? /of_val_word [sz'] [?] [hle' ??]; subst => _ -> /= [<-].
+ by case => <-; rewrite (eval_low_read _ h) //; update_set.
apply: rbindP => /= m'' [<-] {m''}; rewrite truncate_word_u /= h (eval_low_read _ h') //= !zero_extend_u.
move => ?; update_set.
Qed.

Definition OR_desc sz := make_instr_desc (OR_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma XOR_gsc sz :
  gen_sem_correct [:: TYoprd; TYoprd] (Ox86_XOR sz)
     (implicit_flags ++ [:: E sz 0])
     [:: E sz 0; E sz 1] [::] (XOR sz).
Proof.
move => x y; split => // gd m m'; rewrite /low_sem_aux /= !arg_of_oprdE /= /x86_xor /eval_XOR.
case: x => // [ x | x ] /=; t_xrbindP => ???? h <-; [ | move => ?? h' <- ] => <-; t_xrbindP => ? /truncate_wordP [hle ->] ? /of_val_word [sz'] [?] [hle' ??]; subst => _ -> /= [<-].
+ by case => <-; rewrite (eval_low_read _ h) //; update_set.
apply: rbindP => /= m'' [<-] {m''}; rewrite truncate_word_u /= h (eval_low_read _ h') //= !zero_extend_u.
move => ?; update_set.
Qed.

Definition XOR_desc sz := make_instr_desc (XOR_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma NOT_gsc sz :
  gen_sem_correct [:: TYoprd] (Ox86_NOT sz)
     [:: E sz 0]
     [:: E sz 0] [::] (NOT sz).
Proof.
move => x; split => // gd m m'; rewrite /low_sem_aux /= arg_of_oprdE /eval_NOT /x86_not /=.
case: x => //= [ x | x ].
- t_xrbindP => ?? /truncate_wordP [hle ->] _ -> /= <- [<-]; update_set.
t_xrbindP => ???? hx <- <-; rewrite /= truncate_word_u /=.
t_xrbindP => _ -> /= <-.
rewrite /sets_low /= truncate_word_u hx /= => ?; update_set.
Qed.

Definition NOT_desc sz := make_instr_desc (NOT_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma rflagv_leb_undef rf f f' :
  rflagv_leb (RflagMap.oset rf f Undef f') (rf f').
Proof. rewrite ffunE; case: eqP => // _; reflexivity. Qed.

Lemma ROL_gsc sz :
  gen_sem_correct [:: TYoprd; TYireg ] (Ox86_ROL sz)
    [:: ADImplicit (var_of_flag OF) ; ADImplicit (var_of_flag CF) ; E sz 0 ]
    [:: E sz 0 ; ADExplicit (Some sz) 1 (Some RCX) ]
    [::] (ROL sz).
Proof.
move => x y; split => // gd m m'; rewrite /low_sem_aux /= !arg_of_oprdE /= /eval_ROL /x86_rol.
case: y => //= [ y | y ].
- case: x => //= [ x | x ].
  + t_xrbindP => ? _ /truncate_wordP [hle] -> _ -> /=.
    rewrite /read_ireg; case: ifP => _ [<-].
    * case => <-. eexists; split; first reflexivity.
      by constructor => // f; etransitivity; apply/rflagv_leb_undef.
    case: ifP => _ [<-]; update_set.
  t_xrbindP =>???? hptr <- <- /=; rewrite truncate_word_u /=.
  t_xrbindP => _ -> /=; case: ifP => _ [<-]; rewrite /sets_low /=.
  + rewrite /truncate_word cmp_le_refl /= !zero_extend_u /mem_write_mem/=.
    rewrite !decode_addr_unset_rflags hptr /=.
    t_xrbindP => ? -> <- /=.
    eexists; split; first reflexivity.
    by constructor => // f; etransitivity; apply/rflagv_leb_undef.
  case: ifP => _; rewrite hptr /= !decode_addr_set_rflags ?decode_addr_unset_rflags truncate_word_u /= /mem_write_mem /=; t_xrbindP => ? -> <-; update_set.
case: eqP => // <- {y} /=.
  rewrite /sets_low /=.
(* Duplicate of above proof script *)
case: x => //= [ x | x ].
+ t_xrbindP => ? _ /truncate_wordP [hle] -> _ -> /=.
  rewrite /read_ireg; case: ifP => _ [<-].
  * case => <-. eexists; split; first reflexivity.
    by constructor => // f; etransitivity; apply/rflagv_leb_undef.
  case: ifP => _ [<-]; update_set.
t_xrbindP =>???? hptr <- <- /=; rewrite truncate_word_u /=.
t_xrbindP => _ -> /=; case: ifP => _ [<-]; rewrite /sets_low /=.
+ rewrite /truncate_word cmp_le_refl /= !zero_extend_u /mem_write_mem/=.
  rewrite !decode_addr_unset_rflags hptr /=.
  t_xrbindP => ? -> <- /=.
  eexists; split; first reflexivity.
  by constructor => // f; etransitivity; apply/rflagv_leb_undef.
case: ifP => _; rewrite hptr /= !decode_addr_set_rflags ?decode_addr_unset_rflags truncate_word_u /= /mem_write_mem /=; t_xrbindP => ? -> <-; update_set.
Qed.

Definition ROL_desc sz := make_instr_desc (ROL_gsc sz).

Lemma ROR_gsc sz :
  gen_sem_correct [:: TYoprd; TYireg ] (Ox86_ROR sz)
    [:: ADImplicit (var_of_flag OF) ; ADImplicit (var_of_flag CF) ; E sz 0 ]
    [:: E sz 0 ; ADExplicit (Some sz) 1 (Some RCX) ]
    [::] (ROR sz).
Proof.
move => x y; split => // gd m m'; rewrite /low_sem_aux /= !arg_of_oprdE /= /eval_ROR /x86_ror.
case: y => //= [ y | y ].
- case: x => //= [ x | x ].
  + t_xrbindP => ? _ /truncate_wordP [hle] -> _ -> /=.
    rewrite /read_ireg; case: ifP => _ [<-].
    * case => <-. eexists; split; first reflexivity.
      by constructor => // f; etransitivity; apply/rflagv_leb_undef.
    case: ifP => _ [<-]; update_set.
  t_xrbindP =>???? hptr <- <- /=; rewrite truncate_word_u /=.
  t_xrbindP => _ -> /=; case: ifP => _ [<-]; rewrite /sets_low /=.
  + rewrite /truncate_word cmp_le_refl /= !zero_extend_u /mem_write_mem/=.
    rewrite !decode_addr_unset_rflags hptr /=.
    t_xrbindP => ? -> <- /=.
    eexists; split; first reflexivity.
    by constructor => // f; etransitivity; apply/rflagv_leb_undef.
  case: ifP => _; rewrite hptr /= !decode_addr_set_rflags ?decode_addr_unset_rflags truncate_word_u /= /mem_write_mem /=; t_xrbindP => ? -> <-; update_set.

case: eqP => // <- {y} /=.
  rewrite /sets_low /=.
(* Duplicate of above proof script *)
case: x => //= [ x | x ].
+ t_xrbindP => ? _ /truncate_wordP [hle] -> _ -> /=.
  rewrite /read_ireg; case: ifP => _ [<-].
  * case => <-. eexists; split; first reflexivity.
    by constructor => // f; etransitivity; apply/rflagv_leb_undef.
  case: ifP => _ [<-]; update_set.
t_xrbindP =>???? hptr <- <- /=; rewrite truncate_word_u /=.
t_xrbindP => _ -> /=; case: ifP => _ [<-]; rewrite /sets_low /=.
+ rewrite /truncate_word cmp_le_refl /= !zero_extend_u /mem_write_mem/=.
  rewrite !decode_addr_unset_rflags hptr /=.
  t_xrbindP => ? -> <- /=.
  eexists; split; first reflexivity.
  by constructor => // f; etransitivity; apply/rflagv_leb_undef.
case: ifP => _; rewrite hptr /= !decode_addr_set_rflags ?decode_addr_unset_rflags truncate_word_u /= /mem_write_mem /=; t_xrbindP => ? -> <-; update_set.
Qed.

Definition ROR_desc sz := make_instr_desc (ROR_gsc sz).

Lemma SHL_gsc sz :
  gen_sem_correct [:: TYoprd; TYireg] (Ox86_SHL sz)
     (implicit_flags ++ [:: E sz 0])
     [:: E sz 0; ADExplicit (Some sz) 1 (Some RCX)]
     [::] (SHL sz).
Proof.
move => x y; split => // gd m m'. rewrite /low_sem_aux /= !arg_of_oprdE /= /x86_shl /eval_SHL.
case: y => //= [ y | y ].
case: x => //= [ x | x ]; t_xrbindP => ?;
[ move => ? /truncate_wordP [hle] ->
| move=> ??? hptr <- <-; rewrite /= truncate_word_u /=; apply: rbindP ];
move => _ -> /=; case: ifP => _ [<-].
- case => <-; eexists; split; first reflexivity.
  constructor => //= f.
  repeat (etransitivity; [apply/rflagv_leb_undef |]); apply: rflagv_leb_refl.
- rewrite /rflags_of_sh. case: ifP => _ [<-]; update_set.
- rewrite /sets_low /= truncate_word_u /= hptr /= !decode_addr_unset_rflags /mem_write_mem.
  apply: rbindP => ? -> /= [<-].
  eexists; split; first reflexivity.
  constructor => //= f; repeat (etransitivity; [apply/rflagv_leb_undef |]); apply: rflagv_leb_refl.
rewrite /sets_low /= /rflags_of_sh /= hptr /=.
case: ifP => /= _; rewrite truncate_word_u /= !decode_addr_set_rflags /mem_write_mem /=;
apply: rbindP => ? -> [<-] /=; update_set.

case: eqP => // <- {y} /=.
  rewrite /sets_low /=.
(* Duplicate of above *)
case: x => //= [ x | x ]; t_xrbindP => ?;
[ move => ? /truncate_wordP [hle] ->
| move=> ??? hptr <- <-; rewrite /= truncate_word_u /=; apply: rbindP ];
move => _ -> /=; case: ifP => _ [<-].
- case => <-; eexists; split; first reflexivity.
  constructor => //= f.
  repeat (etransitivity; [apply/rflagv_leb_undef |]); apply: rflagv_leb_refl.
- rewrite /rflags_of_sh. case: ifP => _ [<-]; update_set.
- rewrite /sets_low /= truncate_word_u /= hptr /= !decode_addr_unset_rflags /mem_write_mem.
  apply: rbindP => ? -> /= [<-].
  eexists; split; first reflexivity.
  constructor => //= f; repeat (etransitivity; [apply/rflagv_leb_undef |]); apply: rflagv_leb_refl.
rewrite /sets_low /= /rflags_of_sh /= hptr /=.
case: ifP => /= _; rewrite truncate_word_u /= !decode_addr_set_rflags /mem_write_mem /=;
apply: rbindP => ? -> [<-] /=; update_set.
Qed.

Definition SHL_desc sz := make_instr_desc (SHL_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma SHR_gsc sz :
  gen_sem_correct [:: TYoprd; TYireg] (Ox86_SHR sz)
     (implicit_flags ++ [:: E sz 0])
     [:: E sz 0; ADExplicit (Some sz) 1 (Some RCX)]
     [::] (SHR sz).
Proof.
move => x y; split => // gd m m'; rewrite /low_sem_aux /= !arg_of_oprdE /= /x86_shr /eval_SHR.
case: y => //= [ y | y ].
case: x => //= [ x | x ]; t_xrbindP => ?;
[ move => ? /truncate_wordP [hle] ->
| move=> ??? hptr <- <-; rewrite /= truncate_word_u /=; apply: rbindP ];
move => _ -> /=; case: ifP => _ [<-].
- case => <-; eexists; split; first reflexivity.
  constructor => //= f.
  repeat (etransitivity; [apply/rflagv_leb_undef |]); apply: rflagv_leb_refl.
- rewrite /rflags_of_sh. case: ifP => _ [<-]; update_set.
- rewrite /sets_low /= truncate_word_u /= hptr /= !decode_addr_unset_rflags /mem_write_mem.
  apply: rbindP => ? -> /= [<-].
  eexists; split; first reflexivity.
  constructor => //= f; repeat (etransitivity; [apply/rflagv_leb_undef |]); apply: rflagv_leb_refl.
rewrite /sets_low /= /rflags_of_sh /= hptr /=.
case: ifP => /= _; rewrite truncate_word_u /= !decode_addr_set_rflags /mem_write_mem /=;
apply: rbindP => ? -> [<-] /=; update_set.

case: eqP => // <- {y} /=.
  rewrite /sets_low /=.
(* Duplicate of above *)
case: x => //= [ x | x ]; t_xrbindP => ?;
[ move => ? /truncate_wordP [hle] ->
| move=> ??? hptr <- <-; rewrite /= truncate_word_u /=; apply: rbindP ];
move => _ -> /=; case: ifP => _ [<-].
- case => <-; eexists; split; first reflexivity.
  constructor => //= f.
  repeat (etransitivity; [apply/rflagv_leb_undef |]); apply: rflagv_leb_refl.
- rewrite /rflags_of_sh. case: ifP => _ [<-]; update_set.
- rewrite /sets_low /= truncate_word_u /= hptr /= !decode_addr_unset_rflags /mem_write_mem.
  apply: rbindP => ? -> /= [<-].
  eexists; split; first reflexivity.
  constructor => //= f; repeat (etransitivity; [apply/rflagv_leb_undef |]); apply: rflagv_leb_refl.
rewrite /sets_low /= /rflags_of_sh /= hptr /=.
case: ifP => /= _; rewrite truncate_word_u /= !decode_addr_set_rflags /mem_write_mem /=;
apply: rbindP => ? -> [<-] /=; update_set.
Qed.

Definition SHR_desc sz := make_instr_desc (SHR_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma SAR_gsc sz :
  gen_sem_correct [:: TYoprd; TYireg] (Ox86_SAR sz)
     (implicit_flags ++ [:: E sz 0])
     [:: E sz 0; ADExplicit (Some sz) 1 (Some RCX)]
     [::] (SAR sz).
Proof.
move => x y; split => // gd m m'; rewrite /low_sem_aux /= !arg_of_oprdE /= /x86_sar /eval_SAR.
case: y => //= [ y | y ].
case: x => //= [ x | x ]; t_xrbindP => ?;
[ move => ? /truncate_wordP [hle] ->
| move=> ??? hptr <- <-; rewrite /= truncate_word_u /=; apply: rbindP ];
move => _ -> /=; case: ifP => _ [<-].
- case => <-; eexists; split; first reflexivity.
  constructor => //= f.
  repeat (etransitivity; [apply/rflagv_leb_undef |]); apply: rflagv_leb_refl.
- rewrite /rflags_of_sh. case: ifP => _ [<-]; update_set.
- rewrite /sets_low /= truncate_word_u /= hptr /= !decode_addr_unset_rflags /mem_write_mem.
  apply: rbindP => ? -> /= [<-].
  eexists; split; first reflexivity.
  constructor => //= f; repeat (etransitivity; [apply/rflagv_leb_undef |]); apply: rflagv_leb_refl.
rewrite /sets_low /= /rflags_of_sh /= hptr /=.
case: ifP => /= _; rewrite truncate_word_u /= !decode_addr_set_rflags /mem_write_mem /=;
apply: rbindP => ? -> [<-] /=; update_set.

case: eqP => // <- {y} /=.
  rewrite /sets_low /=.
(* Duplicate of above *)
case: x => //= [ x | x ]; t_xrbindP => ?;
[ move => ? /truncate_wordP [hle] ->
| move=> ??? hptr <- <-; rewrite /= truncate_word_u /=; apply: rbindP ];
move => _ -> /=; case: ifP => _ [<-].
- case => <-; eexists; split; first reflexivity.
  constructor => //= f.
  repeat (etransitivity; [apply/rflagv_leb_undef |]); apply: rflagv_leb_refl.
- rewrite /rflags_of_sh. case: ifP => _ [<-]; update_set.
- rewrite /sets_low /= truncate_word_u /= hptr /= !decode_addr_unset_rflags /mem_write_mem.
  apply: rbindP => ? -> /= [<-].
  eexists; split; first reflexivity.
  constructor => //= f; repeat (etransitivity; [apply/rflagv_leb_undef |]); apply: rflagv_leb_refl.
rewrite /sets_low /= /rflags_of_sh /= hptr /=.
case: ifP => /= _; rewrite truncate_word_u /= !decode_addr_set_rflags /mem_write_mem /=;
apply: rbindP => ? -> [<-] /=; update_set.
Qed.

Definition SAR_desc sz := make_instr_desc (SAR_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma SHLD_gsc sz :
  gen_sem_correct [:: TYoprd; TYreg; TYireg] (Ox86_SHLD sz)
     (implicit_flags ++ [:: E sz 0])
     [:: E sz 0; E sz 1; E sz 2] [::] (SHLD sz).
Proof.
move => x y; split => // gd m m'; rewrite /low_sem_aux /= !arg_of_oprdE /= eval_low_ireg /= /x86_shld /eval_SHLD.
case: x => //= [ x | x ]; t_xrbindP => ?;
[ move => ? /truncate_wordP [hle] ->; rewrite /truncate_word hle => _ [<-]
| move=> ??? hptr <- <-; rewrite /= truncate_word_u /=; t_xrbindP => ? /truncate_wordP [hle] -> ];
move => _ -> /=; case: ifP => _ [<-].
- case => <-; eexists; split; first reflexivity.
  constructor => //= f.
  repeat (etransitivity; [apply/rflagv_leb_undef |]); apply: rflagv_leb_refl.
- rewrite /rflags_of_sh. case: ifP => _ [<-]; update_set.
- rewrite /sets_low /= truncate_word_u /= hptr /= !decode_addr_unset_rflags /mem_write_mem.
  apply: rbindP => ? -> /= [<-].
  eexists; split; first reflexivity.
  constructor => //= f; repeat (etransitivity; [apply/rflagv_leb_undef |]); apply: rflagv_leb_refl.
rewrite /sets_low /= /rflags_of_sh /= hptr /=.
case: ifP => /= _; rewrite truncate_word_u /= !decode_addr_set_rflags /mem_write_mem /=;
apply: rbindP => ? -> [<-] /=; update_set.
Qed.

Definition SHLD_desc sz := make_instr_desc (SHLD_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma Set0_gsc sz :
  gen_sem_correct [:: TYoprd] (Oset0 sz)
     (implicit_flags ++ [:: E sz 0])
     [::] [::] (fun x => XOR sz x x).
Proof.
move => x; split => // gd m m'; rewrite /low_sem_aux /= /eval_XOR.
case: x => //= [ x | x ]; t_xrbindP => vs _ -> /= <-.
- by case => <- /=; rewrite wxor_xx /= /rflags_of_bwop /SF_of_word msb0; update_set.
rewrite /sets_low /= truncate_word_u /= /mem_write_mem /= !decode_addr_set_rflags.
apply: rbindP => m'' hw [<-].
have [o ->] := write_mem_can_read hw.
rewrite /= wxor_xx decode_addr_update_rflags /= hw /= /rflags_of_bwop /SF_of_word msb0; update_set.
Qed.

Definition Set0_desc sz := make_instr_desc (Set0_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma eval_low_rm128 gd m x sz (v: word sz) :
  eval_low gd m match x with RM128_reg r => Axreg r | RM128_mem a => Aaddr U128 a end = ok (Vword v) →
  read_rm128 x m = ok (zero_extend _ v).
Proof.
  by case: x => [ r | a ]; [ | apply: rbindP => ?? ] => /(@ok_inj _ _ _ _) /Vword_inj [??]; subst => /=; rewrite zero_extend_u.
Qed.

(* ----------------------------------------------------------------------------- *)
Lemma VPXOR_gsc :
  gen_sem_correct [:: TYrm128 ; TYrm128 ; TYrm128 ] Ox86_VPXOR
                  [:: E U128 0 ] [:: E U128 1 ; E U128 2 ] [::] VPXOR.
Proof.
move => d x y; split => // gd m m'.
rewrite /low_sem_aux /= /eval_VPXOR /eval_bitwise_128 /x86_vpxor /=; t_xrbindP => vs ? kx hx ? ky hy <- <-; t_xrbindP => vx /to_wordI [szx] [wx] [hlex ? ->] {vx}; subst kx => vy /to_wordI [szy] [wy] [hley ? ->] {vy}; subst ky => <- {vs}.
rewrite (eval_low_rm128 hx) (eval_low_rm128 hy) /= /sets_low /=.
case: d => [ r | a ] /=; [ case | ]; rewrite zero_extend_u => ->; eexists; split; reflexivity.
Qed.

Definition VPXOR_desc := make_instr_desc VPXOR_gsc.

(* ----------------------------------------------------------------------------- *)

Definition sopn_desc ii (c : sopn) : ciexec instr_desc :=
  match c with
  | Omulu _ | Oaddcarry _ | Osubcarry _ => cierror ii (Cerr_assembler (AsmErr_string "sopn_desc"))
  | Oset0 sz => ok (Set0_desc sz)
  | Ox86_MOV sz => ok (MOV_desc sz)
  | Ox86_CMOVcc sz => ok (CMOVcc_desc sz)
  | Ox86_ADD sz => ok (ADD_desc sz)
  | Ox86_SUB sz => ok (SUB_desc sz)
  | Ox86_MUL sz => ok (MUL_desc sz)
  | Ox86_IMUL sz => ok (IMUL_desc sz)
  | Ox86_IMULt sz => ok (IMULt_desc sz)
  | Ox86_IMULtimm sz => ok (IMULtimm_desc sz)
  | Ox86_DIV sz => ok (DIV_desc sz)
  | Ox86_IDIV sz => ok (IDIV_desc sz)
  | Ox86_ADC sz => ok (ADC_desc sz)
  | Ox86_SBB sz => ok (SBB_desc sz)
  | Ox86_NEG sz => ok (NEG_desc sz)
  | Ox86_INC sz => ok (INC_desc sz)
  | Ox86_DEC sz => ok (DEC_desc sz)
  | Ox86_SETcc   => ok SETcc_desc
  | Ox86_BT sz => ok (BT_desc sz)
  | Ox86_LEA sz => ok (LEA_desc sz)
  | Ox86_TEST sz => ok (TEST_desc sz)
  | Ox86_CMP sz => ok (CMP_desc sz)
  | Ox86_AND sz => ok (AND_desc sz)
  | Ox86_OR sz => ok (OR_desc sz)
  | Ox86_XOR sz => ok (XOR_desc sz)
  | Ox86_NOT sz => ok (NOT_desc sz)
  | Ox86_ROL sz => ok (ROL_desc sz)
  | Ox86_ROR sz => ok (ROR_desc sz)
  | Ox86_SHL sz => ok (SHL_desc sz)
  | Ox86_SHR sz => ok (SHR_desc sz)
  | Ox86_SAR sz => ok (SAR_desc sz)
  | Ox86_SHLD sz => ok (SHLD_desc sz)
  | Ox86_VMOVDQU => ok VMOVDQU_desc
  | Ox86_VPXOR => ok VPXOR_desc
  end.

Lemma sopn_desc_name ii o d : sopn_desc ii o = ok d -> d.(id_name) = o.
Proof.
  by case: o => //=; (move => w h || move => h); have <- := ok_inj h.
Qed.

(* ----------------------------------------------------------------------------- *)
Definition assemble_sopn (ii: instr_info) (out: lvals) (op: sopn) (args: pexprs) : ciexec asm :=
  Let d := sopn_desc ii op in
  Let hiargs := compile_hi_sopn ii d out args in
  Let loargs := compile_low_args ii (id_tys d) hiargs in
  typed_apply_gargs ii loargs (id_instr d).

Lemma type_apply_gargP ty T ii ga (iasm:interp_ty ty → T) ins: 
   typed_apply_garg ii ga iasm = ok ins ->
   ∃ x' : interp_ty ty, ga = mk_garg x' ∧ ins = iasm x'. 
Proof.
  case: ty iasm => //=; case: ga => //.
  + by move => c i' [<-]; eauto.
  + by move => o i' [<-]; eauto.
  + by case => // r i' [<-]; eauto.
  + case => // a i' [<-].
    + by exists (Imm_ir a).
    by exists (Reg_ir a).
  case => // s w i'; t_xrbindP => z h <-; eexists; split; last reflexivity; repeat f_equal.
  move: h; rewrite /check_immediate. case: eqP => // <- [<-] {z}.
  by rewrite sign_zero_sign_extend.
  + by case => x f [<-]; eauto.
Qed.

Lemma assemble_sopn_is_sopn ii out op args i :
  assemble_sopn ii out op args = ok i →
  is_sopn i.
Proof.
  rewrite /assemble_sopn.
  t_xrbindP => id _ iargs _ gargs _. 
  have := id_gen_sem id; move: [::].
  elim: (id_tys id) (id_in id) (id_out id) (id_instr id) gargs =>
     [ | ty tys ih] /= iin iout iasm [ | ga gargs] //= gargs'. 
  + by move=> [? ?] [<-].
  move=> hgen;t_xrbindP => ins Ha.
  apply (ih iin iout ins gargs (gargs' ++ [::ga])).
  by have [x' [-> ->]]:= type_apply_gargP Ha.
Qed.

Lemma lom_eqv_mem_equiv_trans s m1 m2 :
  lom_eqv s m1 →
  x86_mem_equiv m1 m2 →
  lom_eqv s m2.
Proof.
case: m1 m2 => m1 rg1 xr1 rf1 [] m2 rg2 xr2 rf2 [] /= ? hrg1 hrx1 hrf1 [] /= <- <- <- hrf2.
constructor => //= f v hv.
move: (hrf1 f v hv) (hrf2 f) => {hv}.
case: (rf1 _) v => [ b | ] [] //=.
- by move => ? <- /eqP ->.
- by move => ? -> /eqP ->.
by move => ? -> _; case: (rf2 _).
Qed.

Theorem assemble_sopnP gd ii out op args i s1 m1 s2 :
  lom_eqv s1 m1 →
  assemble_sopn ii out op args = ok i →
  sem_sopn gd op s1 out args = ok s2 →
  ∃ m2,
    eval_instr_mem gd i m1 = ok m2
    ∧ lom_eqv s2 m2.
Proof.
  rewrite /assemble_sopn.
  t_xrbindP => eqm id hid hiargs ok_hi loargs ok_lo ok_i h.
  have hm := compile_hi_sopnP (sopn_desc_name hid) ok_hi h.
  have [m2 [ok_m2 hm2]] := mixed_to_low eqm ok_lo hm.
  suff : ∃ m0, eval_instr_mem gd i m1 = ok m0 ∧ x86_mem_equiv m2 m0.
  - case => m0 [hm0 eqm0].
    exists m0; split => //; exact: (lom_eqv_mem_equiv_trans hm2 eqm0).
  have := id_gen_sem id.
  move: ok_m2 => {h hid op ok_hi ok_lo eqm s1 s2 hm hm2}; rewrite /low_sem.
  rewrite -(cat0s loargs); move: [::] loargs ok_i.
  elim: (id_tys id) (id_in id) (id_out id) (id_name id) (id_instr id).
  - move => ins outs op i'.
    by move => acc [] // - [->] {i'} /=; rewrite cats0 => h [] _ /(_ gd m1 m2 h).
  move => ty tys ih ins outs op i' acc [] // g loargs /=; t_xrbindP => x ok_x hi /= h.
  have := ih ins outs op _ (acc ++ [:: g]) loargs hi.
  rewrite -catA => /(_ h) rec x0; apply: rec.
  by have [x' [-> ->]]:= type_apply_gargP ok_x.
Qed.
