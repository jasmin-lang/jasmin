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
- by rewrite /get_global => g; case: get_global_value => // z /ok_word_inj [??];subst.
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
Lemma MOVSX_gsc sz sz' :
  gen_sem_correct [:: TYreg; TYoprd] (Ox86_MOVSX sz sz') [:: E sz 0] [:: E sz' 1] [::] (MOVSX sz sz').
Proof.
move => /= x y; split => // gd m m'.
rewrite /low_sem_aux /= arg_of_oprdE /= /sets_low /eval_MOVSX /x86_MOVSX.
t_xrbindP => ??? h <-; t_xrbindP => w' /of_val_word [szw] [w] [hle ??] ? -> <- [<-] /=; subst.
rewrite (eval_low_read _ h) //=.
eexists; split; reflexivity.
Qed.

Definition MOVSX_desc sz sz' := make_instr_desc (MOVSX_gsc sz sz').

(* ----------------------------------------------------------------------------- *)
Lemma MOVZX_gsc sz sz' :
  gen_sem_correct [:: TYreg; TYoprd] (Ox86_MOVZX sz sz') [:: E sz 0] [:: E sz' 1] [::] (MOVZX sz sz').
Proof.
move => /= x y; split => // gd m m'.
rewrite /low_sem_aux /= arg_of_oprdE /= /sets_low /eval_MOVZX /x86_MOVZX.
t_xrbindP => ??? h <-; t_xrbindP => w' /of_val_word [szw] [w] [hle ??] ? -> <- [<-] /=; subst.
rewrite (eval_low_read _ h) //=.
eexists; split; reflexivity.
Qed.

Definition MOVZX_desc sz sz' := make_instr_desc (MOVZX_gsc sz sz').

Lemma MOVZX32_gsc :
  gen_sem_correct [:: TYreg; TYoprd ] Ox86_MOVZX32
    [:: E U32 0 ] [:: E U32 1 ] [::] (λ d, MOV U32 (Reg_op d)).
Proof.
move => x y; split => // gd m m'.
rewrite /low_sem_aux /= arg_of_oprdE /=.
t_xrbindP => ??? h <-; t_xrbindP => ? /to_wordI [szw] [w] [hle ??];
subst => <- /= [<-].
rewrite /eval_MOV /= /eval_MOV_nocheck (eval_low_read _ h) //=.
eexists; split; first reflexivity.
split. 1, 3, 4: reflexivity.
by rewrite /= /word_extend_reg /merge_word zero_extend_u.
Qed.

Definition MOVZX32_desc := make_instr_desc MOVZX32_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma MOVD_gsc sz :
  gen_sem_correct' [:: TYxreg ; TYoprd ] MSB_MERGE (Ox86_MOVD sz)
                  [:: E U128 0 ] [:: E sz 1 ] [::] (MOVD sz).
Proof.
move => x y; split => // gd m m'.
rewrite /low_sem_aux /= arg_of_oprdE /= /sets_low /eval_MOVD /x86_movd.
t_xrbindP => ??? h <-; t_xrbindP => w' /of_val_word [szw] [w] [hle ??] _ -> <- /= [<-]; subst.
rewrite (eval_low_read _ h) //=.
eexists; split; reflexivity.
Qed.

Definition MOVD_desc sz := make_instr_desc (MOVD_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma VMOVDQU_gsc sz :
  gen_sem_correct [:: TYrm128; TYrm128] (Ox86_VMOVDQU sz) [:: E sz 0] [:: E sz 1] [::] (VMOVDQU sz).
Proof.
move => /= x y; split => // gd m m'.
rewrite /low_sem_aux /=.
case: y => [ y | y | y ]; rewrite /low_sem_aux /sets_low /eval_VMOV /read_rm128 /=.
+ case: x => //= x; t_xrbindP => ? ? /truncate_wordP [_] <- ? -> <- /=;
  [ case | rewrite truncate_word_u ] => /= ->;
  eexists; split; reflexivity.
+ case: x => //= x; t_xrbindP => ???? h <- <- /=; rewrite truncate_word_u /= h;
  t_xrbindP => _ -> /= <- /=;
  [ case | rewrite truncate_word_u ] => /= ->;
  eexists; split; reflexivity.
case: eqP => // - [<-]{sz}.
case: x => //= x; t_xrbindP => ??? /get_globalI /= [w];rewrite /get_global => -> -> /= <- /=;
rewrite truncate_word_u /= eq_dec_refl; t_xrbindP => _ -> /= <- /=;
[ case | rewrite truncate_word_u ] => /= ->;
eexists; split; reflexivity.
Qed.

Definition VMOVDQU_desc sz := make_instr_desc (VMOVDQU_gsc sz).

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
case: x => //= [x | x]; t_xrbindP => vs ?? hb ?? hv ; [ | move => ??? hm <- <- ] => <- <- /= ; t_xrbindP => _ -> /=;
move => vb /to_boolI => ? ; subst => h2 /to_wordI [x0] [x1] [] ??? ; subst => h4 /truncate_wordP [] ?? ; subst;
have hb' := value_of_boolI hb;
rewrite hb' => {hb}.
+ by case: vb hb' => hb' [] <- //=; [rewrite (eval_low_read _ hv) //= |];
  rewrite /sets_low /= => -[<-] ; eexists ; split ; reflexivity.
case: vb hb' => hb' [] <- //=; [rewrite (eval_low_read _ hv) //= |].
+ by rewrite /sets_low /= truncate_word_u /= => ? ; eexists ; split ; eauto ; reflexivity.
by rewrite /sets_low /= truncate_word_u /= zero_extend_u hm /= ; eexists ; split ; eauto; reflexivity.
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
  rewrite /= /low_sem_aux /= /eval_MUL /x86_mul => x; split => // gd m m'.
  rewrite arg_of_oprdE /=; t_xrbindP => vs ? ? vx ok_vx <- <- /=; t_xrbindP => wa /truncate_wordP [ha ->] {wa}.
  move => wx /of_val_word [sx] [?] [hx ??]; subst => /= _ -> /= <- [<-]; rewrite (eval_low_read _ ok_vx) {ok_vx} //; update_set.
Qed.

Definition MUL_desc sz := make_instr_desc (MUL_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma IMUL_gsc sz :
  gen_sem_correct [:: TYoprd ] (Ox86_IMUL sz) (implicit_flags ++ [:: R RDX; R RAX])
                   [:: R RAX; E sz 0] [::] (λ x, IMUL sz x None).
Proof.
  rewrite /= /low_sem_aux /= /eval_IMUL /x86_imul => x; split => // gd m m'.
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
  rewrite /= /low_sem_aux /= /eval_IMUL /x86_imult => x; split => // gd m m'.
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
  rewrite /= /low_sem_aux /= /eval_IMUL /x86_imult => x; split => // gd m m'.
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
  rewrite /= /low_sem_aux /= /eval_DIV /x86_div => x; split => // gd m m'.
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
  rewrite /= /low_sem_aux /= /eval_IDIV /x86_idiv => x; split => // gd m m'.
  rewrite arg_of_oprdE /=; t_xrbindP => vs ???? hx <- <- <- /=.
  apply: rbindP => ? /truncate_wordP [hle <-].
  rewrite /truncate_word hle /=; t_xrbindP => ? /of_val_word [?][?][hle' ??]; subst => _ -> /=.
  rewrite (eval_low_read _ hx) //=; case: ifP => // _ [<-] [<-].
  update_set.
Qed.

Definition IDIV_desc sz := make_instr_desc (IDIV_gsc sz).


(* ----------------------------------------------------------------------------- *)
Lemma CQO_gsc sz :
  gen_sem_correct [::] (Ox86_CQO sz) [:: R RDX] [:: R RAX] [::] (CQO sz).
Proof.
  rewrite /= /low_sem_aux /= /eval_CQO /x86_cqo; split => // gd m m'.
   t_xrbindP => vs ? /truncate_wordP [ ? -> ] _ -> <- /= [<-].
   eexists;split;reflexivity.
Qed.

Definition CQO_desc sz := make_instr_desc (CQO_gsc sz).

(* ----------------------------------------------------------------------------- *)
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
Lemma ANDN_gsc sz :
  gen_sem_correct [:: TYreg; TYreg; TYoprd] (Ox86_ANDN sz)
     (implicit_flags ++ [:: E sz 0])
     [:: E sz 1; E sz 2] [::] (ANDN sz).
Proof.
move => dst x y; split => // gd m m'; rewrite /low_sem_aux /= !arg_of_oprdE /= /x86_andn /eval_ANDN.
case: y => [ y | y | y | y ] /=.
1,3: t_xrbindP => ?? /truncate_wordP [hle] -> ? /truncate_wordP [hle'] -> _ -> /= <- [<-]; update_set.
- t_xrbindP => ???? -> <- <- /=.
  t_xrbindP => ? /truncate_wordP [hle] -> ? /to_wordI [sz'] [w'] [hle' -> ->] _ -> /= <- [<-]; update_set.
t_xrbindP => ????? h <- <- <- /=.
t_xrbindP => ? /truncate_wordP [hle] -> ?; rewrite truncate_word_u h => - [<-] _ -> /= <- [<-]; update_set.
Qed.

Definition ANDN_desc sz := make_instr_desc (ANDN_gsc sz).

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
     [:: E sz 0; E sz 1; ADExplicit (Some U8) 2 (Some RCX)] [::] (SHLD sz).
Proof.
move => x y z; split => // gd m m'.
rewrite /low_sem_aux /= !arg_of_oprdE /= /x86_shld /eval_SHLD.
case: z => // [ z | z ].
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

(* Duplicate of the above *)
rewrite /=; case: eqP => // ?; subst z.
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
Lemma SHRD_gsc sz :
  gen_sem_correct [:: TYoprd; TYreg; TYireg] (Ox86_SHRD sz)
     (implicit_flags ++ [:: E sz 0])
     [:: E sz 0; E sz 1; ADExplicit (Some U8) 2 (Some RCX)] [::] (SHRD sz).
Proof.
move => x y z; split => // gd m m'.
rewrite /low_sem_aux /= !arg_of_oprdE /= /x86_shrd /eval_SHRD.
case: z => // [ z | z ].
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

(* Duplicate of the above *)
rewrite /=; case: eqP => // ?; subst z.
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

Definition SHRD_desc sz := make_instr_desc (SHRD_gsc sz).

(* ----------------------------------------------------------------------------- *)
Definition SET0 sz o : asm :=
  XOR
    (if o is Reg_op _
     then cmp_min U32 sz
     else sz)
    o o.

Lemma Set0_gsc sz :
  gen_sem_correct [:: TYoprd] (Oset0 sz)
     (implicit_flags ++ [:: E sz 0])
     [::] [::] (SET0 sz).
Proof.
move => x; split => // gd m m'; rewrite /low_sem_aux /= /eval_XOR.
have ok_sz : ∀ u, check_size_8_64 sz = ok u → check_size_8_64 (if x is Reg_op _ then cmp_min U32 sz else sz) = ok tt.
+ by case: x => //; case: sz.
case: x ok_sz => //= [ x | x ] ok_sz; t_xrbindP => vs _ /(ok_sz) {ok_sz} -> /= <-.
- case => <- /=; rewrite wxor_xx /= /rflags_of_bwop /SF_of_word msb0 /=.
  know_it; f_equal; rewrite /mem_write_reg /=; f_equal; last first.
  * by apply /ffunP; case; rewrite !ffunE.
  by rewrite /word_extend_reg /=; f_equal; case: sz.
rewrite /sets_low /= truncate_word_u /= /mem_write_mem /= !decode_addr_set_rflags.
apply: rbindP => m'' hw [<-].
have [o ->] := write_mem_can_read hw.
rewrite /= wxor_xx decode_addr_update_rflags /= hw /= /rflags_of_bwop /SF_of_word msb0; update_set.
Qed.

Definition Set0_desc sz := make_instr_desc (Set0_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma BSWAP_gsc sz :
  gen_sem_correct [:: TYreg ] (Ox86_BSWAP sz)
     [:: E sz 0] [:: E sz 0] [::] (BSWAP sz).
Proof.
move => x; split => // gd m m'; rewrite /low_sem_aux /= /eval_BSWAP /x86_bswap.
t_xrbindP => _ _ /truncate_wordP [hle ->] _ -> /= <- [<-].
eexists; split; reflexivity.
Qed.

Definition BSWAP_desc sz := make_instr_desc (BSWAP_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma eval_low_rm128_nocheck gd s m x y sz (v: word sz) :
  arg_of_rm128 (Some s) x = Some y →
  eval_low gd m y = ok (Vword v) →
  read_rm128_nocheck gd s x m = ok (zero_extend _ v).
Proof.
  case: x => [ r | a | g ] /=.
  1-2: case => <- {y} /=.
  2: apply: rbindP => ??.
  1-2: by move => /ok_word_inj [?]; subst => /= <-; rewrite /read_rm128_nocheck /= ?zero_extend_u.
  case: eqP => // - [<-] {s} [<-] {y} /= h; rewrite h /=.
  case/get_globalI: h => w h /Vword_inj [?]; subst => /= -> {v}.
  by rewrite eq_dec_refl zero_extend_u.
Qed.

Lemma eval_low_rm128 gd s u m x y sz (v: word sz) :
  check_size_128_256 s = ok u →
  arg_of_rm128 (Some s) x = Some y →
  eval_low gd m y = ok (Vword v) →
  read_rm128 gd s x m = ok (zero_extend _ v).
Proof.
  move => ok_s ok_y ok_v.
  rewrite /read_rm128 ok_s /=.
  exact: (eval_low_rm128_nocheck ok_y ok_v).
Qed.

(* ----------------------------------------------------------------------------- *)
Lemma x86_rm128_binop_gsc sz op i sem :
  (∀ d x y, is_sopn (i sz d x y)) →
  (exec_sopn (op sz) = app_ww sz (@x86_u128_binop sz sem)) →
  (∀ d x y gd m, eval_instr_mem gd (i sz d x y) m = eval_rm128_binop gd MSB_CLEAR sem d x y m) →
  gen_sem_correct [:: TYrm128 ; TYrm128 ; TYrm128 ] (op sz)
                  [:: E sz 0 ] [:: E sz 1 ; E sz 2 ] [::] (i sz).
Proof.
move => ok_sopn hsem lsem d x y; split => // gd m m'.
rewrite /low_sem_aux /= lsem /eval_rm128_binop hsem /x86_u128_binop /=.
case hx: (arg_of_rm128 _ x) => [ x' | ] //.
case hy: (arg_of_rm128 _ y) => [ y' | ] //=.
case: d => d //; t_xrbindP => ??? hx' ?? hy' ??; subst;
t_xrbindP => vx /to_wordI [szx] [wx] [hlex ??];
subst => vy /to_wordI [szy] [wy] [hley ??] ? ok_s ?; subst;
rewrite /sets_low /=;
rewrite (eval_low_rm128 ok_s hx hx') (eval_low_rm128 ok_s hy hy') /=;
[ case | rewrite truncate_word_u /= ];
move => ->; eexists; split; reflexivity.
Qed.

Arguments x86_rm128_binop_gsc : clear implicits.

Definition VPAND_desc sz := make_instr_desc
    (x86_rm128_binop_gsc sz Ox86_VPAND VPAND wand
    (λ d x y, erefl) erefl (λ d x y gd m, erefl)).

Definition VPOR_desc sz := make_instr_desc
    (x86_rm128_binop_gsc sz Ox86_VPOR VPOR wor
    (λ d x y, erefl) erefl (λ d x y gd m, erefl)).

Definition VPXOR_desc sz := make_instr_desc
    (x86_rm128_binop_gsc sz Ox86_VPXOR VPXOR wxor
    (λ d x y, erefl) erefl (λ d x y gd m, erefl)).

Definition VPADD_desc ve sz := make_instr_desc
    (x86_rm128_binop_gsc sz (Ox86_VPADD ve) (VPADD ve) (lift2_vec ve +%R sz)
    (λ d x y, erefl) erefl (λ d x y gd m, erefl)).

Definition VPSUB_desc ve sz := make_instr_desc
    (x86_rm128_binop_gsc sz (Ox86_VPSUB ve) (VPSUB ve) (lift2_vec ve (fun x y => x - y)%R sz)
    (λ d x y, erefl) erefl (λ d x y gd m, erefl)).

(* ----------------------------------------------------------------------------- *)
Lemma VPMULL_gsc ve sz: 
   gen_sem_correct [:: TYrm128 ; TYrm128 ; TYrm128 ] (Ox86_VPMULL ve sz)
                   [:: E sz 0 ] [:: E sz 1 ; E sz 2 ] [::] (VPMULL ve sz).
Proof.
  move=> d x y;split => // gd m m'.
  rewrite /low_sem_aux /= /x86_vpmull /eval_VPMULL /= /x86_u128_binop /= /eval_rm128_binop.
  case hx: (arg_of_rm128 _ x) => [ x' | ] //.
  case hy: (arg_of_rm128 _ y) => [ y' | ] //=.
  case: d => d //; t_xrbindP => ??? hx' ?? hy' ??; subst;
  t_xrbindP => vx /to_wordI [szx] [wx] [hlex ??];
  subst => vy /to_wordI [szy] [wy] [hley ??] ? -> ? ok_s ?; subst;
  rewrite /sets_low /= (eval_low_rm128 ok_s hx hx') (eval_low_rm128 ok_s hy hy') /=;
  [ case | rewrite truncate_word_u /= ];
  move => ->; eexists; split; reflexivity.
Qed.

Definition VPMULL_desc ve sz := make_instr_desc (VPMULL_gsc ve sz).

(* ----------------------------------------------------------------------------- *)
Lemma VPEXTR_gsc ve :
  gen_sem_correct [:: TYoprd ; TYxreg ; TYimm U8 ] (Ox86_VPEXTR ve)
      [:: E ve 0 ] [:: E U128 1 ; E U8 2 ] [::] (VPEXTR ve).
Proof.
move => x y z; split => // gd m m'.
rewrite /low_sem_aux /= /x86_vpextr /eval_VPEXTR.
case: x => //= [ x | x ]; t_xrbindP => ?? hve <-; rewrite /sets_low /=;
[ case | rewrite truncate_word_u/= ];
rewrite zero_extend_sign_extend // sign_extend_u.
+ move => <-; eexists; split; first reflexivity.
  split; try reflexivity.
  rewrite /=; f_equal; rewrite /mem_write_reg /word_extend_reg /merge_word zero_extend_u.
  by case: ve hve.
move => ->; eexists; split; reflexivity.
Qed.

Definition VPEXTR_desc ve := make_instr_desc (VPEXTR_gsc ve).

(* ----------------------------------------------------------------------------- *)
Definition VPINSR_gsc ve :
  gen_sem_correct [:: TYxreg ; TYxreg ; TYoprd ; TYimm U8 ]
    (Ox86_VPINSR ve)
    [:: E U128 0 ] [:: E U128 1 ; E ve 2 ; E U8 3 ] [::]
    (VPINSR ve).
Proof.
move => d x y i; split => // gd m m'.
rewrite /low_sem_aux/= arg_of_oprdE /= /x86_vpinsr /eval_VPINSR.
t_xrbindP => ???? h <- <- /=; t_xrbindP => w' /to_wordI [sz'] [w] [hle ??].
subst => <- [<-].
rewrite (eval_low_read hle h) /= zero_extend_sign_extend // sign_extend_u.
update_set.
Qed.

Definition VPINSR_desc ve := make_instr_desc (VPINSR_gsc ve).

(* ----------------------------------------------------------------------------- *)
Lemma x86_rm128_shift_gsc ve sz op i sem :
  (∀ d x y, is_sopn (i sz d x y)) →
  (exec_sopn (op sz) = app_w8 sz (x86_u128_shift ve sz sem)) →
  (∀ d x y gd m, eval_instr_mem gd (i sz d x y) m = eval_rm128_shift gd MSB_CLEAR sz sem d x y m) →
  gen_sem_correct [:: TYrm128 ; TYrm128 ; TYimm U8 ] (op sz)
                  [:: E sz 0 ] [:: E sz 1 ; E U8 2 ] [::] (i sz).
Proof.
move => ok_sopn hsem lsem d x y; split => // gd m m'.
rewrite /low_sem_aux /= lsem /eval_rm128_shift hsem /x86_u128_shift /=.
case hx: arg_of_rm128 => [ x' | ] //.
case: d => d //=;
t_xrbindP => ??? hx' ?; subst;
t_xrbindP => vx /to_wordI [szx] [wx] [hlex ??];
subst => _ [<-] _ -> /= ? ok_s <-;
rewrite zero_extend_sign_extend // sign_extend_u (eval_low_rm128 ok_s hx hx') /sets_low /= => {hx};
[ case | rewrite truncate_word_u /= ] => ->;
eexists; split; reflexivity.
Qed.

Arguments x86_rm128_shift_gsc : clear implicits.

Definition VPSLL_desc (ve: velem) sz := make_instr_desc (x86_rm128_shift_gsc ve sz (Ox86_VPSLL ve) (VPSLL ve) _ (λ d x y, erefl) erefl (λ d x y gd m, erefl)).
Definition VPSRL_desc (ve: velem) sz := make_instr_desc (x86_rm128_shift_gsc ve sz (Ox86_VPSRL ve) (VPSRL ve) _ (λ d x y, erefl) erefl (λ d x y gd m, erefl)).

Definition VPSRA_desc (ve: velem) sz := make_instr_desc (x86_rm128_shift_gsc ve sz (Ox86_VPSRA ve) (VPSRA ve) _ (λ d x y, erefl) erefl (λ d x y gd m, erefl)).

(* ----------------------------------------------------------------------------- *)
Lemma x86_rm128_shift_variable_gsc ve sz op i sem :
  (∀ d x y, is_sopn (i sz d x y)) →
  (exec_sopn (op sz) = app_ww sz (x86_u128_shift_variable ve sz sem)) →
  (∀ d x y gd m, eval_instr_mem gd (i sz d x y) m = eval_rm128_shift_variable gd sz sem d x y m) →
  gen_sem_correct [:: TYxreg ; TYxreg ; TYrm128 ] (op sz)
                  [:: E sz 0 ] [:: E sz 1 ; E sz 2 ] [::] (i sz).
Proof.
move => ok_sopn hsem lsem d x y; split => // gd m m'.
rewrite /low_sem_aux /= lsem /eval_rm128_shift_variable hsem /x86_u128_shift_variable /=.
case hy: arg_of_rm128 => [ y' | ] //=.
t_xrbindP => ???? hy' <- <- /=.
rewrite /truncate_word wsize_le_U256 /=; t_xrbindP => w /to_wordI [sz'] [w'] [hle ??].
subst => _ -> /= ? ok_sz <- [<-].
rewrite /eval_xmm_binop (eval_low_rm128 ok_sz hy hy').
eexists; split; reflexivity.
Qed.

Arguments x86_rm128_shift_variable_gsc : clear implicits.

Definition VPSLLV_desc (ve: velem) sz := make_instr_desc (x86_rm128_shift_variable_gsc ve sz (Ox86_VPSLLV ve) (VPSLLV ve) _ (λ d x y, erefl) erefl (λ d x y gd m, erefl)).
Definition VPSRLV_desc (ve: velem) sz := make_instr_desc (x86_rm128_shift_variable_gsc ve sz (Ox86_VPSRLV ve) (VPSRLV ve) _ (λ d x y, erefl) erefl (λ d x y gd m, erefl)).

(* ----------------------------------------------------------------------------- *)
Lemma x86_shift_double_quadword_gsc sz op i sem :
  (∀ d x y, is_sopn (i sz d x y)) →
  (exec_sopn (op sz) = app_w8 sz (x86_vpsxldq sem)) →
  (∀ d x y gd m, eval_instr_mem gd (i sz d x y) m = eval_shift_double_quadword sem d x y m) →
  gen_sem_correct [:: TYxreg ; TYxreg ; TYimm U8 ] (op sz)
                  [:: E sz 0 ] [:: E sz 1 ; E sz 2 ] [::] (i sz).
Proof.
move => ok_sopn hsem lsem d x y; split => // gd m m'.
rewrite /low_sem_aux /= lsem /eval_shift_double_quadword hsem /x86_vpsxldq /=.
t_xrbindP => ?? /truncate_wordP [_ ->] ? ok_sz /= <- [<-].
rewrite ok_sz /=; know_it; do 3 f_equal.
by rewrite zero_extend_sign_extend // sign_extend_u.
Qed.

Arguments x86_shift_double_quadword_gsc : clear implicits.

Definition VPSLLDQ_desc sz := make_instr_desc (x86_shift_double_quadword_gsc sz Ox86_VPSLLDQ VPSLLDQ _ (λ d x y, erefl) erefl (λ d x y gd m, erefl)).
Definition VPSRLDQ_desc sz := make_instr_desc (x86_shift_double_quadword_gsc sz Ox86_VPSRLDQ VPSRLDQ _ (λ d x y, erefl) erefl (λ d x y gd m, erefl)).

(* ----------------------------------------------------------------------------- *)
Lemma x86_xmm_binop_gsc sz op i sem :
  (∀ d x y, is_sopn (i sz d x y)) →
  (exec_sopn (op sz) = app_ww sz (@x86_u128_binop sz sem)) →
  (∀ d x y gd m, eval_instr_mem gd (i sz d x y) m = eval_xmm_binop gd sem d x y m) →
  gen_sem_correct [:: TYxreg ; TYxreg ; TYrm128 ] (op sz)
                  [:: E sz 0 ] [:: E sz 1 ; E sz 2 ] [::] (i sz).
Proof.
move => ok_sopn hsem lsem d x y; split => // gd m m'.
rewrite /low_sem_aux /= lsem /eval_xmm_binop hsem /x86_u128_binop /=.
case hy: (arg_of_rm128 _ y) => [ y' | ] //=.
t_xrbindP => ???? h <- <- /=; rewrite /truncate_word wsize_le_U256 /=.
t_xrbindP => w /to_wordI [sz'] [w'] [hle ??].
subst => ? ok_sz <- [<-].
rewrite (eval_low_rm128 ok_sz hy h).
eexists; split; reflexivity.
Qed.

Arguments x86_xmm_binop_gsc : clear implicits.

Definition VPMULU_desc sz := make_instr_desc (x86_xmm_binop_gsc sz Ox86_VPMULU VPMULU _ (λ d x y, erefl) erefl (λ d x y gd m, erefl)).
Definition VPANDN_desc sz := make_instr_desc (x86_xmm_binop_gsc sz Ox86_VPANDN VPANDN _ (λ d x y, erefl) erefl (λ d x y gd m, erefl)).
Definition VPSHUFB_desc sz := make_instr_desc (x86_xmm_binop_gsc sz Ox86_VPSHUFB VPSHUFB _ (λ d x y, erefl) erefl (λ d x y gd m, erefl)).

(* ----------------------------------------------------------------------------- *)
Lemma vpshuf_gsc sz op i sem :
  (∀ d x y, is_sopn (i sz d x y)) →
  (exec_sopn (op sz) = app_w8 sz (x86_vpshuf sz sem)) →
  (∀ d x y gd m, eval_instr_mem gd (i sz d x y) m = eval_vpshuf gd sem d x y m) →
  gen_sem_correct [:: TYxreg ; TYrm128 ; TYimm U8 ]
    (op sz) [:: E sz 0 ] [:: E sz 1 ; E U8 2 ] [::]
    (i sz).
Proof.
move => ok_sopn hsem lsem x y z; split => // gd m m'.
rewrite /low_sem_aux /= lsem /eval_vpshuf hsem /x86_vpshuf /=.
case hz: arg_of_rm128 => [ z' | ] //=.
t_xrbindP => ??? h <-; t_xrbindP => w /to_wordI [sz'] [w'] [hle ??].
subst => _ [<-].
t_xrbindP => ? ok_sz <-.
rewrite /sets_low => - [<-].
rewrite (eval_low_rm128 ok_sz hz h).
eexists; split; first reflexivity.
by rewrite zero_extend_sign_extend // sign_extend_u; reflexivity.
Qed.

Arguments vpshuf_gsc : clear implicits.

Definition VPSHUFHW_desc sz := make_instr_desc (vpshuf_gsc sz Ox86_VPSHUFHW VPSHUFHW _ (λ d x y, erefl) erefl (λ d x y gd m, erefl)).
Definition VPSHUFLW_desc sz := make_instr_desc (vpshuf_gsc sz Ox86_VPSHUFLW VPSHUFLW _ (λ d x y, erefl) erefl (λ d x y gd m, erefl)).
Definition VPSHUFD_desc sz := make_instr_desc (vpshuf_gsc sz Ox86_VPSHUFD VPSHUFD _ (λ d x y, erefl) erefl (λ d x y gd m, erefl)).

(* ----------------------------------------------------------------------------- *)
Lemma vpunpck_gsc (ve: velem) sz op i sem :
  (∀ d x y, is_sopn (i ve sz d x y)) →
  (exec_sopn (op ve sz) = app_ww sz (x86_u128_binop sem)) →
  (∀ d x y gd m, eval_instr_mem gd (i ve sz d x y) m = eval_vpunpck gd sem d x y m) →
  gen_sem_correct [:: TYxreg ; TYxreg ; TYrm128 ]
    (op ve sz) [:: E sz 0 ] [:: E sz 1 ; E sz 2 ] [::] (i ve sz).
Proof.
move => ok_sopn hsem lsem x y z; split => // gd m m'.
rewrite /low_sem_aux /= lsem /eval_vpunpck hsem /x86_u128_binop /=.
case hz: arg_of_rm128 => [ z' | ] //=.
t_xrbindP => ???? h <- <- /=; rewrite /truncate_word wsize_le_U256 /=.
t_xrbindP => w /to_wordI [sz'] [w'] [hle ??].
subst => ? ok_sz <-.
rewrite /sets_low => - [<-].
rewrite (eval_low_rm128 ok_sz hz h).
eexists; split; reflexivity.
Qed.

Arguments vpunpck_gsc : clear implicits.

Definition VPUNPCKH_desc ve sz := make_instr_desc (vpunpck_gsc ve sz Ox86_VPUNPCKH VPUNPCKH _ (λ d x y, erefl) erefl (λ d x y gd m, erefl)).
Definition VPUNPCKL_desc ve sz := make_instr_desc (vpunpck_gsc ve sz Ox86_VPUNPCKL VPUNPCKL _ (λ d x y, erefl) erefl (λ d x y gd m, erefl)).

(* ----------------------------------------------------------------------------- *)
Lemma VPBLENDD_gsc sz :
  gen_sem_correct [:: TYxreg ; TYxreg ; TYrm128 ; TYimm U8 ]
    (Ox86_VPBLENDD sz)
    [:: E sz 0 ] [:: E sz 1 ; E sz 2 ; E U8 3 ] [::]
    (VPBLENDD sz).
Proof.
move => x y z k; split => // gd m m'.
rewrite /low_sem_aux /=.
case hz: arg_of_rm128 => [ z' | ] //=.
t_xrbindP => ???? h <- <-; t_xrbindP => w1 /to_wordI [sz1] [w1'] [_ /Vword_inj [?]].
subst => /= ??; subst => w1 /to_wordI [sz1] [w1'] [hle ??]; subst => ?.
rewrite /truncate_word /= zero_extend_sign_extend // sign_extend_u => - [?]; subst.
rewrite /x86_vpblendd; t_xrbindP => ? ok_sz <-.
rewrite /sets_low => - [<-].
rewrite /eval_VPBLENDD (eval_low_rm128 ok_sz hz h).
eexists; split; reflexivity.
Qed.

Definition VPBLENDD_desc sz := make_instr_desc (VPBLENDD_gsc sz).

(* ----------------------------------------------------------------------------- *)
Lemma VPBROADCAST_gsc ve sz :
  gen_sem_correct [:: TYxreg ; TYrm128 ]
    (Ox86_VPBROADCAST ve sz)
    [:: E sz 0 ] [:: E ve 1 ] [::]
    (VPBROADCAST ve sz).
Proof.
move => x y; split => // gd m m'.
rewrite /low_sem_aux /=.
case hy: arg_of_rm128 => [ y' | ] //=.
t_xrbindP => ??? h <-; t_xrbindP => w' /to_wordI [sz'] [w] [hle ??]; subst.
rewrite /x86_vpbroadcast /eval_VPBROADCAST.
t_xrbindP => _ -> /= <- [<-].
rewrite (eval_low_rm128_nocheck hy h).
eexists; split; reflexivity.
Qed.

Definition VPBROADCAST_desc ve sz := make_instr_desc (VPBROADCAST_gsc ve sz).

Lemma VBROADCASTI128_gsc :
  gen_sem_correct [:: TYxreg ; TYm128 ]
    Ox86_VBROADCASTI128
    [:: E U256 0 ] [:: E U128 1 ] [::]
    VBROADCASTI128.
Proof.
move => x y; split => // gd m m'.
rewrite /low_sem_aux /=.
case hy: arg_of_rm128 => [ y' | ] //=.
t_xrbindP => ??? h <-; t_xrbindP => w' /to_wordI [sz'] [w] [hle ??]; subst.
rewrite /x86_vpbroadcast /eval_VBROADCASTI128 /eval_VPBROADCAST => - [<-] [<-].
rewrite (eval_low_rm128_nocheck hy h).
eexists; split; reflexivity.
Qed.

Definition VBROADCASTI128_desc := make_instr_desc VBROADCASTI128_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma VEXTRACTI128_gsc :
  gen_sem_correct [:: TYrm128 ; TYxreg ; TYimm U8 ]
    Ox86_VEXTRACTI128
    [:: E U128 0 ] [:: E U256 1 ; E U8 2 ] [::]
    VEXTRACTI128.
Proof.
move => x y z; split => // gd m m'.
rewrite /low_sem_aux /=.
rewrite zero_extend_u zero_extend_sign_extend //.
case: x => // [ x | x ]; [ case | ];
rewrite /sets_low /= sign_extend_u.
1: move => <-.
2: rewrite zero_extend_u => ->.
all: eexists; split; reflexivity.
Qed.

Definition VEXTRACTI128_desc := make_instr_desc VEXTRACTI128_gsc.

(* ----------------------------------------------------------------------------- *)
Lemma i128_terop_gsc sz op i sem :
  (check_size_128_256 sz = ok tt) →
  (∀ d x y n, is_sopn (i d x y n)) →
  (exec_sopn op = app_sopn [:: sword256 ; sword sz ; sword8 ] (λ x y n, ok [:: Vword (sem x y n)])) →
  (∀ d x y n gd m, eval_instr_mem gd (i d x y n) m = eval_i128_terop gd sem d x y n m) →
  gen_sem_correct [:: TYxreg ; TYxreg ; TYrm128 ; TYimm U8 ]
    op
    [:: E U256 0 ] [:: E U256 1 ; E sz 2 ; E U8 3 ] [::]
    i.
Proof.
move => ok_sz ok_sopn hsem lsem x y z k; split => // gd m m'.
rewrite /low_sem_aux /=.
case hz: arg_of_rm128 => [ z' | ] //=.
rewrite hsem lsem /=.
t_xrbindP => ???? h <- <-; t_xrbindP => w1 /to_wordI [sz1] [w1'] [_ /Vword_inj [?]].
subst => /= ??; subst => w1 /to_wordI [sz1] [w1'] [hle ??]; subst => ?.
rewrite /truncate_word /= zero_extend_sign_extend // sign_extend_u => - [?]; subst => <-.
rewrite /sets_low zero_extend_u => - [<-].
rewrite /eval_i128_terop (eval_low_rm128 ok_sz hz h).
eexists; split; reflexivity.
Qed.

Arguments i128_terop_gsc : clear implicits.

Definition VINSERTI128_desc := make_instr_desc (i128_terop_gsc U128 Ox86_VINSERTI128 VINSERTI128 winserti128 erefl (λ d x y n, erefl) erefl (λ d x y n gd m, erefl)).
Definition VPERM2I128_desc := make_instr_desc (i128_terop_gsc U256 Ox86_VPERM2I128 VPERM2I128 wperm2i128 erefl (λ d x y n, erefl) erefl (λ d x y n gd m, erefl)).

(* ----------------------------------------------------------------------------- *)
Lemma VPERMQ_gsc :
  gen_sem_correct [:: TYxreg ; TYrm128 ; TYimm U8 ]
    Ox86_VPERMQ [:: E U256 0 ] [:: E U256 1 ; E U8 2 ] [::] VPERMQ.
Proof.
move => dst src imm; split => // gd m m'.
rewrite /low_sem_aux /= /eval_VPERMQ /x86_vpermq /=.
case hsrc: arg_of_rm128 => [ src' | ] //=.
t_xrbindP => ??? h <-; t_xrbindP => w /to_wordI [sz'] [w'] [hle ??].
subst => _ [<-] <- [<-].
rewrite (eval_low_rm128 (erefl : check_size_128_256 U256 = ok tt) hsrc h) zero_extend_sign_extend // sign_extend_u.
eexists; split; reflexivity.
Qed.

Definition VPERMQ_desc := make_instr_desc VPERMQ_gsc.

(* ----------------------------------------------------------------------------- *)

Definition sopn_desc ii (c : sopn) : ciexec instr_desc :=
  match c with
  | Omulu _ | Oaddcarry _ | Osubcarry _ => cierror ii (Cerr_assembler (AsmErr_string "sopn_desc"))
  | Oset0 sz => ok (Set0_desc sz)
  | Ox86_MOV sz => ok (MOV_desc sz)
  | Ox86_MOVSX sz sz' => ok (MOVSX_desc sz sz')
  | Ox86_MOVZX sz sz' => ok (MOVZX_desc sz sz')
  | Ox86_MOVZX32 => ok MOVZX32_desc
  | Ox86_CMOVcc sz => ok (CMOVcc_desc sz)
  | Ox86_ADD sz => ok (ADD_desc sz)
  | Ox86_SUB sz => ok (SUB_desc sz)
  | Ox86_MUL sz => ok (MUL_desc sz)
  | Ox86_IMUL sz => ok (IMUL_desc sz)
  | Ox86_IMULt sz => ok (IMULt_desc sz)
  | Ox86_IMULtimm sz => ok (IMULtimm_desc sz)
  | Ox86_DIV sz => ok (DIV_desc sz)
  | Ox86_IDIV sz => ok (IDIV_desc sz)
  | Ox86_CQO sz => ok (CQO_desc sz)
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
  | Ox86_ANDN sz => ok (ANDN_desc sz)
  | Ox86_OR sz => ok (OR_desc sz)
  | Ox86_XOR sz => ok (XOR_desc sz)
  | Ox86_NOT sz => ok (NOT_desc sz)
  | Ox86_ROL sz => ok (ROL_desc sz)
  | Ox86_ROR sz => ok (ROR_desc sz)
  | Ox86_SHL sz => ok (SHL_desc sz)
  | Ox86_SHR sz => ok (SHR_desc sz)
  | Ox86_SAR sz => ok (SAR_desc sz)
  | Ox86_SHLD sz => ok (SHLD_desc sz)
  | Ox86_SHRD sz => ok (SHRD_desc sz)
  | Ox86_BSWAP sz => ok (BSWAP_desc sz)
  | Ox86_MOVD sz => ok (MOVD_desc sz)
  | Ox86_VMOVDQU sz => ok (VMOVDQU_desc sz)
  | Ox86_VPAND sz => ok (VPAND_desc sz)
  | Ox86_VPANDN sz => ok (VPANDN_desc sz)
  | Ox86_VPOR sz => ok (VPOR_desc sz)
  | Ox86_VPXOR sz => ok (VPXOR_desc sz)
  | Ox86_VPADD ve sz => ok (VPADD_desc ve sz)
  | Ox86_VPSUB ve sz => ok (VPSUB_desc ve sz)
  | Ox86_VPMULL ve sz => ok (VPMULL_desc ve sz)
  | Ox86_VPMULU sz => ok (VPMULU_desc sz)
  | Ox86_VPEXTR ve => ok (VPEXTR_desc ve)
  | Ox86_VPINSR ve => ok (VPINSR_desc ve)
  | Ox86_VPSLL ve sz => ok (VPSLL_desc ve sz)
  | Ox86_VPSRL ve sz => ok (VPSRL_desc ve sz)
  | Ox86_VPSRA ve sz => ok (VPSRA_desc ve sz)
  | Ox86_VPSLLV ve sz => ok (VPSLLV_desc ve sz)
  | Ox86_VPSRLV ve sz => ok (VPSRLV_desc ve sz)
  | Ox86_VPSLLDQ sz => ok (VPSLLDQ_desc sz)
  | Ox86_VPSRLDQ sz => ok (VPSRLDQ_desc sz)
  | Ox86_VPSHUFB sz => ok (VPSHUFB_desc sz)
  | Ox86_VPSHUFHW sz => ok (VPSHUFHW_desc sz)
  | Ox86_VPSHUFLW sz => ok (VPSHUFLW_desc sz)
  | Ox86_VPSHUFD sz => ok (VPSHUFD_desc sz)
  | Ox86_VPUNPCKH ve sz => ok (VPUNPCKH_desc ve sz)
  | Ox86_VPUNPCKL ve sz => ok (VPUNPCKL_desc ve sz)
  | Ox86_VPBLENDD sz => ok (VPBLENDD_desc sz)
  | Ox86_VPBROADCAST ve sz => ok (VPBROADCAST_desc ve sz)
  | Ox86_VBROADCASTI128 => ok VBROADCASTI128_desc
  | Ox86_VEXTRACTI128 => ok VEXTRACTI128_desc
  | Ox86_VINSERTI128 => ok VINSERTI128_desc
  | Ox86_VPERM2I128 => ok VPERM2I128_desc
  | Ox86_VPERMQ => ok VPERMQ_desc
  end.

Lemma sopn_desc_name ii o d : sopn_desc ii o = ok d -> d.(id_name) = o.
Proof.
  by case: o => //=; (move => w w' h || move => w h || move => h); have <- := ok_inj h.
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
  + case => // s w i'; t_xrbindP => z h <-; eexists; split; last reflexivity; repeat f_equal.
    move: h; rewrite /check_immediate. case: eqP => // <- [<-] {z}.
    case hsz: (w ≤ U64)%CMP.
    + by rewrite zero_extend_sign_extend // sign_extend_u.
    have hsz' : (U64 ≤ w)%CMP.
    + by apply: cmp_nle_le; rewrite hsz.
    by rewrite !(sign_extend_truncate _ hsz') !(zero_extend_idem _ hsz') !zero_extend_u.
  + by case => // ? ? [<-]; eauto.
  + by case => // ? ? [<-]; eexists; (split; [ | reflexivity ]).
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

Lemma type_of_rbool c : type_of_val (of_rbool c) = sbool.
Proof. by case: c. Qed.

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
- by rewrite type_of_rbool.
- by rewrite type_of_rbool.
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
