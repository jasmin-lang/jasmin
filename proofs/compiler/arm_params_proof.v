From Coq Require Import Relations.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat finfun.
From mathcomp Require Import ssralg.
From mathcomp Require Import word_ssrZ.

Require Import oseq.

Require Import
  arch_params_proof
  compiler_util
  expr
  fexpr
  fexpr_sem
  psem
  psem_facts
  sem_one_varmap.
Require Import
  lea_proof
  linearization
  linearization_proof
  lowering
  stack_alloc_params_proof
  stack_zeroization_proof.
Require
  arch_sem.
Require Import
  arch_decl
  arch_extra
  asm_gen
  asm_gen_proof
  sem_params_of_arch_extra.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl
  arm
  arm_params_common
  arm_params_common_proof
  arm_params_core_proof
  arm_lowering
  arm_lowering_proof
  arm_stack_zeroization_proof.
Require Export arm_params.

Section Section.

#[local] Existing Instance withsubword.
#[local] Existing Instance direct_c.

Context
  {atoI  : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {call_conv : calling_convention}.

(* ------------------------------------------------------------------------ *)
(* Stack alloc hypotheses. *)

Section STACK_ALLOC.

(* TODO: we may want to factor this (cf. riscv_lower_addressing_proof)
   but not that simple *)
Lemma shift_of_scaleP scale shift w :
  shift_of_scale scale = Some shift ->
  wshl w (wunsigned (wrepr U8 (Z.of_nat shift))) = (wrepr Uptr scale * w)%R.
Proof.
  by case: scale => // -[|[|[|[]|]|]|] //= [<-]; rewrite wshl_sem /=.
Qed.

Lemma arm_mov_ofsP : mov_ofs_correct arm_saparams.(sap_mov_ofs).
Proof.
  move=> P' ev s1 e w ofs pofs x tag mk ii ins s2 P'_globs.
  t_xrbindP=> ve ok_ve ok_w vofs ok_vofs ok_pofs.
  rewrite /sap_mov_ofs /= /arm_mov_ofs.
  case: mk.
  + move=> [<-] hw; exists (evm s2) => //.
    rewrite with_vm_same.
    rewrite /sem_sopn /= P'_globs /exec_sopn.
    case: is_zeroP.
    + move=> hofs.
      rewrite ok_ve /= ok_w /=.
      move: hofs ok_vofs ok_pofs hw => -> /=.
      rewrite /sem_sop1 /= => -[<-] /=.
      rewrite truncate_word_u wrepr0 => -[<-].
      by rewrite GRing.addr0 => -> /=.
    move=> _ /=.
    rewrite ok_ve ok_vofs /= /sem_sop2 /= ok_w ok_pofs /= truncate_word_u /=.
    by rewrite hw.
  case: x => //.
  + move=> x_; set x := Lvar x_.
    case: ifP => _.
    + case: is_zeroP => // hofs [<-] hw; exists (evm s2) => //.
      rewrite with_vm_same.
      rewrite /sem_sopn /= P'_globs /exec_sopn ok_ve /= ok_w /= zero_extend_u.
      move: hofs ok_vofs ok_pofs hw => -> /=.
      rewrite /sem_sop1 /= => -[<-] /=.
      rewrite truncate_word_u wrepr0 => -[<-].
      by rewrite GRing.addr0 => -> /=.
    case hlea: mk_lea => [[disp base scale offset]|//] /=.
    case: base hlea => [base|//] hlea.
    have lea_sem: sem_pexpr true [::] s1 (add e ofs) = ok (Vword (w + pofs)).
    + by rewrite /= ok_ve ok_vofs /= /sem_sop2 /= ok_w ok_pofs /=.
    have /(_ (cmp_le_refl _)) /(_ (cmp_le_refl _)) := mk_leaP _ _ hlea lea_sem.
    rewrite zero_extend_u /sem_lea /=.
    (* t_xrbindP too aggressive *)
    apply: rbindP => wb.
    apply: rbindP => vb ok_vb ok_wb.
    apply: rbindP => wo ok_wo.
    move=> /ok_inj; rewrite GRing.addrC => {}lea_sem.
    case: offset {hlea} ok_wo => [offset|] /=.
    + t_xrbindP=> vo ok_vo ok_wo.
      case: eqP => // ?; subst disp.
      case hshift: shift_of_scale => [shift|//] /=.
      case: eqP => [heq|_].
      + move=> [<-] hw.
        exists (evm s2) => //.
        rewrite /sem_sopn P'_globs /= /get_gvar /= ok_vb ok_vo /=
          /exec_sopn /= ok_wb ok_wo /=.
        have := shift_of_scaleP wo hshift.
        rewrite heq wrepr0 wunsigned0 wshl_sem //= wrepr1 GRing.mul1r => ->.
        move: lea_sem; rewrite wrepr0 GRing.addr0 => ->.
        by rewrite hw /= with_vm_same.
      move=> [<-] hw.
      exists (evm s2) => //.
      rewrite /sem_sopn P'_globs /= /get_gvar /= ok_vb ok_vo /=
        /exec_sopn /= ok_wb ok_wo truncate_word_u /=.
      rewrite (shift_of_scaleP wo hshift).
      move: lea_sem; rewrite wrepr0 GRing.addr0 => ->.
      by rewrite hw /= with_vm_same.
    move=> [?]; subst wo.
    case: eqP => [|_].
    + move=> ?; subst disp.
      move=> [<-] hw.
      exists s2.(evm) => //.
      rewrite /sem_sopn P'_globs /= /get_gvar /= ok_vb /=
        /exec_sopn /= ok_wb /=.
      move: lea_sem; rewrite wrepr0 GRing.mulr0 !GRing.addr0 => ->.
      by rewrite hw /= with_vm_same.
    case: ifP => _.
    + move=> [<-] hw.
      exists s2.(evm) => //.
      rewrite /sem_sopn P'_globs /= /get_gvar /= ok_vb /=
        /exec_sopn /= ok_wb truncate_word_u /=.
      move: lea_sem; rewrite GRing.mulr0 GRing.addr0 => ->.
      by rewrite hw /= with_vm_same.
    move=> [<-] hw.
    exists s2.(evm) => //.
    rewrite /sem_sopn P'_globs /= /get_gvar /= ok_vb /=
      /exec_sopn /= ok_wb truncate_word_u /=.
    move: lea_sem; rewrite GRing.mulr0 GRing.addr0 => ->.
    by rewrite hw /= with_vm_same.
  move=> al ws_ x_ e_; move: (Lmem al ws_ x_ e_) => {al ws_ x_ e_} x.
  case: is_zeroP => // hofs [<-] hw; exists (evm s2) => //.
  rewrite with_vm_same.
  rewrite /sem_sopn /= P'_globs /exec_sopn ok_ve /= ok_w /= zero_extend_u.
  move: hofs ok_vofs ok_pofs hw => -> /=.
  rewrite /sem_sop1 /= => -[<-] /=.
  rewrite truncate_word_u wrepr0 => -[<-].
  by rewrite GRing.addr0 => -> /=.
Qed.

Lemma arm_immediateP : immediate_correct arm_saparams.(sap_immediate).
Proof.
  move=> P' ev s ii x z.
  case: x => - [] [] // [] // x xi _ /=.
  by rewrite /sem_sopn /= /exec_sopn /= truncate_word_u.
Qed.

Lemma arm_swapP : swap_correct arm_saparams.(sap_swap).
Proof.
  move=> P' ev s ii tag x y z w pz pw hxty hyty hzty hwty hz hw.
  rewrite /= /sem_sopn /= /get_gvar /= /get_var /= hz hw /=.
  rewrite /exec_sopn /= !truncate_word_u /= /write_var /set_var /=.
  rewrite hxty hyty //=.
Qed.

End STACK_ALLOC.

Definition arm_hsaparams :
  h_stack_alloc_params (ap_sap arm_params) :=
  {|
    mov_ofsP := arm_mov_ofsP;
    sap_immediateP := arm_immediateP;
    sap_swapP := arm_swapP;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization hypotheses. *)

Section LINEARIZATION.

Lemma arm_spec_lip_allocate_stack_frame :
  allocate_stack_frame_correct arm_liparams.
Proof.
  move=> sp_rsp tmp s ts sz htmp hget /=.
  rewrite /arm_allocate_stack_frame.
  case: tmp htmp => [tmp [h1 h2]| _].
  + have [? [-> ? /get_varP [-> _ _]]] := [elaborate
      ARMFopnP.smart_subi_tmp_sem_fopn_args dummy_var_info sz h1 h2 (to_word_get_var hget)
    ].
    by eexists.
  rewrite /= hget /=; t_arm_op.
  eexists; split; first reflexivity.
  + by move=> z hz; rewrite Vm.setP_neq //; apply /eqP; SvD.fsetdec.
  by rewrite Vm.setP_eq wsub_wnot1 vm_truncate_val_eq.
Qed.

Lemma arm_spec_lip_free_stack_frame :
  free_stack_frame_correct arm_liparams.
Proof.
  move=> sp_rsp tmp s ts sz htmp hget /=.
  rewrite /arm_free_stack_frame.
  case: tmp htmp => [tmp [h1 h2]| _].
  + have [? [-> ? /get_varP [-> _ _]]] := [elaborate
      ARMFopnP.smart_addi_tmp_sem_fopn_args dummy_var_info sz h1 h2 (to_word_get_var hget)
    ].
    by eexists.
  rewrite /= hget /=; t_arm_op.
  eexists; split; first reflexivity.
  + by move=> z hz; rewrite Vm.setP_neq //; apply /eqP; SvD.fsetdec.
  by rewrite Vm.setP_eq vm_truncate_val_eq.
Qed.

Lemma arm_spec_lip_set_up_sp_register :
  set_up_sp_register_correct arm_liparams.
Proof.
  Opaque sem_fopn_args.
  move=> [[? nrsp] vi1] [[? nr] vi2] [[? ntmp] vi3] ts al sz s hget /= ??? hne hne1 hne2; subst.
  rewrite /arm_set_up_sp_register sem_fopns_args_cat /=.
  set vr := {|vname := nr|}; set r := {|v_var := vr|}.
  set vtmp := {|vname := ntmp|}; set tmp := {|v_var := vtmp|}.
  set vrsp := {|vname := nrsp|}; set rsp := {|v_var := vrsp|}.
  set ts' := align_word _ _.
  have := ARMFopnP.smart_subi_sem_fopn_args vi3 (y:= rsp) _ (to_word_get_var hget).
  move=> /(_ arm_linux_call_conv ntmp sz) [].
  + by right => /= -[?]; subst ntmp.
  move=> vm1 [] -> heq1 hget1 /=.
  set s1 := with_vm _ _.
  have -> /= := ARMFopnP.align_sem_fopn_args ntmp vi3 al
                 (y:= tmp) (s:= s1) (to_word_get_var hget1).
  set s2 := with_vm _ _.
  have hget2 : get_var true (evm s2) rsp = ok (Vword ts).
  + by t_get_var; rewrite (get_var_eq_ex _ _ heq1) //; apply/Sv_neq_not_in_singleton.
  have -> /= := ARMFopnP.mov_sem_fopn_args (to_word_get_var hget2).
  set s3 := with_vm _ _.
  have hget3 : get_var true (evm s3) tmp = ok (Vword ts').
  + by t_get_var.
  have -> /= := ARMFopnP.mov_sem_fopn_args (to_word_get_var hget3).
  set s4 := with_vm _ _.
  Transparent sem_fopn_args.
  eexists; split => //.

  - move=> x; t_notin_add; t_vm_get; rewrite heq1; first by t_vm_get.
    by apply/Sv_neq_not_in_singleton/nesym.

  - by t_get_var => //=; rewrite wrepr_mod.

  - by t_get_var.

  move=> x hx _.
  move: hx => /vflagsP hxtype.
  have [*] : [/\ vrsp <> x,  vtmp <> x & vr <> x].
  - by split; apply/eqP/vtype_diff; rewrite hxtype.
  t_vm_get; rewrite heq1 //.
  by apply: Sv_neq_not_in_singleton.
Qed.

Lemma uload_mn_of_wsizeP ws ws' mn (w : word ws) (w' : word ws') :
  uload_mn_of_wsize ws = Some mn
  -> truncate_word ws w' = ok w
  -> exec_sopn (Oarm (ARM_op mn default_opts)) [:: Vword w' ]
     = ok [:: Vword (zero_extend reg_size w) ].
Proof.
  case: ws w => w // [?]; subst mn.
  all: rewrite /exec_sopn /=.
  all: by move=> -> /=.
Qed.

Lemma arm_lmove_correct : lmove_correct arm_liparams.
Proof.
  move=> xd xs w ws w' s htxd htxs hget htr.
  rewrite /arm_liparams /lip_lmove /arm_lmove /= hget /=.
  rewrite /exec_sopn /= htr /=.
  by rewrite set_var_eq_type ?htxd.
Qed.

Lemma arm_lstore_correct : lstore_correct_aux arm_check_ws arm_lstore.
Proof.
  move=> xd xs ofs ws w wp s m htxs /eqP hchk; t_xrbindP; subst ws.
  move=> vd hgetd htrd vs hgets htrs hwr.
  rewrite /arm_lstore /= hgets hgetd /= /exec_sopn /= htrs /=.
  rewrite /sem_sop2 /= htrd /= !truncate_word_u /= truncate_word_u /=.
  by rewrite zero_extend_u hwr.
Qed.

Lemma arm_smart_addi_correct : ladd_imm_correct_aux ARMFopn.smart_addi.
Proof.
  move=> [[_ xn1] xi] x2 s w ofs /= -> hne hget.
  by apply: ARMFopnP.smart_addi_sem_fopn_args hget; right.
Qed.

Lemma arm_lstores_correct : lstores_correct arm_liparams.
Proof.
  apply/lstores_imm_dfl_correct.
  + by apply arm_lstore_correct.
  apply arm_smart_addi_correct.
Qed.

Lemma arm_lload_correct : lload_correct_aux (lip_check_ws arm_liparams) arm_lload.
Proof.
  move=> xd xs ofs ws top s w vm heq hcheck; t_xrbindP => ? hgets hto hread hset.
  move/eqP: hcheck => ?; subst ws.
  rewrite /arm_lload /= hgets /= /sem_sop2 /= hto /= !truncate_word_u /= truncate_word_u /= hread /=.
  by rewrite /exec_sopn /= truncate_word_u /= zero_extend_u hset.
Qed.

Lemma arm_lloads_correct : lloads_correct arm_liparams.
Proof.
  apply/lloads_imm_dfl_correct.
  + by apply arm_lload_correct.
  apply arm_smart_addi_correct.
Qed.

Lemma arm_tmp_correct : lip_tmp arm_liparams <> lip_tmp2 arm_liparams.
Proof. by move=> h; assert (h1 := inj_to_ident h). Qed.

Lemma arm_check_ws_correct : lip_check_ws arm_liparams Uptr.
Proof. done. Qed.

End LINEARIZATION.

Definition arm_hliparams :
  h_linearization_params (ap_lip arm_params) :=
  {|
    spec_lip_allocate_stack_frame := arm_spec_lip_allocate_stack_frame;
    spec_lip_free_stack_frame     := arm_spec_lip_free_stack_frame;
    spec_lip_set_up_sp_register   := arm_spec_lip_set_up_sp_register;
    spec_lip_lmove                := arm_lmove_correct;
    spec_lip_lstore               := arm_lstore_correct;
    spec_lip_lload                := arm_lload_correct;
    spec_lip_lstores              := arm_lstores_correct;
    spec_lip_lloads               := arm_lloads_correct;
    spec_lip_tmp                  := arm_tmp_correct;
    spec_lip_check_ws             := arm_check_ws_correct;
  |}.

Lemma arm_ok_lip_tmp :
  exists r : reg_t, of_ident (lip_tmp (ap_lip arm_params)) = Some r.
Proof. exists R12; exact: to_identK. Qed.

Lemma arm_ok_lip_tmp2 :
  exists r : reg_t, of_ident (lip_tmp2 (ap_lip arm_params)) = Some r.
Proof. exists LR; exact: to_identK. Qed.

(* ------------------------------------------------------------------------ *)
(* Lowering hypotheses. *)

Definition arm_hloparams : h_lowering_params (ap_lop arm_params).
Proof. split=> *; [exact: lower_callP | exact: it_lower_callP]. Qed.

(* ------------------------------------------------------------------------ *)
(* Lowering of complex addressing mode for RISC-V.
   It is the identity on arm, so the proof is trivial. *)

Lemma arm_hlaparams : h_lower_addressing_params (ap_lap arm_params).
Proof.
  split=> /=.
  + by move=> _ ? _ [<-].
  + move=> _ ? _ [<-] _ fd ->; by exists fd.
  + by move=> _ ? _ [<-].
  move=> ???? _ ? _ ?? [<-]; exact: (wiequiv_f_eq (scP := sCP_stack)).
Qed.

(* ------------------------------------------------------------------------ *)
(* Assembly generation hypotheses. *)

Section ASM_GEN.

Notation assemble_extra_correct :=
  (assemble_extra_correct arm_agparams) (only parsing).

(* FIXME: the following line fixes type inference with Coq 8.16 *)
Local Instance the_asm : asm _ _ _ _ _ _ := _.

Lemma condt_of_rflagP rf r :
  arm_eval_cond (get_rf rf) (condt_of_rflag r) = to_bool (of_rbool (rf r)).
Proof.
  rewrite -get_rf_to_bool_of_rbool. by case: r.
Qed.

Lemma condt_notP rf c b :
  arm_eval_cond rf c = ok b
  -> arm_eval_cond rf (condt_not c) = ok (negb b).
Proof.
  case: c => /=.

  (* Introduce booleans [b] and equalities [_ = b] and [rf _ = ok b].
     Rewrite all equalities, simplify and case all booleans. *)
  all: t_xrbindP=> *.
  all: subst=> /=.
  all:
    repeat
      match goal with
      | [ H : _ _ = ok _ |- _ ] => rewrite H {H} /=
      end.
  all:
    by repeat
      match goal with
      | [ b : bool |- _ ] => case: b
      end.
Qed.

Lemma condt_andP rf c0 c1 c b0 b1 :
  condt_and c0 c1 = Some c
  -> arm_eval_cond rf c0 = ok b0
  -> arm_eval_cond rf c1 = ok b1
  -> arm_eval_cond rf c = ok (b0 && b1).
Proof.
  move: c0 c1 => [] [] //.
  all: move=> [?]; subst c.
  all: rewrite /arm_eval_cond /=.

  (* Introduce booleans [b] and equalities [_ = b] and [rf _ = ok b].
     Rewrite all equalities, simplify and case all booleans. *)
  all: t_xrbindP=> *.
  all: subst=> /=.
  all:
    repeat
      match goal with
      | [ H : _ _ = ok _ |- _ ] => rewrite H {H} /=
      end.
  all:
    by repeat
      match goal with
      | [ b : bool |- _ ] => case: b
      end.
Qed.

Lemma condt_orP rf c0 c1 c b0 b1 :
  condt_or c0 c1 = Some c
  -> arm_eval_cond rf c0 = ok b0
  -> arm_eval_cond rf c1 = ok b1
  -> arm_eval_cond rf c = ok (b0 || b1).
Proof.
  move: c0 c1 => [] [] //.
  all: move=> [?]; subst c.
  all: rewrite /arm_eval_cond /=.

  (* Introduce booleans [b] and equalities [_ = b] and [rf _ = ok b].
     Rewrite all equalities, simplify and case all booleans. *)
  all: t_xrbindP=> *.
  all: subst=> /=.
  all:
    repeat
      match goal with
      | [ H : _ _ = ok _ |- _ ] => rewrite H {H} /=
      end.
  all:
    by repeat
      match goal with
      | [ b : bool |- _ ] => case: b
      end.
Qed.

Lemma eval_assemble_cond_Pvar ii m rf x r v :
  eqflags m rf
  -> of_var_e ii x = ok r
  -> get_var true (evm m) x = ok v
  -> exists2 v',
       value_of_bool (arm_eval_cond (get_rf rf) (condt_of_rflag r)) = ok v'
       & value_uincl v v'.
Proof.
  move=> eqf hr hv.
  have hincl := xgetflag_ex eqf hr hv.
  clear ii x m eqf hr hv.

  rewrite condt_of_rflagP.

  eexists; last exact: hincl.
  clear v hincl.
  exact: value_of_bool_to_bool_of_rbool.
Qed.

Lemma eval_assemble_cond_Onot rf c v v0 v1 :
  value_of_bool (arm_eval_cond (get_rf rf) c) = ok v1
  -> value_uincl v0 v1
  -> sem_sop1 Onot v0 = ok v
  -> exists2 v',
       value_of_bool (arm_eval_cond (get_rf rf) (condt_not c)) = ok v'
       & value_uincl v v'.
Proof.
  move=> hv1 hincl.
  move=> /sem_sop1I /= [b [b'] [hb [?] ? ]]; subst v b'.

  have hc := value_uincl_to_bool_value_of_bool hincl hb hv1.
  clear v0 v1 hincl hb hv1.

  rewrite (condt_notP hc) {hc}.
  by eexists.
Qed.

Lemma eval_assemble_cond_Obeq ii m rf v x0 x1 r0 r1 v0 v1 :
  is_rflags_GE r0 r1 = true
  -> eqflags m rf
  -> of_var_e ii x0 = ok r0
  -> get_var true (evm m) x0 = ok v0
  -> of_var_e ii x1 = ok r1
  -> get_var true (evm m) x1 = ok v1
  -> sem_sop2 Obeq v0 v1 = ok v
  -> exists2 v',
       value_of_bool (arm_eval_cond (get_rf rf) GE_ct) = ok v' & value_uincl v v'.
Proof.
  move=> hGE eqf hr0 hv0 hr1 hv1.

  move=> /sem_sop2I /= [b0 [b1 [b [hb0 hb1 hb ?]]]]; subst v.
  move: hb.
  rewrite /mk_sem_sop2 /=.
  move=> [?]; subst b.

  have hincl0 := xgetflag_ex eqf hr0 hv0.
  have hincl1 := xgetflag_ex eqf hr1 hv1.
  clear ii m x0 x1 eqf hr0 hv0 hr1 hv1.

  have ? := to_boolI hb0; subst v0.
  have ? := to_boolI hb1; subst v1.
  clear hb0 hb1.

  move: r0 r1 hincl0 hincl1 hGE.
  move=> [] [] // hincl0 hincl1 _.
  all: rewrite 2!get_rf_to_bool_of_rbool.
  all: rewrite (value_uinclE hincl0) {hincl0} /=.
  all: rewrite (value_uinclE hincl1) {hincl1} /=.
  all: by eexists.
Qed.

Lemma eval_assemble_cond_Oand rf c c0 c1 v v0 v1 v0' v1' :
  condt_and c0 c1 = Some c
  -> value_of_bool (arm_eval_cond (get_rf rf) c0) = ok v0'
  -> value_uincl v0 v0'
  -> value_of_bool (arm_eval_cond (get_rf rf) c1) = ok v1'
  -> value_uincl v1 v1'
  -> sem_sop2 Oand v0 v1 = ok v
  -> exists2 v',
       value_of_bool (arm_eval_cond (get_rf rf) c) = ok v' & value_uincl v v'.
Proof.
  move=> hand hv0' hincl0 hv1' hincl1.
  move=> /sem_sop2I /= [b0 [b1 [b [hb0 hb1 hb ?]]]]; subst v.

  move: hb.
  rewrite /mk_sem_sop2 /=.
  move=> [?]; subst b.

  have hc0 := value_uincl_to_bool_value_of_bool hincl0 hb0 hv0'.
  have hc1 := value_uincl_to_bool_value_of_bool hincl1 hb1 hv1'.
  clear hincl0 hb0 hv0' hincl1 hb1 hv1'.

  rewrite (condt_andP hand hc0 hc1) {hand hc0 hc1} /=.
  by eexists.
Qed.

Lemma eval_assemble_cond_Oor rf c c0 c1 v v0 v1 v0' v1' :
  condt_or c0 c1 = Some c
  -> value_of_bool (arm_eval_cond (get_rf rf) c0) = ok v0'
  -> value_uincl v0 v0'
  -> value_of_bool (arm_eval_cond (get_rf rf) c1) = ok v1'
  -> value_uincl v1 v1'
  -> sem_sop2 Oor v0 v1 = ok v
  -> exists2 v',
       value_of_bool (arm_eval_cond (get_rf rf) c) = ok v' & value_uincl v v'.
Proof.
  move=> hor hv0' hincl0 hv1' hincl1.
  move=> /sem_sop2I /= [b0 [b1 [b [hb0 hb1 hb ?]]]]; subst v.

  move: hb.
  rewrite /mk_sem_sop2 /=.
  move=> [?]; subst b.

  have hc0 := value_uincl_to_bool_value_of_bool hincl0 hb0 hv0'.
  have hc1 := value_uincl_to_bool_value_of_bool hincl1 hb1 hv1'.
  clear hincl0 hb0 hv0' hincl1 hb1 hv1'.

  rewrite (condt_orP hor hc0 hc1) {hor hc0 hc1} /=.
  by eexists.
Qed.

Lemma arm_eval_assemble_cond : assemble_cond_spec arm_agparams.
Proof.
  move=> ii m rr rf e c v; rewrite /arm_agparams /arm_eval_cond /get_rf /=.
  move=> eqr eqf.
  elim: e c v => [| x | op1 e hind | op2 e0 hind0 e1 hind1 |] //= c v.

  - t_xrbindP=> r hr hc; subst c.
    move=> hv.
    exact: (eval_assemble_cond_Pvar eqf hr hv).

  - case: op1 => //.
    t_xrbindP=> c' hc' hc; subst c.
    move=> v0 hv0 hsem.
    have [v1 hv1 hincl1] := hind _ _ hc' hv0.
    clear ii m e eqr eqf hc' hv0 hind.
    exact: (eval_assemble_cond_Onot hv1 hincl1 hsem).

  case: op2 => //.
  - case: e0 hind0 => // x0 _.
    case: e1 hind1 => // x1 _.
    t_xrbindP=> r0 hr0 r1 hr1 //=.
    case hGE: is_rflags_GE => // -[?]; subst c.
    move=> v0 hv0 v1 hv1 hsem.
    exact: (eval_assemble_cond_Obeq hGE eqf hr0 hv0 hr1 hv1 hsem).

  - t_xrbindP=> c0 hass0 c1 hass1.
    case hand: condt_and => [c'|] // [?]; subst c'.
    move=> v0 hsem0 v1 hsem1 hsem.
    have [v0' hv0' hincl0] := hind0 _ _ hass0 hsem0.
    have [v1' hv1' hincl1] := hind1 _ _ hass1 hsem1.
    clear eqr eqf hass0 hsem0 hind0 hass0 hsem1 hind1.
    exact: (eval_assemble_cond_Oand hand hv0' hincl0 hv1' hincl1 hsem).

  t_xrbindP=> c0 hass0 c1 hass1.
  case hor: condt_or => [c'|] // [?]; subst c'.
  move=> v0 hsem0 v1 hsem1 hsem.
  have [v0' hv0' hincl0] := hind0 _ _ hass0 hsem0.
  have [v1' hv1' hincl1] := hind1 _ _ hass1 hsem1.
  clear eqr eqf hass0 hsem0 hind0 hass0 hsem1 hind1.
  exact: (eval_assemble_cond_Oor hor hv0' hincl0 hv1' hincl1 hsem).
Qed.

(* TODO_ARM: Is there a way of avoiding importing here? *)
Import arch_sem.

Lemma sem_sopns_fopns_args s lc :
  sem_sopns s [seq (None, o, d, e) | '(d, o, e) <- lc] =
  sem_fopns_args s (map ARMFopn.to_opn lc).
Proof.
  elim: lc s => //= -[[xs o] es ] lc ih s.
  rewrite /sem_fopn_args /sem_sopn_t /=; case: sem_rexprs => //= >.
  by rewrite /exec_sopn /= /sopn_sem /Oarm; case: i_valid => //=; case : app_sopn => //= >; case write_lexprs.
Qed.

Lemma assemble_swap_correct ws : assemble_extra_correct (Oarm_swap ws).
Proof.
  move=> rip ii lvs args m xs ys m' s ops ops' /=.
  case: eqP => // -> {ws}.
  case: lvs => // -[] // x [] // -[] // y [] //.
  case: args => // -[] // [] // z [] // [] // [] // w [] //=.
  t_xrbindP => vz hz _ vw hw <- <-.
  rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /= /swap_semi.
  t_xrbindP => /= _ wz hvz ww hvw <- <- /=.
  t_xrbindP => _ vm1 /set_varP [_ htrx ->] <- _ vm2 /set_varP [_ htry ->] <- <- /eqP hxw /eqP hyx
    /and4P [/eqP hxt /eqP hyt /eqP hzt /eqP hwt] <-.
  move=> hmap hlom.
  have h := (assemble_opsP arm_eval_assemble_cond hmap erefl _ hlom).
  set m1 := (with_vm m (((evm m).[x <- Vword (wxor wz ww)]).[y <- Vword (wxor (wxor wz ww) ww)])
                                .[x <- Vword (wxor (wxor wz ww) (wxor (wxor wz ww) ww))]).
  case: (h m1) => {h}.
  + rewrite /= hz /= hw /= /exec_sopn /= hvz hvw /=.
    rewrite set_var_truncate //= !get_var_eq //= hxt /=.
    rewrite get_var_neq // hw /= truncate_word_u /= hvw /=.
    rewrite set_var_truncate //= !get_var_eq //= hyt /=.
    rewrite get_var_neq // get_var_eq //= hxt /= !truncate_word_u /=.
    rewrite set_var_truncate //= !with_vm_idem.
  move=> s' hfold hlom'; exists s' => //; apply: lom_eqv_ext hlom'.
  move=> i /=; rewrite !Vm.setP; case: eqP => [<- | ?].
  + by move/eqP/negbTE: hyx => -> /=; rewrite hxt /= wxorA wxor_xx wxor0.
  by case: eqP => // _; rewrite -wxorA wxor_xx wxorC wxor0.
Qed.

Lemma assemble_add_large_imm_correct :
  assemble_extra_correct Oarm_add_large_imm.
Proof.
  move=> rip ii lvs args m xs ys m' s ops ops' /=.
  case: lvs => // -[] // [[xt xn] xi] [] //.
  case: args => // -[] // [] // y [] // [] // [] // [] // w [] // imm [] //=.
  t_xrbindP => vy hvy <-.
  rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /=; t_xrbindP => /= n w1 hw1 w2 hw2 ? <- /=; subst n.
  t_xrbindP => ? vm1 hsetx <- <- /= /eqP hne.
  move=> /andP []/eqP ? /andP [] /eqP hyty _ <- hmap hlom; subst xt.
  move/to_wordI: hw1 => [ws [w' [?]]] /truncate_wordP [hle1 ?]; subst vy w1.
  move/get_varP: (hvy) => [_ _ /compat_valE] /=; rewrite hyty => -[_ [] <- hle2].
  have ? := cmp_le_antisym hle1 hle2; subst ws => {hle1 hle2}.
  have := ARMFopnP.smart_addi_sem_fopn_args xi (y:= y) (or_intror _ hne) (to_word_get_var hvy).
  move=> /(_ _ imm) [vm []]; rewrite -sem_sopns_fopns_args => hsem heqex /get_varP [hvmx _ _].
  have [] := (assemble_opsP arm_eval_assemble_cond hmap _ hsem hlom).
  + by rewrite all_map; apply/allT => -[[]].
  move=> s' -> hlo; exists s' => //.
  apply: lom_eqv_ext hlo => z /=.
  move/get_varP: hvy => -[hvmy _ _].
  move: hsetx; rewrite set_var_eq_type // => -[<-].
  rewrite Vm.setP.
  case: eqP => heqx.
  + rewrite -heqx -hvmx zero_extend_u /=.
    move: hw2 => /truncate_wordP [? ].
    by rewrite zero_extend_wrepr // => ->.
  by apply heqex; rewrite /arm_reg_size; SvD.fsetdec.
Qed.

Lemma unconsP {ii X x} {xs xs' : seq X} :
  uncons ii xs = ok (x, xs') ->
  xs = x :: xs'.
Proof. by case: xs => [// | ??] [-> ->]. Qed.

Lemma uncons_LLvarP ii les x les' :
  uncons_LLvar ii les = ok (x, les') ->
  les = LLvar x :: les'.
Proof. by case: les => [// | [// | ?] ?] [-> ->]. Qed.

Lemma uncons_rvarP ii res x res' :
  uncons_rvar ii res = ok (x, res') ->
  res = rvar x :: res'.
Proof. by case: res => [// | [// | [] // ?] ?] [-> ->]. Qed.

Lemma uncons_wconstP ii les imm les' :
  uncons_wconst ii les = ok (imm, les') ->
  exists ws, les = rconst ws imm :: les'.
Proof.
  case: les => [// | [//|]] [] // [] // ? [] // ?? [-> ->]. by eexists.
Qed.

Lemma smart_li_argsP ii ws les res x imm res' :
  smart_li_args ii ws les res = ok (x, imm, res') ->
  [/\ ws = reg_size
    , les = [:: LLvar x ]
    , vtype (v_var x) = sword reg_size
    & exists ws', res = rconst ws' imm :: res'
  ].
Proof.
  rewrite /smart_li_args.
  t_xrbindP=> /eqP -> -[??] /uncons_LLvarP ->.
  t_xrbindP=> /eqP ? /nilP -> [??] /uncons_wconstP [? ->].
  t_xrbindP=> ???; subst.
  split=> //=.
  by eexists.
Qed.

Lemma assemble_smart_li_correct ws : assemble_extra_correct (Osmart_li ws).
Proof.
  move=> rip ii lvs args m xs ys m' s ops ops'.
  move=> hsemargs hexec hwrite.
  rewrite /= /assemble_smart_li.
  t_xrbindP=> -[[x imm] ?] /smart_li_argsP [? ? hty [ws' ?]] [?] hops heq;
    subst ws lvs args ops.
  have [vm []] :=
    ARMFopn_coreP.li_lsem_1 m (vname (v_var x)) (v_info x) imm.
  rewrite /= -hty -var_surj -var_i_surj => hsem hvm hgetx.
  have [] :=
    assemble_opsP (m' := with_vm m vm) arm_eval_assemble_cond hops _ _ heq.
  - rewrite /ARMFopn_core.li. case: ifP => //. by case: ifP.
  - move: hsem.
    by rewrite ARMFopnP.sem_fopns_equiv -sem_sopns_fopns_args /= => ->.
  move=> s' -> heq'.
  exists s' => //.
  move: hsemargs hexec hwrite => /=.
  t_xrbindP => vs _ ?; subst xs.
  rewrite /exec_sopn /= /sopn_sem /=.
  t_xrbindP=> w w' /truncate_wordP [hws' ?]; subst w'.
  case: vs => // -[?] ?; subst w ys.
  t_xrbindP=> m0 vm0 hsetx ??; subst m0 m'.
  apply: (lom_eqv_ext _ heq').
  move=> y.
  move/get_varP: hgetx => -[/= hx _ _].
  move: hsetx.
  rewrite set_var_eq_type //.
  move=> [<-].
  rewrite Vm.setP.
  case: eqP => [? | hne].
  - subst y.
    by rewrite /= hty cmp_le_refl zero_extend_wrepr // hx -hty -var_surj.
  rewrite hvm //.
  by apply/Sv.singleton_spec/nesym.
Qed.

Lemma assemble_smart_li_cc_correct ws :
  assemble_extra_correct (Osmart_li_cc ws).
Proof.
  move=> rip ii lvs args m xs ys m' s ops ops'.
  move=> hsemargs hexec hwrite.
  rewrite /= /assemble_smart_li_cc.
  t_xrbindP=> -[[x imm] args'] /smart_li_argsP [?? hty [ws' ?]];
    subst lvs args ws.
  t_xrbindP=> -[cond args] /unconsP ?; subst args'.
  t_xrbindP=> hfv_cond -[y ?] /uncons_rvarP ? hmk hops heq; subst args.
  have [vm' []] :=
    ARMFopn_coreP.li_lsem_1 m (vname (v_var x)) (v_info x) imm.
  rewrite /= -hty -var_surj -var_i_surj => hsem hvm hgetx.
  move: hsemargs hexec hwrite.
  rewrite  /exec_sopn /sopn_sem /sopn_sem_ /=.
  t_xrbindP=> _ vcond hsemcond _ vy hgety vrest hsemrest <- <- <-.
  t_xrbindP=>  w w' hw' bcond /to_boolI ? wy hwy; subst vcond.
  move: hw' => /to_wordI [ws [w0 []]] /Vword_inj [] ?; subst ws.
  rewrite /= => ? /truncate_wordP [hle1 ?]; subst w0 w'.
  case: vrest hsemrest; t_xrbindP=> // hsemrest ??; subst w ys.
  t_xrbindP=> _ vm hsetx <- <-.

  (* Type of [y]. *)
  have := type_of_get_var hgety.
  have := of_val_subtype (t := sword _) hwy.
  move=> /subtypeEl [/= wsy1 [htyvy hwsy1]].
  rewrite htyvy.
  move=> /subtypeEl [/= wsy0 [htyy hwsy0]].

  (* If execution goes through, the resulting vm is just
     [(evm m).[x <- Vword imm].
     Otherwise, the pseudo operator returns [(evm m).[x <- wy]], but the
     implementation might require several conditional instructions, all of which
     are the identity, thus it's [(evm m).[x <- wy]....[x <- wy]]. *)
  set vmf :=
    if bcond
    then vm'
    else
      ssrnat.iter
        (size (ARMFopn_core.li x imm) - 1)
        (fun vm => vm.[x <- Vword wy])
        vm.

  have [] :=
    assemble_opsP
      (m' := with_vm m vmf)
      arm_eval_assemble_cond
      hops
      _ _
      heq.
  all: subst vmf.

  - move: hmk.
    rewrite /ARMFopn_core.li.
    case: ifP => [_ [<-] // | _].
    by case: ifP => _ [<-].

  - move: hsem.
    rewrite ARMFopnP.sem_fopns_equiv -sem_sopns_fopns_args /=.
    move: hmk.
    rewrite /ARMFopn_core.li.
    case: ifP => _.

    (* Case: small immediate. *)
    + move=> [<-] /=.
      rewrite /exec_sopn /= /sopn_sem /= truncate_word_u /=.
      t_xrbindP=> ?? vm0 hvm' <- <- [?]; subst vm0.
      rewrite {}hsemcond {}hgety /= truncate_word_u {}hwy /=.
      case: bcond hsetx => /= [|-> //].
      by rewrite hvm'.

    case: ifP => _ [<-] /=.

    (* Case: negated immediate. *)
    + rewrite /exec_sopn /= /sopn_sem /= truncate_word_u /=.
      t_xrbindP=> ?? vm0 hvm' <- <- [?]; subst vm0.
      rewrite {}hsemcond {}hgety /= truncate_word_u {}hwy /=.
      case: bcond hsetx => /= [|-> //].
      by rewrite hvm'.

    (* Case: large immediate. *)
    rewrite /exec_sopn /= /sopn_sem /= truncate_word_u /=.
    t_xrbindP=> ?? vm0 hvm0 <- <- s0 _ vx hgetx0 <- vrest.
    rewrite /= truncate_word_u /=.
    t_xrbindP=> _ wx hwx [<-] <-.
    t_xrbindP=> ? vm1 hvm' <- <- [?]; subst vm1.
    rewrite hsemcond hgety /= truncate_word_u hwy /=.
    case: bcond hsetx hsemcond => /= hsetx hsemcond.
    + rewrite hvm0 /= hgetx0 /=.
      rewrite (fexpr_facts.free_vars_rP (vm2 := evm m) (emem m)); first last.
      * apply/eq_onS. exact: (set_var_disjoint_eq_on _ hvm0).
      rewrite hsemcond /=.
      rewrite (get_var_set_var _ _ hvm0) // hgety -(fun_if (@ok _)) /= hwx
        truncate_word_u /=.
      by rewrite htyy (cmp_le_trans hwsy1 hwsy0) fun_if /= truncate_word_u hwy
        -fun_if /= hvm'.
    rewrite hsetx /= !(get_var_set_var _ _ hsetx) //= eqxx /=.
    rewrite (fexpr_facts.free_vars_rP (vm2 := evm m) (emem m)); first last.
    * apply/eq_onS. exact: (set_var_disjoint_eq_on _ hsetx).
    rewrite hsemcond hgety -(fun_if (@ok _)) /= hty cmp_le_refl
      /= !truncate_word_u /= fun_if /= htyy /= (cmp_le_trans hwsy1 hwsy0)
      fun_if /= truncate_word_u hwy -!fun_if /= if_same.
    by move: hsetx => /set_varP [] /set_var_truncate /[apply] -> -> /=.

  move=> m0 heval hlom.
  eexists; first eassumption.
  apply: (lom_eqv_ext _ hlom).
  clear hsemcond hlom.
  move: hgetx => /get_varP /= [hgetx _ _].
  move: hsetx => /set_varP /= [_ _ ?]; subst vm.
  case: bcond => /= z.
  - rewrite Vm.setP.
    case: eqP => [? | hne].
    + subst z. by rewrite -hgetx /= hty cmp_le_refl zero_extend_wrepr.
    by rewrite hvm // => /Sv.singleton_spec /esym.
  rewrite /ARMFopn_core.li.
  case: ifP => //= _.
  case: ifP => //= _.
  rewrite Vm.setP.
  case: eqP => [-> | //].
  by rewrite Vm.setP_eq.
Qed.

Lemma arm_assemble_extra_op op : assemble_extra_correct op.
Proof.
  case: op.
  + exact: assemble_swap_correct.
  + exact: assemble_add_large_imm_correct.
  + exact: assemble_smart_li_correct.
  exact: assemble_smart_li_cc_correct.
Qed.

Definition arm_hagparams : h_asm_gen_params (ap_agp arm_params) :=
  {|
    hagp_eval_assemble_cond := arm_eval_assemble_cond;
    hagp_assemble_extra_op := arm_assemble_extra_op;
  |}.

End ASM_GEN.


(* ------------------------------------------------------------------------ *)
(* Speculative execution. *)

Lemma arm_hshp: slh_lowering_proof.h_sh_params (ap_shp arm_params).
Proof. by constructor; move=> ???? []. Qed.


(* ------------------------------------------------------------------------ *)
(* Stack zeroization. *)

Section STACK_ZEROIZATION.

Lemma arm_hszparams : h_stack_zeroization_params (ap_szp arm_params).
Proof.
  split.
  + exact: arm_stack_zero_cmd_not_ext_lbl.
  exact: arm_stack_zero_cmdP.
Qed.

End STACK_ZEROIZATION.


(* ------------------------------------------------------------------------ *)
(* Shared hypotheses. *)

Definition arm_is_move_opP op vx v :
  ap_is_move_op arm_params op
  -> exec_sopn (Oasm op) [:: vx ] = ok v
  -> List.Forall2 value_uincl v [:: vx ].
Proof.
  case: op => // -[[] // [mn opt]] /=.
  case: ifP => // hmn /and3P [/negPf hf /negPf hc /negPf hs].
  rewrite /exec_sopn /sopn_sem  /sopn_sem_ /= hc.
  (* To avoid duplication, we prove that [mn] returns [to_word ws vx] for some [ws] *)
  have ->:
    Let semi := assert (id_valid (mn_desc opt mn)) ErrType >> ok (id_semi (mn_desc opt mn)) in
    (Let t := app_sopn (id_tin (mn_desc opt mn)) semi [:: vx] in
    ok (list_ltuple t)) =
      Let ws := if head sbool (id_tout (mn_desc opt mn)) is sword ws then ok ws else type_error in
      Let wx := to_word ws vx in
      ok [:: Vword wx].
  + case: mn hmn => //= _; [rewrite /arm_MOV_instr /= hf /=|..];
      by case: to_word => //= ?; rewrite zero_extend_u.
  t_xrbindP=> ws' _ w' /to_wordI [ws [w [-> htr]]] <-.
  constructor=> //=.
  by apply (truncate_word_uincl htr).
Qed.


(* ------------------------------------------------------------------------ *)

Definition arm_h_params : h_architecture_params arm_params :=
  {|
    hap_hsap        := arm_hsaparams;
    hap_hlip        := arm_hliparams;
    ok_lip_tmp      := arm_ok_lip_tmp;
    ok_lip_tmp2     := arm_ok_lip_tmp2;
    hap_hlop        := arm_hloparams;
    hap_hlap        := arm_hlaparams;
    hap_hagp        := arm_hagparams;
    hap_hshp        := arm_hshp;
    hap_hszp        := arm_hszparams;
    hap_is_move_opP := arm_is_move_opP;
  |}.

End Section.
