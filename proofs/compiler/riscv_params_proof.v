From Coq Require Import Relations.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
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
  linearization
  linearization_proof
  lowering
  stack_alloc
  stack_alloc_proof_1
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
  riscv_decl
  riscv_extra
  riscv_instr_decl
  riscv
  riscv_params_common_proof
  riscv_lowering
  riscv_lowering_proof
  riscv_lower_addressing_proof
  riscv_stack_zeroization_proof.
Require Export riscv_params.

Section Section.

Context
  {atoI  : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {call_conv : calling_convention}.

#[local] Existing Instance withsubword.
#[local] Existing Instance direct_c.

(* ------------------------------------------------------------------------ *)
(* Stack alloc hypotheses. *)

Section STACK_ALLOC.

Lemma riscv_mov_ofsP : mov_ofs_correct riscv_saparams.(sap_mov_ofs).
Proof.
  move=> P' ev s1 e w ofs pofs x tag mk ins s2 P'_globs.
  t_xrbindP=> ve ok_ve ok_w vofs ok_vofs ok_pofs.
  rewrite /sap_mov_ofs /= /riscv_mov_ofs.
  case: mk.
  + move=> [<-] hw; exists (evm s2) => //.
    rewrite with_vm_same.
    constructor.
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
      constructor.
      rewrite /sem_sopn /= P'_globs /exec_sopn ok_ve /= ok_w /= sign_extend_u.
      move: hofs ok_vofs ok_pofs hw => -> /=.
      rewrite /sem_sop1 /= => -[<-] /=.
      rewrite truncate_word_u wrepr0 => -[<-].
      by rewrite GRing.addr0 => -> /=.
    case: is_zeroP.
    + move=> hofs [<-] hw; exists (evm s2) => //.
      rewrite with_vm_same.
      constructor.
      rewrite /sem_sopn /= P'_globs /exec_sopn ok_ve /= ok_w /=.
      move: hofs ok_vofs ok_pofs hw => -> /=.
      rewrite /sem_sop1 /= => -[<-] /=.
      rewrite truncate_word_u wrepr0 => -[<-].
      by rewrite GRing.addr0 => -> /=.
    move=> _.
    case: is_wconst_of_sizeP ok_vofs => [zofs|{}ofs] ok_vofs.
    + case: ifP => _.
      + move=> [<-] hw; exists (evm s2) => //.
        rewrite with_vm_same.
        constructor.
        rewrite /sem_sopn P'_globs /exec_sopn /= ok_ve /= ok_w /= truncate_word_u /=.
        move: ok_vofs ok_pofs hw.
        rewrite /= /sem_sop1 /= => -[<-] /=.
        by rewrite truncate_word_u => -[<-] ->.
      case: e ok_ve => //= y ok_ve.
      case: ifP => // _.
      move=> [<-] hw; exists (evm s2) => //.
      rewrite with_vm_same.
      constructor.
      rewrite /sem_sopn P'_globs /exec_sopn /= ok_ve /= ok_w /= truncate_word_u /=.
      move: ok_vofs ok_pofs hw.
      rewrite /= /sem_sop1 /= => -[<-] /=.
      by rewrite truncate_word_u => -[<-] ->.
    move=> [<-] /= hw; exists (evm s2) => //.
    rewrite with_vm_same.
    constructor.
    rewrite /sem_sopn P'_globs /exec_sopn /= ok_ve ok_vofs /=.
    rewrite /sem_sop2 /= ok_w ok_pofs /= truncate_word_u /=.
    by rewrite hw.
  move=> al ws_ x_ e_; move: (Lmem al ws_ x_ e_) => {al ws_ x_ e_} x.
  case: is_zeroP => // hofs [<-] hw; exists (evm s2) => //.
  rewrite with_vm_same.
  constructor.
  rewrite /sem_sopn /= P'_globs /exec_sopn ok_ve /= ok_w /= zero_extend_u.
  move: hofs ok_vofs ok_pofs hw => -> /=.
  rewrite /sem_sop1 /= => -[<-] /=.
  rewrite truncate_word_u wrepr0 => -[<-].
  by rewrite GRing.addr0 => -> /=.
Qed.

Lemma riscv_immediateP : immediate_correct riscv_saparams.(sap_immediate).
Proof.
  move=> P' ev s x z.
  case: x => - [] [] // [] // x xi _ /=.
  constructor.
  by rewrite /sem_sopn /= /exec_sopn /= truncate_word_u.
Qed.

Lemma riscv_swapP : swap_correct riscv_saparams.(sap_swap).
Proof.
  move=> P' ev s tag x y z w pz pw hxty hyty hzty hwty hz hw.
  constructor; rewrite /sem_sopn /= /get_gvar /= /get_var /= hz hw /=.
  rewrite /exec_sopn /= !truncate_word_u /= /write_var /set_var /=.
  rewrite hxty hyty //=.
Qed.

End STACK_ALLOC.

Definition riscv_hsaparams :
  h_stack_alloc_params (ap_sap riscv_params)  :=
  {|
    mov_ofsP := riscv_mov_ofsP;
    sap_immediateP := riscv_immediateP;
    sap_swapP := riscv_swapP;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization hypotheses. *)

Section LINEARIZATION.

(*Modifiied from ARM proof
- Changed the rewrite at the end of the proof
*)
Lemma riscv_spec_lip_allocate_stack_frame :
  allocate_stack_frame_correct riscv_liparams.
Proof.
  move=> sp_rsp tmp s ts sz htmp hget /=.
  rewrite /riscv_allocate_stack_frame.
  case: tmp htmp => [tmp [h1 h2]| _].
  + have [? [-> ? /get_varP [-> _ _]]] := [elaborate
      RISCVFopnP.smart_subi_tmp_sem_fopn_args dummy_var_info sz h1 h2 (to_word_get_var hget)
    ].
    by eexists.
  rewrite /= hget /=; t_riscv_op.
  eexists; split; first reflexivity.
  + by move=> z hz; rewrite Vm.setP_neq //; apply /eqP; SvD.fsetdec.
  by rewrite Vm.setP_eq /= wrepr_opp.
Qed.


Lemma riscv_spec_lip_free_stack_frame :
  free_stack_frame_correct riscv_liparams.
Proof.
  move=> sp_rsp tmp s ts sz htmp hget /=.
  rewrite /riscv_free_stack_frame.
  case: tmp htmp => [tmp [h1 h2]| _].
  + have [? [-> ? /get_varP [-> _ _]]] := [elaborate
      RISCVFopnP.smart_addi_tmp_sem_fopn_args dummy_var_info sz h1 h2 (to_word_get_var hget)
    ].
    by eexists.
  rewrite /= hget /=; t_riscv_op.
  eexists; split; first reflexivity.
  + by move=> z hz; rewrite Vm.setP_neq //; apply /eqP; SvD.fsetdec.
  by rewrite Vm.setP_eq vm_truncate_val_eq.
Qed.

Lemma riscv_spec_lip_set_up_sp_register :
  set_up_sp_register_correct riscv_liparams.
Proof.
Local Opaque sem_fopn_args.
  move=> [[? nrsp] vi1] [[? nr] vi2] tmp ts al sz s + /= ?? _ _ + _; subst.
  set vrsp := {| vname := nrsp |}; set rsp := {| v_var := vrsp |}.
  set vr := {| vname := nr |}; set r := {| v_var := vr |}.
  move=> hget hne.
  set vm0 := s.(evm).[r <- Vword ts].
  have [vm1 [ok_vm1 heq1 hget1]] : exists vm1, [/\
    sem_fopns_args
        (with_vm s vm0)
        (if sz != 0%Z then RISCVFopn.smart_subi rsp r sz else [::])
      = ok (with_vm s vm1),
    vm1 =[\Sv.singleton rsp] vm0 &
    get_var true vm1 rsp = ok (Vword (ts - wrepr reg_size sz))].
  + case: eqP => [->|_] /=.
    + rewrite wrepr0 GRing.subr0.
      exists vm0; split=> //.
      by t_get_var.
    have hget': get_var true vm0 r = ok (Vword ts).
    + by t_get_var.
    apply:
      (RISCVFopnP.smart_subi_sem_fopn_args _ _
        (s:= with_vm s _) (to_word_get_var hget')).
    by right; apply nesym.
  set vm2 := vm1.[rsp <- Vword (align_word al (ts - wrepr _ sz))].
  exists vm2; split.
  + rewrite (RISCVFopnP.mov_sem_fopn_args (to_word_get_var hget)) -/vm0 /=.
    rewrite -cats1 sem_fopns_args_cat ok_vm1 /=.
    by rewrite
         (RISCVFopnP.align_sem_fopn_args _ _ _
           (s:=with_vm _ _) (to_word_get_var hget1)).
  + move=> x; t_notin_add.
    t_vm_get.
    rewrite heq1 /=; last by apply /Sv_neq_not_in_singleton/nesym.
    by t_vm_get.
  + by t_get_var.
  + t_get_var.
    rewrite (get_var_eq_ex _ _ heq1) /=;
      last by apply /Sv_neq_not_in_singleton/nesym.
    by t_get_var.
  move=> x /vflagsP hxtype _.
  have [*] : [/\ vrsp <> x & vr <> x].
  - by split; apply/eqP/vtype_diff; rewrite hxtype.
  t_vm_get.
  rewrite heq1 /=; last by apply /Sv_neq_not_in_singleton.
  by t_vm_get.
Local Transparent sem_fopn_args.
Qed.

Lemma riscv_lmove_correct : lmove_correct riscv_liparams.
Proof.
  move=> xd xs w ws w' s htxd htxs hget htr.
  rewrite /riscv_liparams /lip_lmove /riscv_lmove /= hget /=.
  rewrite /exec_sopn /= htr /=.
  by rewrite set_var_eq_type ?htxd.
Qed.

Lemma riscv_lstore_correct : lstore_correct_aux riscv_check_ws riscv_lstore.
Proof.
  move=> xd xs ofs ws w wp s m htxs /eqP hchk; t_xrbindP; subst ws.
  move=> vd hgetd htrd vs hgets htrs hwr.
  rewrite /riscv_lstore /= hgets hgetd /= /exec_sopn /= htrs htrd /= !truncate_word_u /=.
  by rewrite zero_extend_u hwr.
Qed.

Lemma riscv_smart_addi_correct : ladd_imm_correct_aux RISCVFopn.smart_addi.
Proof.
  move=> [[_ xn1] xi] x2 s w ofs /= -> hne hget.
  by apply: RISCVFopnP.smart_addi_sem_fopn_args hget; right.
Qed.

Lemma riscv_lstores_correct : lstores_correct riscv_liparams.
Proof.
  apply/lstores_imm_dfl_correct.
  + by apply riscv_lstore_correct.
  apply riscv_smart_addi_correct.
Qed.

Lemma riscv_lload_correct : lload_correct_aux (lip_check_ws riscv_liparams) riscv_lload.
Proof.
  move=> xd xs ofs ws top s w vm heq hcheck hgets hread hset.
  move/eqP: hcheck => ?; subst ws.
  rewrite /riscv_lload /= hgets /= truncate_word_u /= hread /=.
  by rewrite /exec_sopn /= truncate_word_u /= sign_extend_u hset.
Qed.

Lemma riscv_lloads_correct : lloads_correct riscv_liparams.
Proof.
  apply/lloads_imm_dfl_correct.
  + by apply riscv_lload_correct.
  apply riscv_smart_addi_correct.
Qed.

Lemma riscv_tmp_correct : lip_tmp riscv_liparams <> lip_tmp2 riscv_liparams.
Proof. by move=> h; assert (h1 := inj_to_ident h). Qed.

Lemma riscv_check_ws_correct : lip_check_ws riscv_liparams Uptr.
Proof. done. Qed.

End LINEARIZATION.

Definition riscv_hliparams :
  h_linearization_params (ap_lip riscv_params) :=
  {|
    spec_lip_allocate_stack_frame := riscv_spec_lip_allocate_stack_frame;
    spec_lip_free_stack_frame     := riscv_spec_lip_free_stack_frame;
    spec_lip_set_up_sp_register   := riscv_spec_lip_set_up_sp_register;
    spec_lip_lmove                := riscv_lmove_correct;
    spec_lip_lstore               := riscv_lstore_correct;
    spec_lip_lload                := riscv_lload_correct;
    spec_lip_lstores              := riscv_lstores_correct;
    spec_lip_lloads               := riscv_lloads_correct;
    spec_lip_tmp                  := riscv_tmp_correct;
    spec_lip_check_ws             := riscv_check_ws_correct;
  |}.

Lemma riscv_ok_lip_tmp :
  exists r : reg_t, of_ident (lip_tmp (ap_lip riscv_params)) = Some r.
Proof. exists X28; exact: to_identK. Qed.

Lemma riscv_ok_lip_tmp2 :
  exists r : reg_t, of_ident (lip_tmp2 (ap_lip riscv_params)) = Some r.
Proof. exists X29; exact: to_identK. Qed.

(* ------------------------------------------------------------------------ *)
(* Lowering hypotheses. *)

Lemma riscv_lower_callP
  { dc : DirectCall }
  (pT : progT)
  (sCP : semCallParams)
  (p : prog)
  (ev : extra_val_t)
  (options : lowering_options)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars)
  (_ : lop_fvars_correct riscv_loparams fv (p_funcs p))
  (f : funname)
  scs mem scs' mem'
  (va vr : seq value) :
  psem.sem_call p ev scs mem f va scs' mem' vr
  -> let lprog :=
       lowering.lower_prog
         (lop_lower_i riscv_loparams)
         options
         warning
         fv
         p
     in
     psem.sem_call lprog ev scs mem f va scs' mem' vr.
Proof.
  exact: lower_callP.
Qed.

Definition riscv_hloparams { dc : DirectCall } : h_lowering_params (ap_lop riscv_params) :=
  {|
    hlop_lower_callP := riscv_lower_callP;
  |}.

(* ------------------------------------------------------------------------ *)
(* Lowering of complex addressing mode for RISC-V *)

Lemma riscv_hlaparams : h_lower_addressing_params (ap_lap riscv_params).
Proof.
  split=> /=.
  + exact: (lower_addressing_prog_invariants (pT:=progStack)).
  + exact: (lower_addressing_fd_invariants (pT:=progStack)).
  exact: (lower_addressing_progP (pT:=progStack)).
Qed.

(* ------------------------------------------------------------------------ *)
(* Assembly generation hypotheses. *)

Section ASM_GEN.

Notation assemble_extra_correct :=
  (assemble_extra_correct riscv_agparams) (only parsing).

(* FIXME: the following line fixes type inference with Coq 8.16 *)
Local Instance the_asm : asm _ _ _ _ _ _ := _.

(* TODO: move *)
Lemma negb_wlt ws sg (w1 w2 : word ws) : ~~ (wlt sg w1 w2) = wle sg w2 w1.
Proof. by case: sg => /=; rewrite -Z.leb_antisym. Qed.

Lemma condt_notP rf c b :
  riscv_eval_cond rf c = ok b
  -> riscv_eval_cond rf (condt_not c) = ok (negb b).
Proof.
  case: c => c x y.
  case: c => [| | sg | sg]; rewrite /riscv_eval_cond /= => -[<-] //.
  + by rewrite negbK.
  + by rewrite negb_wlt.
  by rewrite -negb_wlt negbK.
Qed.

(* copied from arm_params_proof *)
Lemma eval_assemble_cond_Onot get c v v0 v1 :
  value_of_bool (riscv_eval_cond (get) c) = ok v1
  -> value_uincl v0 v1
  -> sem_sop1 Onot v0 = ok v
  -> exists2 v',
       value_of_bool (riscv_eval_cond (get) (condt_not c)) = ok v'
       & value_uincl v v'.
Proof.
  Opaque riscv_eval_cond.
  move=> hv1 hincl.
  move=> /sem_sop1I /= [b hb ?]; subst v.

  have hc := value_uincl_to_bool_value_of_bool hincl hb hv1.
  clear v0 v1 hincl hb hv1.

  rewrite (condt_notP hc) {hc}.
  by eexists.
  Transparent riscv_eval_cond.
Qed.

Lemma assemble_cond_argP ii e or vm v rr :
  (forall r, value_uincl vm.[to_var r] (Vword (rr r))) ->
  assemble_cond_arg ii e = ok or ->
  sem_fexpr vm e = ok v ->
  value_uincl v (Vword (sem_cond_arg rr or)).
Proof.
  move=> eqr.
  case: e => //=.
  + t_xrbindP=> _ r /of_var_eI <- <- /get_varP [-> _ _] /=.
    by apply eqr.
  by move=> [] // [] // [] // [] // [<-] /= [<-].
Qed.

Lemma assemble_cond_app2P_aux ck v1 v2 op2 v w1 w2 :
  sem_sop2 op2 v1 v2 = ok v ->
  value_uincl v1 (Vword w1) ->
  value_uincl v2 (Vword w2) ->
  forall (eq1 : type_of_op2 op2 = (sword U32, sword U32, sbool)),
  ecast t (let t := t in _) eq1 (sem_sop2_typed op2) w1 w2 = ok (sem_cond_kind ck w1 w2) ->
  value_uincl v (Vbool (sem_cond_kind ck w1 w2)).
Proof.
  move=> ok_v hincl1 hincl2 eq1.
  move: ok_v.
  rewrite /sem_sop2; move: (sem_sop2_typed op2).
  rewrite -> eq1 => /= sem_sop2_typed ok_v.

  move: ok_v.
  t_xrbindP=> _ /to_wordI' [ws1 [w1' [hcmp1 ? ->]]]
              _ /to_wordI' [ws2 [w2' [hcmp2 ? ->]]]; subst.
  move: hincl1 hincl2 => /= /andP [hcmp1' /eqP ->{w1'}] /andP [hcmp2' /eqP ->{w2'}].
  have ? := cmp_le_antisym hcmp1 hcmp1'.
  have ? := cmp_le_antisym hcmp2 hcmp2'; subst.
  rewrite !zero_extend_u.
  by move=> _ -> <- [->].
Qed.

Lemma assemble_cond_app2P op2 ck swap v1 v2 v w1 w2 :
  assemble_cond_app2 op2 = Some (ck, swap) ->
  sem_sop2 op2 v1 v2 = ok v ->
  value_uincl v1 (Vword w1) ->
  value_uincl v2 (Vword w2) ->
  let: (w1, w2) := if swap then (w2, w1) else (w1, w2) in
  value_uincl v (Vbool (sem_cond_kind ck w1 w2)).
Proof.
  case: op2 => //=.
  + move=> [] // [] // [<- <-] ok_v hincl1 hincl2.
    by apply: (assemble_cond_app2P_aux ok_v hincl1 hincl2).
  + move=> [] // [] // [<- <-] ok_v hincl1 hincl2.
    by apply: (assemble_cond_app2P_aux ok_v hincl1 hincl2).
  + move=> [] // sg [] // [<- <-] ok_v hincl1 hincl2.
    by apply: (assemble_cond_app2P_aux ok_v hincl1 hincl2).
  + move=> [] // sg [] // [<- <-] ok_v hincl1 hincl2.
    have {}ok_v: sem_sop2 (Oge (Cmp_w sg U32)) v2 v1 = ok v.
    + by move: ok_v; rewrite /sem_sop2 /=; t_xrbindP=> _ -> _ -> /= ->.
    by apply: (assemble_cond_app2P_aux ok_v hincl2 hincl1).
  + move=> [] // sg [] // [<- <-] ok_v hincl1 hincl2.
    have {}ok_v: sem_sop2 (Olt (Cmp_w sg U32)) v2 v1 = ok v.
    + by move: ok_v; rewrite /sem_sop2 /=; t_xrbindP=> _ -> _ -> /= ->.
    by apply: (assemble_cond_app2P_aux ok_v hincl2 hincl1).
  move=> [] // sg [] // [<- <-] ok_v hincl1 hincl2.
  by apply: (assemble_cond_app2P_aux ok_v hincl1 hincl2).
Qed.

Lemma riscv_eval_assemble_cond : assemble_cond_spec riscv_agparams.
Proof.
  move=> ii m rr _ e c v eqr _ ok_c ok_v /=.
  eexists; first by reflexivity.
  elim: e c ok_c v ok_v => [| | op1 e hind | op2 e1 _ e2 _ |] //=.

  - case: op1 => //.
    t_xrbindP=> _ c ok_c <- v v1 ok_v ok_v1.
    have hincl := hind _ ok_c _ ok_v.
    by have [_ [<-] ?] := eval_assemble_cond_Onot erefl hincl ok_v1.

  t_xrbindP=> c [ck b] /o2rP hop2.
  t_xrbindP=> arg1 ok_arg1 arg2 ok_arg2 ok_c v v1 ok_v1 v2 ok_v2 ok_v.
  have hincl1 := assemble_cond_argP eqr ok_arg1 ok_v1.
  have hincl2 := assemble_cond_argP eqr ok_arg2 ok_v2.
  have {hop2} := assemble_cond_app2P hop2 ok_v hincl1 hincl2.
  by case: b ok_c => -[<-].
Qed.

(* TODO_RISCV: Is there a way of avoiding importing here? *)
Import arch_sem.

Lemma sem_sopns_fopns_args s lc :
  sem_sopns s [seq (None, o, d, e) | '(d, o, e) <- lc] =
  sem_fopns_args s (map RISCVFopn.to_opn lc).
Proof.
  elim: lc s => //= -[[xs o] es ] lc ih s.
  rewrite /sem_fopn_args /sem_sopn_t /=; case: sem_rexprs => //= >.
  by rewrite /exec_sopn /= /sopn_sem /Oriscv; case: i_valid => //=; case : app_sopn => //= >; case write_lexprs.
Qed.

Lemma assemble_swap_correct ws : assemble_extra_correct (SWAP ws).
Proof.
  move=> rip ii lvs args m xs ys m' s ops ops' /=.
  case: eqP => // -> {ws}.
  case: lvs => // -[] // x [] // -[] // y [] //.
  case: args => // -[] // [] // z [] // [] // [] // w [] //=.
  t_xrbindP => vz hz _ vw hw <- <-.
  rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /= /swap_semi.
  t_xrbindP => /= _ wz hvz ww hvw <- <- /=.
  t_xrbindP.
  t_xrbindP => _ vm1 /set_varP [_ htrx ->] <- _ vm2 /set_varP [_ htry ->] <- <- /eqP hxw /eqP hyx
    /and4P [/eqP hxt /eqP hyt /eqP hzt /eqP hwt] <-.
  move=> hmap hlom.
  have h := (assemble_opsP riscv_eval_assemble_cond hmap erefl _ hlom).
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
  assemble_extra_correct Oriscv_add_large_imm.
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
  have := RISCVFopnP.smart_addi_sem_fopn_args xi (y:= y) (or_intror _ hne) (to_word_get_var hvy).
  move=> /(_ _ imm) [vm []]; rewrite -sem_sopns_fopns_args => hsem heqex /get_varP [hvmx _ _].
  have [] := (assemble_opsP riscv_eval_assemble_cond hmap _ hsem hlom).
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
  by apply heqex; rewrite /riscv_reg_size; SvD.fsetdec.
Qed.

Lemma riscv_assemble_extra_op op : assemble_extra_correct op.
Proof.
  case: op.
  + exact: assemble_swap_correct.
  exact: assemble_add_large_imm_correct.
Qed.

Definition riscv_hagparams : h_asm_gen_params (ap_agp riscv_params) :=
  {|
    hagp_eval_assemble_cond := riscv_eval_assemble_cond;
    hagp_assemble_extra_op := riscv_assemble_extra_op;
  |}.

End ASM_GEN.


(* ------------------------------------------------------------------------ *)
(* Speculative execution. *)

Lemma riscv_hshp: slh_lowering_proof.h_sh_params (ap_shp riscv_params).
Proof. by constructor; move=> ???? []. Qed.


(* ------------------------------------------------------------------------ *)
(* Stack zeroization. *)

Section STACK_ZEROIZATION.

Lemma riscv_hszparams : h_stack_zeroization_params (ap_szp riscv_params).
Proof.
  split.
  + exact: riscv_stack_zero_cmd_not_ext_lbl.
  exact: riscv_stack_zero_cmdP.
Qed.

End STACK_ZEROIZATION.

(* ------------------------------------------------------------------------ *)
(* Shared hypotheses. *)

Definition riscv_is_move_opP op vx v :
  ap_is_move_op riscv_params op
  -> exec_sopn (Oasm op) [:: vx ] = ok v
  -> List.Forall2 value_uincl v [:: vx ].
Proof.
  case: op => //.
  move=> [[]] //.
  move=> [] //= _.
  rewrite /exec_sopn /=.
  t_xrbindP=> w w'' hvx.
  have [ws' [w' [-> /truncate_wordP [hws' ->]]]] := to_wordI hvx.
  move=> [<-] <-.
  apply: List.Forall2_cons; last done.
  exact: (word_uincl_zero_ext w' hws').
Qed.


(* ------------------------------------------------------------------------ *)

Definition riscv_h_params {dc : DirectCall} : h_architecture_params riscv_params :=
  {|
    hap_hsap        := riscv_hsaparams;
    hap_hlip        := riscv_hliparams;
    ok_lip_tmp      := riscv_ok_lip_tmp;
    ok_lip_tmp2     := riscv_ok_lip_tmp2;
    hap_hlop        := riscv_hloparams;
    hap_hlap        := riscv_hlaparams;
    hap_hagp        := riscv_hagparams;
    hap_hshp        := riscv_hshp;
    hap_hszp        := riscv_hszparams;
    hap_is_move_opP := riscv_is_move_opP;
  |}.

End Section.
