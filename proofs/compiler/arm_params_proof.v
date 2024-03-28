From Coq Require Import Relations.
From Coq Require Import Psatz.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
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
  stack_alloc_proof
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
  arm_params_common_proof
  arm_lowering
  arm_lowering_proof
  arm_stack_zeroization_proof.
Require Export arm_params.

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

(* ------------------------------------------------------------------------ *)
(* Stack alloc hypotheses. *)

Section STACK_ALLOC.

Context {dc : DirectCall} (P': sprog).

Lemma arm_mov_ofsP s1 e i x tag ofs w vpk s2 ins :
  p_globs P' = [::]
  -> (Let i' := sem_pexpr true [::] s1 e in to_pointer i') = ok i
  -> sap_mov_ofs arm_saparams x tag vpk e ofs = Some ins
  -> write_lval true [::] x (Vword (i + wrepr Uptr ofs)) s1 = ok s2
  -> exists2 vm2, psem.sem_i (pT := progStack) P' w s1 ins (with_vm s2 vm2) & evm s2 =1 vm2.
Proof.
  rewrite /sap_mov_ofs /= /arm_mov_ofs => P'_globs.
  t_xrbindP => z ok_z ok_i.
  case: (mk_mov vpk).
  + move => /Some_inj <-{ins} hx /=; exists (evm s2) => //.
    constructor.
    rewrite /sem_sopn /= P'_globs /exec_sopn with_vm_same.
    case: eqP hx.
    - by move => -> {ofs}; rewrite wrepr0 GRing.addr0 ok_z /= ok_i /= => ->.
    by move => _ hx; rewrite /= /sem_sop2 ok_z /= ok_i /= truncate_word_u /= ?truncate_word_u /= hx.
  case: x => //.
  + move=> x_; set x := Lvar x_.
    case: ifP.
    + case: eqP => [-> | _ ] _ // /Some_inj <-{ins} hx; exists (evm s2) => //.
      constructor.
      rewrite /sem_sopn /= P'_globs /exec_sopn ok_z /= ok_i /= zero_extend_u with_vm_same.
      by move: hx; rewrite /= wrepr0 GRing.addr0 => ->.
    case: eqP => [-> | _] _ .
    + move=> [<-] hx; exists (evm s2) => //.
      constructor.
      rewrite /sem_sopn /= P'_globs /exec_sopn ok_z /= ok_i /= with_vm_same.
      by move: hx; rewrite /= wrepr0 GRing.addr0 => ->.
    case: ifP => _.
    + move=> [<-] /= hx; exists (evm s2) => //.
      constructor.
      by rewrite /sem_sopn /= P'_globs /exec_sopn /sem_sop2 /= ok_z /= ok_i /= truncate_word_u /= ?truncate_word_u /= hx with_vm_same.
    case: e ok_z => // y_.
    case: and4P => // -[] /=; rewrite /x => {x}.
    case: x_ => -[] xty x_ xi /=.
    case: y_ => y_ -[] //= /eqP hxy _ /eqP ? /eqP hyty.
    rewrite /get_gvar /= => hget -[<-] hw.
    have [? _ hcomp]:= get_varP hget; subst z.
    move /to_wordI' : ok_i => [sz' [w' [hle heq ?]]]; subst i.
    move: hcomp; rewrite heq hyty /= => /compat_valE -[_ [<-] hsub].
    have ? : sz' = U32; last subst sz' xty.
    + case: sw_allowed hsub => // hle'.
      by apply: cmp_le_antisym hle.
    set x := {| v_var := _ |}.
    exists ((evm s1).[ x <- Vword (w' + wrepr _ ofs)].[y_ <- Vword w']).
    constructor.
    + rewrite /sem_sopn /= P'_globs /exec_sopn /get_gvar hget heq/= !truncate_word_u /=.
      rewrite write_var_eq_type /= -?hyty // /with_vm.
      by move/write_varP : hw => [-> _ _].
    move=> z; rewrite !Vm.setP hyty /=.
    case: eqP => hyz.
    + by subst z; rewrite (write_getP_neq _ hw) //; apply/eqP.
    case: eqP => hxz.
    + by subst z; have /write_getP_eq [_ _ ->] /= := hw; rewrite zero_extend_u.
    by rewrite (write_getP_neq _ hw) //; apply/eqP.
  move=> al ws_ x_ e_; move: (Lmem al ws_ x_ e_) => {al ws_ x_ e_} x.
  case: eqP => [-> | _ ] // /Some_inj <-{ins} hx; exists (evm s2) => //.
  constructor.
  rewrite /sem_sopn /= P'_globs /exec_sopn ok_z /= ok_i /= zero_extend_u.
  by move: hx; rewrite wrepr0 GRing.addr0 with_vm_same => ->.
Qed.

Lemma arm_immediateP w s (x: var_i) z :
  vtype x = sword Uptr
  -> psem.sem_i (pT := progStack) P' w s (arm_immediate x z) (with_vm s (evm s).[x <- Vword (wrepr Uptr z)]).
Proof.
  case: x => - [] [] // [] // x xi _ /=.
  constructor.
  by rewrite /sem_sopn /= /exec_sopn /= truncate_word_u.
Qed.

Lemma arm_swapP rip s tag (x y z w : var_i) (pz pw: pointer):
  vtype x = spointer -> vtype y = spointer ->
  vtype z = spointer -> vtype w = spointer ->
  (evm s).[z] = Vword pz ->
  (evm s).[w] = Vword pw ->
  psem.sem_i (pT := progStack) P' rip s (arm_swap tag x y z w)
       (with_vm s ((evm s).[x <- Vword pw]).[y <- Vword pz]).
Proof.
  move=> hxty hyty hzty hwty hz hw.
  constructor; rewrite /sem_sopn /= /get_gvar /= /get_var /= hz hw /=.
  rewrite /exec_sopn /= !truncate_word_u /= /write_var /set_var /=.
  rewrite hxty hyty //=.
Qed.

End STACK_ALLOC.

Definition arm_hsaparams {dc : DirectCall} :
  h_stack_alloc_params (ap_sap arm_params)  :=
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
  rewrite /arm_lstore /= hgets hgetd /= /exec_sopn /= htrs htrd /= !truncate_word_u /=.
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
  move=> xd xs ofs s vm top hgets.
  case heq: vtype => [|||ws] //; t_xrbindP.
  move=> _ <- /eqP ? w hread hset; subst ws.
  rewrite /arm_lload /= hgets /= truncate_word_u /= hread /=.
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

Lemma arm_lower_callP
  { dc : DirectCall }
  (pT : progT)
  (sCP : semCallParams)
  (p : prog)
  (ev : extra_val_t)
  (options : lowering_options)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars)
  (_ : lop_fvars_correct arm_loparams fv (p_funcs p))
  (f : funname)
  scs mem scs' mem'
  (va vr : seq value) :
  psem.sem_call p ev scs mem f va scs' mem' vr
  -> let lprog :=
       lowering.lower_prog
         (lop_lower_i arm_loparams)
         options
         warning
         fv
         p
     in
     psem.sem_call lprog ev scs mem f va scs' mem' vr.
Proof.
  exact: lower_callP.
Qed.

Definition arm_hloparams { dc : DirectCall } : h_lowering_params (ap_lop arm_params) :=
  {|
    hlop_lower_callP := arm_lower_callP;
  |}.

(* ------------------------------------------------------------------------ *)
(* Assembly generation hypotheses. *)

Section ASM_GEN.

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
  move=> /sem_sop1I /= [b hb ?]; subst v.

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
  by rewrite /exec_sopn /= /Oarm; case : app_sopn => //= >; case write_lexprs.
Qed.

Lemma arm_assemble_extra_op rip ii op lvs args m xs ys m' s ops ops' :
  sem_rexprs m args = ok xs
  -> exec_sopn (Oasm (ExtOp op)) xs = ok ys
  -> write_lexprs lvs ys m = ok m'
  -> to_asm ii op lvs args = ok ops
  -> mapM (fun '(op0, ls, rs) => assemble_asm_op arm_agparams rip ii op0 ls rs) ops = ok ops'
  -> lom_eqv rip m s
  -> exists2 s' : asmmem,
       foldM (fun '(op'', asm_args) => [eta eval_op op'' asm_args]) s ops' = ok s' &
       lom_eqv rip m' s'.
Proof.
  case: op => /=.
  + move=> w; case: eqP => // -> {w}.
    case: lvs => // -[] // x [] // -[] // y [] //.
    case: args => // -[] // [] // z [] // [] // [] // w [] //=.
    t_xrbindP => vz hz _ vw hw <- <-.
    rewrite /exec_sopn /= /sopn_sem /= /swap_semi.
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
  case: lvs => // -[] // [[xt xn] xi] [] // [] // [[yt yn] yi] [] //.
  set y := {|v_info := yi|}.
  case: args => // -[] // [] // y' [] // [] // [] // [] // w [] // imm [] //=.
  t_xrbindP => vy hvy <-.
  rewrite /exec_sopn /= /sopn_sem /=; t_xrbindP => /= -[ n1 n2] w1 hw1 w2 hw2 [??] <- /=; subst n1 n2.
  t_xrbindP => _ vm1 hsetx <- /= _ vm2 hsety <- <- /andP[] /eqP hne /eqP heq.
  move=> /andP []/eqP ? /andP [] /eqP ? _ <- hmap hlom; subst xt yt.
  rewrite -heq in hvy.
  move/to_wordI: hw1 => [ws [w' [?]]] /truncate_wordP [hle1 ?]; subst vy w1.
  move/get_varP: (hvy) => [_ _ /compat_valE] /= [_ [] <- hle2].
  have ? := cmp_le_antisym hle1 hle2; subst ws => {hle1 hle2}.
  have := ARMFopnP.smart_addi_sem_fopn_args xi (y:= y) (or_intror _ hne) (to_word_get_var hvy).
  move=> /(_ _ imm) [vm []]; rewrite -sem_sopns_fopns_args => hsem heqex /get_varP [hvmx _ _].
  have [] := (assemble_opsP arm_eval_assemble_cond hmap _ hsem hlom).
  + by rewrite all_map; apply/allT => -[[]].
  move=> s' -> hlo; exists s' => //.
  apply: lom_eqv_ext hlo => z /=.
  move/get_varP: hvy => -[hvmy _ _].
  move: hsety hsetx; rewrite !set_var_eq_type // => -[<-] [<-].
  rewrite !Vm.setP; case: eqP => heqy.
  + subst z; rewrite /= heqex /arm_reg_size; last by SvD.fsetdec.
    by rewrite -hvmy zero_extend_u.
  case: eqP => heqx.
  + rewrite -heqx -hvmx zero_extend_u /=.
    move: hw2 => /truncate_wordP [? ].
    by rewrite zero_extend_wrepr // => ->.
  by apply heqex; rewrite /arm_reg_size; SvD.fsetdec.
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
  case: op => //.
  move=> [[]] //.
  move=> [] //.
  move=> [] //.
  move=> [[] [] [?|]] _ //.
  rewrite /exec_sopn /=.
  t_xrbindP=> w w'' hvx.
  have [ws' [w' [-> /truncate_wordP [hws' ->]]]] := to_wordI hvx.
  move=> [<-] <-.
  apply: List.Forall2_cons; last done.
  exact: (word_uincl_zero_ext w' hws').
Qed.


(* ------------------------------------------------------------------------ *)

Definition arm_h_params {dc : DirectCall} : h_architecture_params arm_params :=
  {|
    hap_hsap        := arm_hsaparams;
    hap_hlip        := arm_hliparams;
    ok_lip_tmp      := arm_ok_lip_tmp;
    ok_lip_tmp2     := arm_ok_lip_tmp2;
    hap_hlop        := arm_hloparams;
    hap_hagp        := arm_hagparams;
    hap_hshp        := arm_hshp;
    hap_hszp        := arm_hszparams;
    hap_is_move_opP := arm_is_move_opP;
  |}.

End Section.
