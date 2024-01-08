From Coq Require Import Relations.
From Coq Require Import Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
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

Context
  (P' : sprog)
  (P'_globs : p_globs P' = [::]).

End STACK_ALLOC.

Lemma arm_mov_ofsP {dc : DirectCall} (P': sprog) s1 e i x tag ofs w vpk s2 ins :
  p_globs P' = [::]
  -> (Let i' := sem_pexpr true [::] s1 e in to_pointer i') = ok i
  -> sap_mov_ofs arm_saparams x tag vpk e ofs = Some ins
  -> write_lval true [::] x (Vword (i + wrepr Uptr ofs)) s1 = ok s2
  -> psem.sem_i (pT := progStack) P' w s1 ins s2.
Proof.
  rewrite /sap_mov_ofs /= /arm_mov_ofs => P'_globs.
  t_xrbindP => z ok_z ok_i.
  case: (mk_mov vpk).
  + move => /Some_inj <-{ins} hx; constructor.
    rewrite /sem_sopn /= P'_globs /exec_sopn.
    case: eqP hx.
    - by move => -> {ofs}; rewrite wrepr0 GRing.addr0 ok_z /= ok_i /= => ->.
    by move => _ hx; rewrite /= /sem_sop2 ok_z /= ok_i /= truncate_word_u /= ?truncate_word_u /= hx.
  case: x => //.
  + move=> x_; move: (Lvar x_) => x.
    case: ifP; case: eqP => [-> | _ ] _ // /Some_inj <-{ins} hx; constructor.
    + rewrite /sem_sopn /= P'_globs /exec_sopn ok_z /= ok_i /= zero_extend_u.
      by move: hx; rewrite wrepr0 GRing.addr0 => ->.
    + rewrite /sem_sopn /= P'_globs /exec_sopn ok_z /= ok_i /=.
      by move: hx; rewrite wrepr0 GRing.addr0 => ->.
    by rewrite /sem_sopn /= P'_globs /exec_sopn /sem_sop2 /= ok_z /= ok_i /= truncate_word_u /= ?truncate_word_u /= hx.
  move=> ws_ x_ e_; move: (Lmem ws_ x_ e_) => {ws_ x_ e_} x.
  case: eqP => [-> | _ ] // /Some_inj <-{ins} hx; constructor.
  rewrite /sem_sopn /= P'_globs /exec_sopn ok_z /= ok_i /= zero_extend_u.
  by move: hx; rewrite wrepr0 GRing.addr0 => ->.
Qed.

Lemma arm_immediateP {dc : DirectCall} (P': sprog) w s (x: var_i) z :
  vtype x = sword Uptr
  -> psem.sem_i (pT := progStack) P' w s (arm_immediate x z) (with_vm s (evm s).[x <- Vword (wrepr Uptr z)]).
Proof.
  case: x => - [] [] // [] // x xi _ /=.
  constructor.
  by rewrite /sem_sopn /= /exec_sopn /= truncate_word_u.
Qed.

Definition arm_hsaparams {dc : DirectCall} :
  h_stack_alloc_params (ap_sap arm_params)  :=
  {|
    mov_ofsP := arm_mov_ofsP;
    sap_immediateP := arm_immediateP;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization hypotheses. *)

Section LINEARIZATION.

Lemma arm_spec_lip_allocate_stack_frame :
  allocate_stack_frame_correct arm_liparams.
Proof.
  move=> *.
  apply: ARMFopnP.subi_eval_instr.
  rewrite /get_var.
  by t_simpl_rewrites.
Qed.

Lemma arm_spec_lip_free_stack_frame :
  free_stack_frame_correct arm_liparams.
Proof.
  move=> *.
  apply: ARMFopnP.addi_eval_instr.
  rewrite /get_var.
  by t_simpl_rewrites.
Qed.

Lemma arm_spec_lip_set_up_sp_register :
  set_up_sp_register_correct arm_liparams.
Proof.
  move=> lp sp_rsp ls r ts al sz P Q.
  set ts' := align_word _ _.
  move: r => [[rtype rname] rinfo] /=.
  set r := {| v_info := rinfo; |}.
  set vtmp := {| vname := arm_tmp; |}.
  set vtmpi := mk_var_i vtmp.
  set vrsp := {| vname := sp_rsp; |}.
  set vrspi := mk_var_i vrsp.
  move=>
    /oassertP_isSome [hset_up _]
    hbody hpc hneq_tmp_rsp hgetrsp ? hnot_saved_stack hneq_r_rsp;
    subst rtype.

  have hneq_r_tmp :
    v_var r <> vtmp.
  - move=> [h]. move: hnot_saved_stack. by rewrite mem_seq1 h eqxx.
  clear hnot_saved_stack.

  move: hbody.
  rewrite /set_up_sp_register /= /arm_set_up_sp_register hset_up /= -/vtmpi.
  rewrite map_cat.
  rewrite -catA /=.
  set cmd_large_subi := _ _ (ARMFopn.smart_subi _ _ _).
  set i_mov_r := _ _ (ARMFopn.mov _ _).
  set i_align_tmp := _ _ (ARMFopn.align _ _ _).
  set i_mov_rsp := _ _ (ARMFopn.mov _ _).
  rewrite -[i_mov_r :: _]/([:: i_mov_r ] ++ _).
  rewrite catA.
  move=> hbody.

  (* We need [vm1] before [eexists]. *)
  set vm0 := (lvm ls).[v_var r <- Vword ts].

  have hsz : (0 <= sz < wbase reg_size)%Z.
  - by move: hset_up => /andP [] /ZleP hlo /ZltP hhi.
  clear hset_up.

  have hgetrsp0 :
    get_var true vm0 vrsp = ok (Vword ts).
  - rewrite get_var_neq; first exact: hgetrsp. exact: hneq_r_rsp.

  set ls0 := lnext_pc (lset_vm ls vm0).
  have [|vm1 [hsem hvm1 hgettmp1]] :=
    ARMFopnP.smart_subi_lsem (ls := ls0) hbody _ erefl hneq_tmp_rsp hgetrsp0 hsz.
  - by rewrite size_cat addn1 -hpc.

  set vm2 := vm1.[vtmp <- Vword ts'].
  set vm3 := vm2.[vrsp <- Vword ts'].

  exists vm3; split.

  - apply: lsem_step.

    (* R[r] := R[rsp]; *)
    + rewrite -catA in hbody.
      apply: (eval_lsem1 hbody) => //.
      exact: (ARMFopnP.mov_eval_instr (y := vrspi) hgetrsp).

    (* R[tmp] := R[rsp] - off; *)
    apply: (lsem_trans hsem).
    clear hsem.

    apply: lsem_step2.
    (* R[tmp] := R[tmp] & alignment; *)
    + rewrite catA in hbody.
      apply: (eval_lsem1 hbody) => //;
        first by rewrite !size_cat.
      set ls1 := setpc (lset_vm _ _) _.
      exact: (ARMFopnP.align_eval_instr (ls := ls1) (y := vtmpi) hgettmp1).

    (* R[rsp] := R[tmp]; *)
    + rewrite -(cat1s i_align_tmp) 2!catA in hbody.
      apply: (eval_lsem1 hbody) => //;
        first by rewrite !size_cat !addn1 /=.

      have hgettmp2 :
        get_var true vm2 vtmp = ok (Vword ts').
      * by rewrite get_var_eq.

      set ls2 := lnext_pc (lset_vm _ _).
      rewrite (ARMFopnP.mov_eval_instr (ls := ls2) (y := vtmpi) hgettmp2).
      rewrite /lnext_pc /setpc /= !size_cat /= !size_map /addn /addn_rec.
      repeat f_equal.
      lia.

  - move=> x.
    t_notin_add.
    t_vm_get.
    rewrite hvm1; first by t_vm_get.
    apply: Sv_neq_not_in_singleton.
    by apply/nesym.

  - by t_get_var.

  - t_get_var.
    rewrite (get_var_eq_ex _ _ hvm1); first by t_get_var.
    apply: Sv_neq_not_in_singleton.
    by apply/nesym.

  rewrite /= -/vm3.
  move=> x hx _.
  move: hx => /vflagsP hxtype.

  have ? : v_var r <> x.
  - apply/eqP. apply: vtype_diff. by rewrite hxtype.

  have ? : vrsp <> x.
  - apply/eqP. apply: vtype_diff. by rewrite hxtype.

  have ? : vtmp <> x.
  - apply/eqP. apply: vtype_diff. by rewrite hxtype.

  t_vm_get.
  rewrite hvm1 /=; first by t_vm_get.
  by apply: Sv_neq_not_in_singleton.
Qed.

Lemma arm_spec_lip_set_up_sp_stack :
  set_up_sp_stack_correct arm_liparams.
Proof.
  move=> lp sp_rsp ls ts m' al sz off P Q.
  set ts' := align_word _ _.
  move=> /oassertP_isSome [hset_up _] hbody hpc hneq_tmp_rsp hgetrsp hwrite.

  move: hbody.
  set vtmp := {| vname := arm_tmp; |}.
  set vtmpi := mk_var_i vtmp.
  set vrsp := {| vname := sp_rsp; |}.
  set vrspi := mk_var_i vrsp.
  rewrite /set_up_sp_stack /= /arm_set_up_sp_stack hset_up /= -/vtmpi.
  rewrite map_cat /=.
  set cmd_large_subi := map _ (ARMFopn.smart_subi _ _ _).
  set i_align_tmp := li_of_fopn_args _ (ARMFopn.align _ _ _).
  set i_str_rsp := li_of_fopn_args _ (ARMFopn.str _ _ _).
  set i_mov_rsp := li_of_fopn_args _ (ARMFopn.mov _ _).
  rewrite -catA.
  move=> hbody.

  have hsz : (0 <= sz < wbase reg_size)%Z.
  - by move: hset_up => /andP [] /ZleP hlo /ZltP hhi.
  clear hset_up.

  (* We need [vm0] before [eexists]. *)
  have [vm0 [hsem hvm0 hgettmp0]] :=
    ARMFopnP.smart_subi_lsem hbody hpc erefl hneq_tmp_rsp hgetrsp hsz.
  set vm1 := vm0.[vtmp <- Vword ts'].
  set vm2 := vm1.[vrsp <- Vword ts'].

  have hgetrsp1 :
    get_var true vm1 vrsp = ok (Vword ts).
  * rewrite get_var_neq; last exact: hneq_tmp_rsp.
    rewrite (get_var_eq_ex _ _ hvm0); first exact: hgetrsp.
    exact: (Sv_neq_not_in_singleton hneq_tmp_rsp).

  have hgettmp1 :
    get_var true vm1 vtmp = ok (Vword ts').
  * by rewrite get_var_eq.

  eexists; split.

  (* R[tmp] := R[rsp] - off; *)
  - apply: (lsem_trans hsem).
    apply: lsem_step3.

    (* R[tmp] := R[tmp] & alignment; *)
    + rewrite catA in hbody.
      apply: (eval_lsem1 hbody) => //;
        first by rewrite size_cat.
      set ls0 := setpc (lset_vm _ _) _.
      exact: (ARMFopnP.align_eval_instr (ls := ls0) (y := vtmpi) hgettmp0).

    (* M[R[rsp]] := R[tmp]; *)
    + rewrite -(cat1s i_align_tmp) -!catA 2!catA in hbody.
      apply: (eval_lsem1 hbody) => //;
        first by rewrite !size_cat /= addn1.
      set ls1 := lnext_pc (lset_vm _ _).
      apply:
        (ARMFopnP.str_eval_instr (ls := ls1) (y := vrspi) hgettmp1 hgetrsp1).
      exact: hwrite.

    (* R[rsp] := R[tmp]; *)
    + rewrite -(cat1s i_align_tmp) -(cat1s i_str_rsp) -!catA 3!catA in hbody.
      apply: (eval_lsem1 hbody) => //;
        first by rewrite !size_cat /= !addn1.
      set ls2 := lnext_pc (lset_mem _ _).
      rewrite (ARMFopnP.mov_eval_instr (ls := ls2) (y := vtmpi) hgettmp1).
      rewrite /ls2 !size_cat /= !addnS addn0.
      reflexivity.

  - move=> x.
    t_notin_add.
    t_vm_get.
    rewrite hvm0; first done.
    apply: Sv_neq_not_in_singleton.
    by apply/nesym.

  - by t_get_var.

  rewrite /= -/vm2.
  move=> x hx _.
  move: hx => /vflagsP hxtype.

  have ? : vrsp <> x.
  - apply/eqP. apply: vtype_diff. by rewrite hxtype.

  have ? : vtmp <> x.
  - apply/eqP. apply: vtype_diff. by rewrite hxtype.

  t_vm_get.
  rewrite hvm0 /=; first done.
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

Lemma arm_hlip_lassign :
  lassign_correct arm_liparams.
Proof.
  move=> lp fn s1 s2 x e args ws ws' w w' hlassign hseme htrunc hwrite.
  move: hlassign.
  apply: obindP => -[mn' re].
  case: x hwrite => [??? | x] /= hwrite.

  - apply: obindP => mn hmn [??] [?]; subst mn' re args.
    rewrite /eval_instr /= /sem_sopn /= hseme {hseme} /=.
    by rewrite (store_mn_of_wsizeP hmn htrunc) /= hwrite.

  move=> /oassertP [/eqP ?]; subst ws.
  case: e hseme => [ ??? | ]; last case => //; last case => // - [] // [] // z.
  2: move=> e.
  all: move=> /= hseme [??] [?]; subst mn' re args.
  all: rewrite /eval_instr /= /sem_sopn /= /exec_sopn.
  - by rewrite hseme /= htrunc /= zero_extend_u hwrite.
  - by rewrite hseme /= htrunc /= hwrite.

  case/ok_inj/Vword_inj: hseme => ?; subst => /= ?; subst.
  move: htrunc; rewrite truncate_word_u => /ok_inj ?; subst.
  by rewrite /= hwrite.
Qed.

End LINEARIZATION.

Definition arm_hliparams :
  h_linearization_params (ap_lip arm_params) :=
  {|
    spec_lip_allocate_stack_frame := arm_spec_lip_allocate_stack_frame;
    spec_lip_free_stack_frame := arm_spec_lip_free_stack_frame;
    spec_lip_set_up_sp_register := arm_spec_lip_set_up_sp_register;
    spec_lip_set_up_sp_stack := arm_spec_lip_set_up_sp_stack;
    hlip_lassign := arm_hlip_lassign;
  |}.

Lemma arm_ok_lip_tmp :
  exists r : reg_t, of_ident (lip_tmp (ap_lip arm_params)) = Some r.
Proof.
  exists R12.
  rewrite /=.
  change arm_tmp with (to_ident R12).
  exact: to_identK.
Qed.

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
  eval_cond (get_rf rf) (condt_of_rflag r) = to_bool (of_rbool (rf r)).
Proof.
  rewrite -get_rf_to_bool_of_rbool. by case: r.
Qed.

Lemma condt_notP rf c b :
  eval_cond rf c = ok b
  -> eval_cond rf (condt_not c) = ok (negb b).
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
  -> eval_cond rf c0 = ok b0
  -> eval_cond rf c1 = ok b1
  -> eval_cond rf c = ok (b0 && b1).
Proof.
  move: c0 c1 => [] [] //.
  all: move=> [?]; subst c.
  all: rewrite /eval_cond /=.

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
  -> eval_cond rf c0 = ok b0
  -> eval_cond rf c1 = ok b1
  -> eval_cond rf c = ok (b0 || b1).
Proof.
  move: c0 c1 => [] [] //.
  all: move=> [?]; subst c.
  all: rewrite /eval_cond /=.

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
       value_of_bool (eval_cond (get_rf rf) (condt_of_rflag r)) = ok v'
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
  value_of_bool (eval_cond (get_rf rf) c) = ok v1
  -> value_uincl v0 v1
  -> sem_sop1 Onot v0 = ok v
  -> exists2 v',
       value_of_bool (eval_cond (get_rf rf) (condt_not c)) = ok v'
       & value_uincl v v'.
Proof.
  move=> hv1 hincl.
  move=> /sem_sop1I /= [b hb ?]; subst v.

  have hc := value_uincl_to_bool_value_of_bool hincl hb hv1.
  clear v0 v1 hincl hb hv1.

  change arm.eval_cond with eval_cond.
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
       value_of_bool (eval_cond (get_rf rf) GE_ct) = ok v' & value_uincl v v'.
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
  -> value_of_bool (eval_cond (get_rf rf) c0) = ok v0'
  -> value_uincl v0 v0'
  -> value_of_bool (eval_cond (get_rf rf) c1) = ok v1'
  -> value_uincl v1 v1'
  -> sem_sop2 Oand v0 v1 = ok v
  -> exists2 v',
       value_of_bool (eval_cond (get_rf rf) c) = ok v' & value_uincl v v'.
Proof.
  move=> hand hv0' hincl0 hv1' hincl1.
  move=> /sem_sop2I /= [b0 [b1 [b [hb0 hb1 hb ?]]]]; subst v.

  move: hb.
  rewrite /mk_sem_sop2 /=.
  move=> [?]; subst b.

  have hc0 := value_uincl_to_bool_value_of_bool hincl0 hb0 hv0'.
  have hc1 := value_uincl_to_bool_value_of_bool hincl1 hb1 hv1'.
  clear hincl0 hb0 hv0' hincl1 hb1 hv1'.

  change arm.eval_cond with eval_cond.
  rewrite (condt_andP hand hc0 hc1) {hand hc0 hc1} /=.
  by eexists.
Qed.

Lemma eval_assemble_cond_Oor rf c c0 c1 v v0 v1 v0' v1' :
  condt_or c0 c1 = Some c
  -> value_of_bool (eval_cond (get_rf rf) c0) = ok v0'
  -> value_uincl v0 v0'
  -> value_of_bool (eval_cond (get_rf rf) c1) = ok v1'
  -> value_uincl v1 v1'
  -> sem_sop2 Oor v0 v1 = ok v
  -> exists2 v',
       value_of_bool (eval_cond (get_rf rf) c) = ok v' & value_uincl v v'.
Proof.
  move=> hor hv0' hincl0 hv1' hincl1.
  move=> /sem_sop2I /= [b0 [b1 [b [hb0 hb1 hb ?]]]]; subst v.

  move: hb.
  rewrite /mk_sem_sop2 /=.
  move=> [?]; subst b.

  have hc0 := value_uincl_to_bool_value_of_bool hincl0 hb0 hv0'.
  have hc1 := value_uincl_to_bool_value_of_bool hincl1 hb1 hv1'.
  clear hincl0 hb0 hv0' hincl1 hb1 hv1'.

  change arm.eval_cond with eval_cond.
  rewrite (condt_orP hor hc0 hc1) {hor hc0 hc1} /=.
  by eexists.
Qed.

Lemma arm_eval_assemble_cond ii m rf e c v :
  eqflags m rf
  -> agp_assemble_cond arm_agparams ii e = ok c
  -> sem_fexpr (evm m) e = ok v
  -> exists2 v',
       value_of_bool (eval_cond (get_rf rf) c) = ok v' & value_uincl v v'.
Proof.
  rewrite /=.
  elim: e c v => [| x | op1 e hind | op2 e0 hind0 e1 hind1 |] //= c v eqf.

  - t_xrbindP=> r hr hc; subst c.
    move=> hv.
    exact: (eval_assemble_cond_Pvar eqf hr hv).

  - case: op1 => //.
    t_xrbindP=> c' hc' hc; subst c.
    move=> v0 hv0 hsem.
    have [v1 hv1 hincl1] := hind _ _ eqf hc' hv0.
    clear ii m e eqf hc' hv0 hind.
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
    have [v0' hv0' hincl0] := hind0 _ _ eqf hass0 hsem0.
    have [v1' hv1' hincl1] := hind1 _ _ eqf hass1 hsem1.
    clear eqf hass0 hsem0 hind0 hass0 hsem1 hind1.
    exact: (eval_assemble_cond_Oand hand hv0' hincl0 hv1' hincl1 hsem).

  t_xrbindP=> c0 hass0 c1 hass1.
  case hor: condt_or => [c'|] // [?]; subst c'.
  move=> v0 hsem0 v1 hsem1 hsem.
  have [v0' hv0' hincl0] := hind0 _ _ eqf hass0 hsem0.
  have [v1' hv1' hincl1] := hind1 _ _ eqf hass1 hsem1.
  clear eqf hass0 hsem0 hind0 hass0 hsem1 hind1.
  exact: (eval_assemble_cond_Oor hor hv0' hincl0 hv1' hincl1 hsem).
Qed.

(* TODO_ARM: Is there a way of avoiding importing here? *)
Import arch_sem.

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
Proof. by case: op. Qed.

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
    hap_hsap := arm_hsaparams;
    hap_hlip := arm_hliparams;
    ok_lip_tmp := arm_ok_lip_tmp;
    hap_hlop := arm_hloparams;
    hap_hagp := arm_hagparams;
    hap_hshp := arm_hshp;
    hap_hszp := arm_hszparams;
    hap_is_move_opP := arm_is_move_opP;
  |}.

End Section.
