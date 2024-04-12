From Coq Require Import Relations.
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
  riscv_decl
  riscv_extra
  riscv_instr_decl
  riscv
  riscv_params_common_proof
  riscv_lowering
  riscv_lowering_proof
  riscv_stack_zeroization_proof.
Require Export riscv_params.

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

Lemma riscv_mov_ofsP s1 e i x tag ofs w vpk s2 ins :
  p_globs P' = [::]
  -> (Let i' := sem_pexpr true [::] s1 e in to_pointer i') = ok i
  -> sap_mov_ofs riscv_saparams x tag vpk e ofs = Some ins
  -> write_lval true [::] x (Vword (i + wrepr Uptr ofs)) s1 = ok s2
  -> exists2 vm2, psem.sem_i (pT := progStack) P' w s1 ins (with_vm s2 vm2) & evm s2 =1 vm2.
Proof.
  rewrite /sap_mov_ofs /= /riscv_mov_ofs => P'_globs.
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
      rewrite /sem_sopn /= P'_globs /exec_sopn ok_z /= ok_i /= sign_extend_u with_vm_same.
      by move: hx; rewrite /= wrepr0 GRing.addr0 => ->.
    case: eqP => [-> | _] _ .
    + move=> [<-] hx; exists (evm s2) => //.
      constructor.
      rewrite /sem_sopn /= P'_globs /exec_sopn ok_z /= ok_i /= with_vm_same.
      by move: hx; rewrite /= wrepr0 GRing.addr0 => ->.
    move=> [<-] /= hx; exists (evm s2) => //.
    constructor.
    by rewrite /sem_sopn /= P'_globs /exec_sopn /sem_sop2 /= ok_z /= ok_i /= truncate_word_u /= ?truncate_word_u /= hx with_vm_same.
  move=> al ws_ x_ e_; move: (Lmem al ws_ x_ e_) => {al ws_ x_ e_} x.
  case: eqP => [-> | _ ] // /Some_inj <-{ins} hx; exists (evm s2) => //.
  constructor.
  rewrite /sem_sopn /= P'_globs /exec_sopn ok_z /= ok_i /= zero_extend_u.
  by move: hx; rewrite wrepr0 GRing.addr0 with_vm_same => ->.
Qed.


Lemma riscv_immediateP w s (x: var_i) z :
  vtype x = sword Uptr
  -> psem.sem_i (pT := progStack) P' w s (riscv_immediate x z) (with_vm s (evm s).[x <- Vword (wrepr Uptr z)]).
Proof.
  case: x => - [] [] // [] // x xi _ /=.
  constructor.
  by rewrite /sem_sopn /= /exec_sopn /= truncate_word_u.
Qed.

Lemma riscv_swapP rip s tag (x y z w : var_i) (pz pw: pointer):
  vtype x = spointer -> vtype y = spointer ->
  vtype z = spointer -> vtype w = spointer ->
  (evm s).[z] = Vword pz ->
  (evm s).[w] = Vword pw ->
  psem.sem_i (pT := progStack) P' rip s (riscv_swap tag x y z w)
       (with_vm s ((evm s).[x <- Vword pw]).[y <- Vword pz]).
Proof.
  move=> hxty hyty hzty hwty hz hw.
  constructor; rewrite /sem_sopn /= /get_gvar /= /get_var /= hz hw /=.
  rewrite /exec_sopn /= !truncate_word_u /= /write_var /set_var /=.
  rewrite hxty hyty //=.
Qed.

End STACK_ALLOC.

Definition riscv_hsaparams {dc : DirectCall} :
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
  by rewrite Vm.setP_eq /=.
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
  Opaque sem_fopn_args.
  move=> [[? nrsp] vi1] [[? nr] vi2] [[? ntmp] vi3] ts al sz s hget /= ??? hne hne1 hne2; subst.
  rewrite /riscv_set_up_sp_register sem_fopns_args_cat /=.
  set vr := {|vname := nr|}; set r := {|v_var := vr|}.
  set vtmp := {|vname := ntmp|}; set tmp := {|v_var := vtmp|}.
  set vrsp := {|vname := nrsp|}; set rsp := {|v_var := vrsp|}.
  set ts' := align_word _ _.
  have := RISCVFopnP.smart_subi_sem_fopn_args vi3 (y:= rsp) _ (to_word_get_var hget).
  move=> /(_ riscv_linux_call_conv ntmp sz) [].
  + by right => /= -[?]; subst ntmp.
  move=> vm1 [] -> heq1 hget1 /=.
  set s1 := with_vm _ _.
  have -> /= := RISCVFopnP.align_sem_fopn_args ntmp vi3 al
                 (y:= tmp) (s:= s1) (to_word_get_var hget1).
  set s2 := with_vm _ _.
  have hget2 : get_var true (evm s2) rsp = ok (Vword ts).
  + by t_get_var; rewrite (get_var_eq_ex _ _ heq1) //; apply/Sv_neq_not_in_singleton.
  have -> /= := RISCVFopnP.mov_sem_fopn_args (to_word_get_var hget2).
  set s3 := with_vm _ _.
  have hget3 : get_var true (evm s3) tmp = ok (Vword ts').
  + by t_get_var.
  have -> /= := RISCVFopnP.mov_sem_fopn_args (to_word_get_var hget3).
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
  move=> xd xs ofs s vm top hgets.
  case heq: vtype => [|||ws] //; t_xrbindP.
  move=> _ <- /eqP ? w hread hset; subst ws.
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
(* Assembly generation hypotheses. *)

Section ASM_GEN.

(* FIXME: the following line fixes type inference with Coq 8.16 *)
Local Instance the_asm : asm _ _ _ _ _ _ := _.

Lemma condt_notP rf c b :
  riscv_eval_cond rf c = ok b
  -> riscv_eval_cond rf (condt_not c) = ok (negb b).
Proof.
  case: c => c x y.
  case: c => [| | sg | sg].
  rewrite /riscv_eval_cond /=.
  by move=> [] <-.
  
  rewrite /riscv_eval_cond /=.
  move => [] <-.
  by rewrite negbK.

  rewrite /riscv_eval_cond /=.
  move => [] <-.
  by rewrite -Z.leb_antisym Z.geb_leb.

  rewrite /riscv_eval_cond /=.
  move => [] <-.
  rewrite Z.geb_leb Z.leb_antisym.
  by rewrite negbK.

Qed.

(* Lemma eval_assemble_cond_Pvar ii m rf x r v :
  eqflags m rf
  -> of_var_e ii x = ok r
  -> get_var true (evm m) x = ok v
  -> exists2 v',
       value_of_bool (riscv_eval_cond (get_rf rf) (condt_of_rflag r)) = ok v'
       & value_uincl v v'.
Proof.
  move=> eqf hr hv.
  have hincl := xgetflag_ex eqf hr hv.
  clear ii x m eqf hr hv.

  rewrite condt_of_rflagP.

  eexists; last exact: hincl.
  clear v hincl.
  exact: value_of_bool_to_bool_of_rbool.
Qed. *)

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
(* 
Lemma eval_assemble_cond_Obeq ii m rf v x0 x1 r0 r1 v0 v1 :
  is_rflags_GE r0 r1 = true
  -> eqflags m rf
  -> of_var_e ii x0 = ok r0
  -> get_var true (evm m) x0 = ok v0
  -> of_var_e ii x1 = ok r1
  -> get_var true (evm m) x1 = ok v1
  -> sem_sop2 Obeq v0 v1 = ok v
  -> exists2 v',
       value_of_bool (riscv_eval_cond (get_rf rf) GE_ct) = ok v' & value_uincl v v'.
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
Qed. *)

(* Lemma eval_assemble_cond_Oand rf c c0 c1 v v0 v1 v0' v1' :
  condt_and c0 c1 = Some c
  -> value_of_bool (riscv_eval_cond (get_rf rf) c0) = ok v0'
  -> value_uincl v0 v0'
  -> value_of_bool (riscv_eval_cond (get_rf rf) c1) = ok v1'
  -> value_uincl v1 v1'
  -> sem_sop2 Oand v0 v1 = ok v
  -> exists2 v',
       value_of_bool (riscv_eval_cond (get_rf rf) c) = ok v' & value_uincl v v'.
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
  -> value_of_bool (riscv_eval_cond (get_rf rf) c0) = ok v0'
  -> value_uincl v0 v0'
  -> value_of_bool (riscv_eval_cond (get_rf rf) c1) = ok v1'
  -> value_uincl v1 v1'
  -> sem_sop2 Oor v0 v1 = ok v
  -> exists2 v',
       value_of_bool (riscv_eval_cond (get_rf rf) c) = ok v' & value_uincl v v'.
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
Qed. *)

Lemma riscv_eval_assemble_cond : assemble_cond_spec riscv_agparams.
Proof.
  move=> ii m rr rf e c v; rewrite /riscv_agparams /riscv_eval_cond /get_rf /=.
  move=> eqr _.
  elim: e c v => [| | op1 e hind | op2 e0 _ e1 _ |] //= c v.

  - case: op1 => //.
    t_xrbindP=> c' hc' hc; subst c.
    move=> v0 hv0 hsem.
    have [v1 hv1 hincl1] := hind _ _ hc' hv0.
    clear ii m e eqr hc' hv0 hind.
    exact: (eval_assemble_cond_Onot hv1 hincl1 hsem).
    
  t_xrbindP=> -[c_k b] h_op2.
  t_xrbindP=> arg0 h_arg0 arg1 h_arg1 h_c v0 h_v0 v1 h_v1 h_v.
  set sem_arg := (fun or => match or with
    | Some reg => rr reg
    | None => wrepr riscv_reg_size 0
  end).
  rewrite -/(sem_arg (cond_fst c)) -/(sem_arg (cond_snd c)).
  have h_sem_arg0: value_uincl v0 (Vword (sem_arg arg0)).
  + case: e0 {h_op2} h_arg0 {h_arg1} h_v0 => //.
    + move=> v2.
      t_xrbindP => z /of_var_eP h_of_var <-.
      rewrite /sem_fexpr /get_var.
      t_xrbindP => //= h_defined <-.
      have h_to_var:=of_varI h_of_var.
      have:=eqr z.
      by rewrite h_to_var.
    + move => [] // [] // [] // [] // [] <-.
      rewrite /sem_fexpr /=.
      by rewrite /sem_sop1 /= => -[] <-.

  have h_sem_arg1: value_uincl v1 (Vword (sem_arg arg1)).
  + case: e1 {h_op2 h_arg0} h_arg1 h_v1 => //.
    + move=> v2.
      t_xrbindP => z /of_var_eP h_of_var <-.
      rewrite /sem_fexpr /get_var.
      t_xrbindP => //= h_defined <-.
      have h_to_var:=of_varI h_of_var.
      have:=eqr z.
      by rewrite h_to_var.
    + move => [] // [] // [] // [] // [] <-.
      rewrite /sem_fexpr /=.
      by rewrite /sem_sop1 /= => -[] <-.
  
  case: op2 h_op2 h_c h_arg0 h_arg1 h_v => //=.
  - move=> -[] // [] //.
    move=> [] <- <- [] <- h_arg0 h_arg1 /=.
    rewrite /sem_sop2 /=.
    t_xrbindP => z0 /to_wordI' [] ws0 [] w0 [] h_w0 //= ? ->; subst.
    move => z1 /to_wordI' [] ws1 [] w1 [] h_w1 //= ? ->; subst.
    move => <-.
    eexists; first by reflexivity.
    have /word_uincl_eq <- := word_uincl_trans (word_uincl_zero_ext w0 h_w0) h_sem_arg0.
    by have /word_uincl_eq <- := word_uincl_trans (word_uincl_zero_ext w1 h_w1) h_sem_arg1.
    
  - move=> -[] // [] //.
    move=> [] <- <- [] <- h_arg0 h_arg1 /=.
    rewrite /sem_sop2 /=.
    t_xrbindP => z0 /to_wordI' [] ws0 [] w0 [] h_w0 //= ? ->; subst.
    move => z1 /to_wordI' [] ws1 [] w1 [] h_w1 //= ? ->; subst.
    move => <-.
    eexists; first by reflexivity.
    have /word_uincl_eq <- := word_uincl_trans (word_uincl_zero_ext w0 h_w0) h_sem_arg0.
    by have /word_uincl_eq <- := word_uincl_trans (word_uincl_zero_ext w1 h_w1) h_sem_arg1.

  - move=> -[] // sg // [] //.
    move=> [] <- <- [] <- h_arg0 h_arg1 /=.
    rewrite /sem_sop2 /=.
    t_xrbindP => z0 /to_wordI' [] ws0 [] w0 [] h_w0 //= ? ->; subst.
    move => z1 /to_wordI' [] ws1 [] w1 [] h_w1 //= ? ->; subst.
    move => <-.
    eexists; first by reflexivity.
    have /word_uincl_eq <- := word_uincl_trans (word_uincl_zero_ext w0 h_w0) h_sem_arg0.
    have /word_uincl_eq <- := word_uincl_trans (word_uincl_zero_ext w1 h_w1) h_sem_arg1.
    by case: sg {h_arg0 h_arg1}.

  move=> -[] // sg // [] //.
  + move=> [] <- <- [] <- h_arg0 h_arg1 /=.
    rewrite /sem_sop2 /=.
    t_xrbindP => z0 /to_wordI' [] ws0 [] w0 [] h_w0 //= ? ->; subst.
    move => z1 /to_wordI' [] ws1 [] w1 [] h_w1 //= ? ->; subst.
    move => <-.
    eexists; first by reflexivity.
    have /word_uincl_eq <- := word_uincl_trans (word_uincl_zero_ext w0 h_w0) h_sem_arg0.
    have /word_uincl_eq <- := word_uincl_trans (word_uincl_zero_ext w1 h_w1) h_sem_arg1.
    rewrite Z.geb_leb.
    by case: sg {h_arg0 h_arg1}.

  move=> -[] // sg // [] //.
  + move=> [] <- <- [] <- h_arg0 h_arg1 /=.
    rewrite /sem_sop2 /=.
    t_xrbindP => z0 /to_wordI' [] ws0 [] w0 [] h_w0 //= ? ->; subst.
    move => z1 /to_wordI' [] ws1 [] w1 [] h_w1 //= ? ->; subst.
    move => <-.
    eexists; first by reflexivity.
    have /word_uincl_eq <- := word_uincl_trans (word_uincl_zero_ext w0 h_w0) h_sem_arg0.
    have /word_uincl_eq <- := word_uincl_trans (word_uincl_zero_ext w1 h_w1) h_sem_arg1.
    by case: sg {h_arg0 h_arg1}.

  move=> -[] // sg // [] //.
  + move=> [] <- <- [] <- h_arg0 h_arg1 /=.
    rewrite /sem_sop2 /=.
    t_xrbindP => z0 /to_wordI' [] ws0 [] w0 [] h_w0 //= ? ->; subst.
    move => z1 /to_wordI' [] ws1 [] w1 [] h_w1 //= ? ->; subst.
    move => <-.
    eexists; first by reflexivity.
    have /word_uincl_eq <- := word_uincl_trans (word_uincl_zero_ext w0 h_w0) h_sem_arg0.
    have /word_uincl_eq <- := word_uincl_trans (word_uincl_zero_ext w1 h_w1) h_sem_arg1.
    rewrite Z.geb_leb.
    by case: sg {h_arg0 h_arg1}.
Qed.


    (* - t_xrbindP=> //=.
    case: e1 => // x1 _.
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
Qed. *)
(* TODO_RISCV: Is there a way of avoiding importing here? *)
Import arch_sem.

(* Lemma sem_sopns_fopns_args s lc :
  sem_sopns s [seq (None, o, d, e) | '(d, o, e) <- lc] =
  sem_fopns_args s (map RISCVFopn.to_opn lc).
Proof.
  elim: lc s => //= -[[xs o] es ] lc ih s.
  rewrite /sem_fopn_args /sem_sopn_t /=; case: sem_rexprs => //= >.
  by rewrite /exec_sopn /= /Oriscv; case : app_sopn => //= >; case write_lexprs.
Qed. *)

Lemma riscv_assemble_extra_op rip ii op lvs args m xs ys m' s ops ops' :
  sem_rexprs m args = ok xs
  -> exec_sopn (Oasm (ExtOp op)) xs = ok ys
  -> write_lexprs lvs ys m = ok m'
  -> to_asm ii op lvs args = ok ops
  -> mapM (fun '(op0, ls, rs) => assemble_asm_op riscv_agparams rip ii op0 ls rs) ops = ok ops'
  -> lom_eqv rip m s
  -> exists2 s' : asmmem,
       foldM (fun '(op'', asm_args) => [eta eval_op op'' asm_args]) s ops' = ok s' &
       lom_eqv rip m' s'.
Proof.
Admitted.
  (* case: op => /=.
  + move=> w; case: eqP => // -> {w}.
    case: lvs => // -[] // x [] // -[] // y [] //.
    case: args => // -[] // [] // z [] // [] // [] // w [] //=.
    t_xrbindP => vz hz _ vw hw <- <-.
    rewrite /exec_sopn /= /sopn_sem /= /swap_semi.
    t_xrbindP => /= _ wz hvz ww hvw <- <- /=.
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
  have := RISCVFopnP.smart_addi_sem_fopn_args xi (y:= y) (or_intror _ hne) (to_word_get_var hvy).
  move=> /(_ _ imm) [vm []]; rewrite -sem_sopns_fopns_args => hsem heqex /get_varP [hvmx _ _].
  have [] := (assemble_opsP riscv_eval_assemble_cond hmap _ hsem hlom).
  + by rewrite all_map; apply/allT => -[[]].
  move=> s' -> hlo; exists s' => //.
  apply: lom_eqv_ext hlo => z /=.
  move/get_varP: hvy => -[hvmy _ _].
  move: hsety hsetx; rewrite !set_var_eq_type // => -[<-] [<-].
  rewrite !Vm.setP; case: eqP => heqy.
  + subst z; rewrite /= heqex /riscv_reg_size; last by SvD.fsetdec.
    by rewrite -hvmy zero_extend_u.
  case: eqP => heqx.
  + rewrite -heqx -hvmx zero_extend_u /=.
    move: hw2 => /truncate_wordP [? ].
    by rewrite zero_extend_wrepr // => ->.
  by apply heqex; rewrite /riscv_reg_size; SvD.fsetdec.
Qed. *)

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
Admitted.
  (* split.
  + exact: riscv_stack_zero_cmd_not_ext_lbl.
  exact: riscv_stack_zero_cmdP.
Qed. *)

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
    hap_hagp        := riscv_hagparams;
    hap_hshp        := riscv_hshp;
    hap_hszp        := riscv_hszparams;
    hap_is_move_opP := riscv_is_move_opP;
  |}.

End Section.
