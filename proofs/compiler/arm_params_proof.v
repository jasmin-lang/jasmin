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
  fexpr_facts
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
  arm_params_common
  arm_params_common_proof
  arm_params_core_proof
  arm_lowering
  arm_lowering_proof
  arm_stack_zeroization_proof.
Require Export arm_params.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Context (P': sprog).

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
    case: e ok_z => // y /= hget.
    case: andb => // -[<-] hw.
    exists (evm s2) => //.
    constructor.
    by rewrite /sem_sopn /= P'_globs /exec_sopn hget /= ok_i /= truncate_word_u /= hw with_vm_same.
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

Lemma smart_mem_mnP mn e op wdb gd s :
  smart_mem_mn mn e = Some op ->
  exists (woff : wreg),
    let: off := wsigned woff in
    [/\ Let x := sem_pexpr wdb gd s e in to_word reg_size x = ok woff
      , ~~ is_mem_immediate off
      & op = Oasm (ExtOp (mn off))
    ].
Proof.
  rewrite /smart_mem_mn.
  apply: obindP => w /is_wconstP -> /oassertP [h [<-]].
  by exists w.
Qed.

Lemma sem_sopn_smart_store
  gd vi s s' al ws xbase eoff es lvs' mn opts (woff : wreg) :
  let: op := Oarm (ARM_op mn opts) in
  let: eop := Oasm (ExtOp (Olarge_store ws (wsigned woff))) in
  let: lnone := Lnone vi (sword arm_reg_size) in
  let: lvs := lnone :: Lmem al ws xbase eoff :: lvs' in
  ~~ set_flags opts ->
  has_shift opts = None ->
  ~~ is_conditional opts ->
  store_mn_of_wsize ws = Some mn ->
  sem_sopn gd op s (Lmem al ws xbase eoff :: lvs') es = ok s' ->
  sem_sopn gd eop s lvs es = ok s'.
Proof.
  move: opts => [[] [] []] //= _ _ _.
  rewrite /sem_sopn /exec_sopn /= /sopn_sem => hmn.
  t_xrbindP=> res args -> /= _ _ <- w'.
  case: ws hmn => //= -[?];
    subst mn;
    case: args => [//|v []] /=;
    t_xrbindP=> // w -> [<-] ?;
    by subst res.
Qed.

Lemma sem_sopn_smart_store_cc
  gd vi s s' al ws xbase eoff es lvs' mn opts (woff : wreg) :
  let: op := Oarm (ARM_op mn opts) in
  let: eop := Oasm (ExtOp (Olarge_store_cc ws (wsigned woff))) in
  let: lnone := Lnone vi (sword arm_reg_size) in
  let: lvs := lnone :: Lmem al ws xbase eoff :: lvs' in
  ~~ set_flags opts ->
  has_shift opts = None ->
  is_conditional opts ->
  store_mn_of_wsize ws = Some mn ->
  sem_sopn gd op s (Lmem al ws xbase eoff :: lvs') es = ok s' ->
  sem_sopn gd eop s lvs es = ok s'.
Proof.
  move: opts => [[] [] []] //= _ _ _.
  rewrite /sem_sopn /exec_sopn /sopn_sem => hmn.
  t_xrbindP=> res args -> /= _ _ <- w'.
  case: ws hmn => // -[?];
    subst mn;
    case: args => [//|v0 []] /=;
    t_xrbindP=> // ? -[//|? [|??]] w -> [] ->;
    t_xrbindP=> //= ? -> [?] ?;
    by subst res w'.
Qed.

Lemma smart_mem_mn_storeP gd vi s s' al ws xbase eoff es lvs' op op' eop :
  let: lnone := Lnone vi (sword arm_reg_size) in
  let: lvs := Lmem al ws xbase eoff :: lvs' in
  get_eop_store op ws = Some eop ->
  sem_sopn gd op s lvs es = ok s' ->
  smart_mem_mn (eop ws) eoff = Some op' ->
  sem_sopn gd op' s (lnone :: lvs) es = ok s'.
Proof using.
  move=> hop hsemes hop'.
  have [woff [_ _ ?]] := smart_mem_mnP true gd s hop'; subst op'.
  clear hop'.
  rewrite /get_eop_store in hop.
  case: op hop hsemes => // -[] // [[//|] []] mn opts.
  move=> /oassertP [] /eqP hmn /oassertP [] /andP [] hsft /eqP hhs.
  case: (boolP (is_conditional _)) => hic [<-].
  - exact: sem_sopn_smart_store_cc.
  exact: sem_sopn_smart_store.
Qed.

Lemma sem_sopn_smart_load
  gd vi s s' al ws xbase eoff lvs es' mn opts (woff : wreg) :
  let: op := Oarm (ARM_op mn opts) in
  let: eop := Oasm (ExtOp (Olarge_load ws (wsigned woff))) in
  let: lnone := Lnone vi (sword arm_reg_size) in
  ~~ set_flags opts ->
  has_shift opts = None ->
  ~~ is_conditional opts ->
  uload_mn_of_wsize ws = Some mn ->
  sem_sopn gd op s lvs (Pload al ws xbase eoff :: es') = ok s' ->
  sem_sopn gd eop s (lnone :: lvs) (Pload al ws xbase eoff :: es') = ok s'.
Proof.
  move: opts => [[] [] []] //= _ _ _.
  rewrite /sem_sopn /exec_sopn /sopn_sem => hmn.
  t_xrbindP=> res args.
  case: ws hmn => // -[?];
    subst mn;
    case: args => [// | v []] /=;
    by t_xrbindP=> // ??? -> /= -> ?? -> /= -> ? /= -> <- ? -> <- -> ?? <- ? /=
      ? -> [<-] <-.
Qed.

Lemma sem_sopn_smart_load_cc
  gd vi s s' al ws xbase eoff lvs es' mn opts (woff : wreg) :
  let: op := Oarm (ARM_op mn opts) in
  let: eop := Oasm (ExtOp (Olarge_load_cc ws (wsigned woff))) in
  let: lnone := Lnone vi (sword arm_reg_size) in
  ~~ set_flags opts ->
  has_shift opts = None ->
  is_conditional opts ->
  uload_mn_of_wsize ws = Some mn ->
  sem_sopn gd op s lvs (Pload al ws xbase eoff :: es') = ok s' ->
  sem_sopn gd eop s (lnone :: lvs) (Pload al ws xbase eoff :: es') = ok s'.
Proof.
  move: opts => [[] [] []] //= _ _ _.
  rewrite /sem_sopn /exec_sopn /sopn_sem => hmn.
  t_xrbindP=> res args.
  case: ws hmn => // -[?];
    subst mn;
    case: args => [// | v []] /=;
    t_xrbindP=> // ? [//|? [|//]];
    by t_xrbindP=> // ??? -> /= -> ?? -> /= -> ? /= -> <- ? -> <- -> _ _ <- ??
      /= -> [] -> ? -> [<-] <- /= ->.
Qed.

Lemma smart_mem_mn_loadP gd vi s s' lvs al ws xbase eoff es' op op' eop :
  let: es := Pload al ws xbase eoff :: es' in
  let: lnone := Lnone vi (sword arm_reg_size) in
  get_eop_load op ws = Some eop ->
  sem_sopn gd op s lvs es = ok s' ->
  smart_mem_mn (eop ws) eoff = Some op' ->
  sem_sopn gd op' s (lnone :: lvs) es = ok s'.
Proof using.
  move=> hop hsemes hop'.
  have [woff [_ _ ?]] := smart_mem_mnP true gd s hop'; subst op'.
  clear hop'.
  rewrite /get_eop_store in hop.
  case: op hop hsemes => // -[] // [[//|] []] mn opts.
  move=> /oassertP [] /eqP hmn /oassertP [] /andP [] hsft /eqP hhs.
  case: (boolP (is_conditional _)) => hic [<-].
  - exact: sem_sopn_smart_load_cc.
  exact: sem_sopn_smart_load.
Qed.

Lemma split_mem_opn_match_lvsP lvs lvs' al ws xbase eoff :
  split_mem_opn_match_lvs lvs = Some (al, ws, xbase, eoff, lvs') <->
  lvs = Lmem al ws xbase eoff :: lvs'.
Proof.
  case: lvs => [// | lv]; case: lv => //= ????. split=> -[]; congruence.
Qed.

Lemma split_mem_opn_match_esP es es' al ws xbase eoff :
  split_mem_opn_match_es es = Some (al, ws, xbase, eoff, es') <->
  es = Pload al ws xbase eoff :: es'.
Proof.
  case: es => [// | e]; case: e => //= ????. split=> -[]; congruence.
Qed.

Lemma arm_mem_opnP : sap_mem_opn_correct (sap_mem_opn arm_saparams).
Proof.
  move=> sp rip s s' lvs tag op es /psem.sem_iE h.
  rewrite /= /arm_mem_opn.
  case hsplit: split_mem_opn => [-[[lvs' op'] es']|]; last by constructor.
  constructor.
  move: hsplit.
  rewrite /split_mem_opn.
  case hlvs: split_mem_opn_match_lvs => [[[[[al ws] xbase] eoff] ?]|].
  - move: hlvs => /split_mem_opn_match_lvsP ?; subst lvs.
    apply: obindP => eop heop.
    apply: obindP => op'' hop'' [???]; subst lvs' op'' es'.
    exact: (smart_mem_mn_storeP _ heop h hop'').
  case hes: split_mem_opn_match_es => [[[[[al ws] xbase] eoff] ?] | //].
  move: hes => /split_mem_opn_match_esP ?; subst es.
  apply: obindP => eop heop.
  apply: obindP => op'' hop'' [???]; subst lvs' op'' es'.
  exact: (smart_mem_mn_loadP _ heop h hop'').
Qed.

End STACK_ALLOC.

Definition arm_hsaparams :
  h_stack_alloc_params (ap_sap arm_params)  :=
  {|
    mov_ofsP := arm_mov_ofsP;
    sap_immediateP := arm_immediateP;
    sap_swapP := arm_swapP;
    sap_mem_opnP := arm_mem_opnP;
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
Proof. case: ws w => w // [?]; subst mn; by rewrite /exec_sopn /= => ->. Qed.

Lemma uload_mn_of_wsize_ccP
  ws ws' mn opts b (w : word ws) (w' : word ws') wold vold :
  ~~ set_flags opts ->
  is_conditional opts ->
  has_shift opts = None ->
  uload_mn_of_wsize ws = Some mn ->
  truncate_word ws w' = ok w ->
  to_word reg_size vold = ok wold ->
  exec_sopn (Oarm (ARM_op mn opts)) [:: Vword w'; Vbool b; vold ]
  = ok [:: Vword (if b then zero_extend reg_size w else wold) ].
Proof.
  move: opts => [[] [] []] //= _ _ _.
  rewrite /exec_sopn /=.
  case: ws w => // w [<-] /= -> ->; by case: b.
Qed.

Lemma store_mn_of_wsize_ccP
  ws ws' mn opts b (w : word ws) (w' : word ws') wold vold :
  ~~ set_flags opts ->
  is_conditional opts ->
  has_shift opts = None ->
  store_mn_of_wsize ws = Some mn ->
  truncate_word ws w' = ok w ->
  to_word ws vold = ok wold ->
  exec_sopn (Oarm (ARM_op mn opts)) [:: Vword w'; Vbool b; vold ]
  = ok [:: Vword (if b then w else wold) ].
Proof.
  move: opts => [[] [] []] //= _ _ _.
  rewrite /exec_sopn /=.
  case: ws w wold => // w wold [<-] /= -> -> /=;
    case: b => //=;
    by rewrite zero_extend_u.
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

Definition arm_hloparams : h_lowering_params (ap_lop arm_params) :=
  {|
    hlop_lower_callP := arm_lower_callP;
  |}.

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

Lemma uncons_StoreP ii les al ws xbase eoff les' :
  uncons_Store ii les = ok (al, ws, xbase, eoff, les') ->
  les = Store al ws xbase eoff :: les'.
Proof. by case: les => [// | [|//]] ????? [-> -> -> -> ->]. Qed.

Lemma uncons_rvarP ii res x res' :
  uncons_rvar ii res = ok (x, res') ->
  res = rvar x :: res'.
Proof. by case: res => [// | [// | [] // ?] ?] [-> ->]. Qed.

Lemma uncons_LoadP ii res al ws xbase eoff res' :
  uncons_Load ii res = ok (al, ws, xbase, eoff, res') ->
  res = Load al ws xbase eoff :: res'.
Proof.
  by case: res => [// | [|//]] ????? [-> -> -> -> ->].
Qed.

Lemma uncons_wconstP ii res imm res' :
  uncons_wconst ii res = ok (imm, res') ->
  exists ws, res = rconst ws imm :: res'.
Proof.
  case: res => [// | [//|]] [] // [] // ? [] // ?? [-> ->]. by eexists.
Qed.

Lemma smart_li_argsP ii ws les res x imm res' :
  smart_li_args ii ws les res = ok (x, imm, res') ->
  [/\ ws = reg_size
    , exists les', les = LLvar x :: les'
    , vtype (v_var x) = sword reg_size
    & exists ws', res = rconst ws' imm :: res'
  ].
Proof.
  rewrite /smart_li_args.
  t_xrbindP=> /eqP -> -[??] /uncons_LLvarP ->.
  t_xrbindP=> /eqP ? _ [??] /uncons_wconstP [? ->].
  t_xrbindP=> ???; subst.
  split=> //=; by eexists.
Qed.

Lemma assemble_smart_li_correct ws : assemble_extra_correct (Osmart_li ws).
Proof.
  move=> rip ii lvs args m xs ys m' s ops ops'.
  move=> hsemargs hexec hwrite.
  rewrite /= /assemble_smart_li.
  t_xrbindP=> -[[x imm] ?] /smart_li_argsP [? [les' ?] hty [ws' ?]] [?] hops
    heq;
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
  t_xrbindP=> m0 vm0 hsetx ? hwrite; subst m0.
  case: les' hwrite => // -[?]; subst m'.
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
  t_xrbindP=> -[[x imm] args'] /smart_li_argsP [? [lvs' ?] hty [ws' ?]];
    subst lvs args ws.
  t_xrbindP=> -[cond args] /unconsP ?; subst args'.
  t_xrbindP=> hfv_cond -[y ?] /uncons_rvarP ? [?] hops heq; subst args ops.
  have [vm' []] :=
    ARMFopn_coreP.li_lsem_1 m (vname (v_var x)) (v_info x) imm.
  rewrite /= -hty -var_surj -var_i_surj => hsem hvm hgetx.
  move: hsemargs hexec hwrite.
  rewrite  /exec_sopn /sopn_sem /sopn_sem_ /=.
  t_xrbindP=> _ vcond hsemcond _ vy hgety vrest hsemrest <- <- <-.
  t_xrbindP=>  w w' hw' bcond /to_boolI ? wy hwy; subst vcond.
  move: hw' => /to_wordI [ws [w0 []]] /Vword_inj [] ?; subst ws.
  rewrite /= => ? /truncate_wordP [hle1 ?]; subst w0 w'.
  case: vrest hsemrest; t_xrbindP=> // _ ??; subst w ys.
  t_xrbindP=> _ vm hsetx <- /[dup] /size_fold2 /size0nil -> /= [?]; subst m'.

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

  - rewrite /ARMFopn_core.li.
    case: ifP => //; by case: ifP.

  - move: hsem.
    rewrite ARMFopnP.sem_fopns_equiv -sem_sopns_fopns_args /=.
    rewrite /ARMFopn_core.li.
    case: ifP => _ /=.

    (* Case: small immediate. *)
    + rewrite /exec_sopn /= /sopn_sem /= truncate_word_u /=.
      t_xrbindP=> ?? vm0 hvm' <- <- [?]; subst vm0.
      rewrite {}hsemcond {}hgety /= truncate_word_u {}hwy /=.
      case: bcond hsetx => /= [|-> //].
      by rewrite hvm'.

    case: ifP => _ /=.

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

Lemma ok_smart_li_args ii imm x :
  let: args := ARMFopn_core.li x imm in
  let: les := [:: LLvar x ] in
  let: res := [:: rconst reg_size imm ] in
  vtype x = sword reg_size ->
  to_asm ii (Osmart_li reg_size) les res = ok (asm_args_of_opn_args args).
Proof. by rewrite /= /assemble_smart_li /smart_li_args /= => ->. Qed.

Lemma chk_assemble_large_loadP err ws woff ws' xbase tmp eoff :
  chk_assemble_large_load err ws woff ws' xbase tmp eoff = ok tt ->
  [/\ ws = ws'
    , forall vm, Let off := sem_fexpr vm eoff in to_word reg_size off = ok woff
    , v_var xbase <> v_var tmp
    , ~~ Sv.mem tmp (free_vars eoff)
    & vtype tmp = sword reg_size
  ].
Proof.
  rewrite /chk_assemble_large_load.
  t_xrbindP=> /eqP ? /eqP /[dup] h /is_fwconstP h' /eqP ? /eqP ?.
  split=> //.
  case: eoff h h' => //= -[] // ? [] //=; by rewrite if_same.
Qed.

Lemma assemble_large_load_correct ws off :
  assemble_extra_correct (Olarge_load ws off).
Proof.
  move=> rip ii lvs args s vargs vres s' xm ops ops' hsemargs hexec hwrite h
    hops' heq.
  move: h.
  rewrite /= /assemble_large_load.
  t_xrbindP=> mn /o2rP hmn [tmp les] /uncons_LLvarP ?; subst lvs.
  t_xrbindP=> -[x les'] /uncons_LLvarP ?; subst les.
  t_xrbindP=> -[[[[al ws'] xbase] eoff] args'] /uncons_LoadP ?; subst args.
  t_xrbindP=> /chk_assemble_large_loadP [? hsemeoff hneq _ hty] ?;
    subst ws' ops.
  move: hsemargs => /=.
  t_xrbindP=> _ wbase vbase hgetbase hwbase woff voff hsemeoff' hwoff w hread <-
    vargs' _ ?; subst vargs.
  move: (hsemeoff (evm s)).
  rewrite {}hsemeoff' /= hwoff => -[?]; subst woff.
  move: hops'.
  rewrite -cats1 mapM_cat; t_xrbindP=> ops_li hli ops_ldr hldr ?; subst ops'.
  move: hexec.
  rewrite /exec_sopn /= truncate_word_le //=.
  case: vargs' => //= -[?]; subst vres.
  move: hwrite => /=.
  rewrite zero_extend_u.
  t_xrbindP=> _ vm /set_varP [_ htrunctmp ?] <- _ vm' /set_varP [_ htruncx ?] <-
    hs'; subst vm vm'.
  move: hs'.
  rewrite with_vm_idem /=.
  case: les' => // -[?]; subst s'.

  (* Load offset to [tmp]. *)
  have [vmi []] :=
    ARMFopn_coreP.li_lsem_1 s (vname (v_var tmp)) (v_info tmp) off.
  rewrite /= -hty -var_surj -var_i_surj => hsem_li hvmi hgettmp.
  have [] :=
    assemble_opsP (m' := with_vm s vmi) arm_eval_assemble_cond hli _ _ heq.
  - rewrite /ARMFopn_core.li. case: ifP => //. by case: ifP.
  - move: hsem_li.
    by rewrite ARMFopnP.sem_fopns_equiv -sem_sopns_fopns_args /= => ->.
  move=> xmi heval_li heqi.

  (* Load from memory at address [xbase + tmp]. *)
  set vmi' := vmi.[x <- Vword (zero_extend reg_size w)].
  have [|xmi' heval_ldr heqi'] :=
    assemble_opsP
      (m' := with_vm s vmi') arm_eval_assemble_cond hldr erefl _ heqi.
  - rewrite /= (get_var_eq_ex (x := xbase) _ _ hvmi);
      last by apply/Sv.singleton_spec.
    rewrite hgetbase /= hwbase /= hgettmp /= truncate_word_u /= hread /=.
    rewrite (uload_mn_of_wsizeP hmn (truncate_word_u w)) /=.
    by rewrite set_var_truncate.
  subst vmi'.

  exists xmi'.
  - by rewrite foldM_cat heval_li.
  apply: (lom_eqv_ext _ heqi') => /= y.
  case: (v_var x =P y) => [<- | /eqP ?].
  - by rewrite !Vm.setP_eq.
  rewrite Vm.setP_neq // Vm.setP_neq //.
  case: (v_var tmp =P y) => [<- | /eqP ?].
  - move: hgettmp => /get_varP [<- _ _].
    by rewrite Vm.setP_eq /= hty cmp_le_refl.
  rewrite Vm.setP_neq //.
  rewrite hvmi //.
  by apply/Sv.singleton_spec/nesym/eqP.
Qed.

Lemma assemble_large_load_cc_correct ws off :
  assemble_extra_correct (Olarge_load_cc ws off).
Proof.
  move=> rip ii lvs args s vargs vres s' xm ops ops' hsemargs hexec hwrite h
    hops' heq.
  move: h.
  rewrite /= /assemble_large_load_cc.
  t_xrbindP=> mn /o2rP hmn [tmp les] /uncons_LLvarP ?; subst lvs.
  t_xrbindP=> -[x les'] /uncons_LLvarP ?; subst les.
  t_xrbindP=> -[[[[al ws'] xbase] eoff] args'] /uncons_LoadP ?; subst args.
  t_xrbindP=> -[cond res] /unconsP ?; subst args'.
  t_xrbindP=> htmpcond htmpres /chk_assemble_large_loadP [? hsemeoff hneq _ hty]
    ?;
    subst ws' ops.

  move: hsemargs => /=.
  t_xrbindP=> _ wbase vbase hgetbase hwbase woff voff hsemeoff' hwoff w hread <-
    _ vcond hsemcond vold hsemold <- ?;
    subst vargs.
  move: (hsemeoff (evm s)).
  rewrite {}hsemeoff' /= hwoff => -[?]; subst woff.
  move: hops'.
  rewrite -cats1 mapM_cat; t_xrbindP=> ops_li hli ops_ldr hldr ?; subst ops'.
  move: hexec.
  rewrite /exec_sopn /= truncate_word_le //=.
  t_xrbindP=> -[/= w0 w1] b /to_boolI ?; subst vcond.
  case: vold hsemold => //.
  t_xrbindP=> vold [|//] hsemres wold hwold [??] ?; subst vres w0 w1.

  move: hwrite => /=.
  t_xrbindP=> _ vm /set_varP [_ htrunctmp ?] <- _ vm' /set_varP [_ htruncx ?] <-
    hs'; subst vm vm'.
  move: hs'.
  rewrite with_vm_idem /=.
  case: les' => // -[?]; subst s'.

  (* Load offset to [tmp]. *)
  have [vmi []] :=
    ARMFopn_coreP.li_lsem_1 s (vname (v_var tmp)) (v_info tmp) off.
  rewrite /= -hty -var_surj -var_i_surj => hsem_li hvmi hgettmp.
  have [] :=
    assemble_opsP (m' := with_vm s vmi) arm_eval_assemble_cond hli _ _ heq.
  - rewrite /ARMFopn_core.li. case: ifP => //. by case: ifP.
  - move: hsem_li.
    by rewrite ARMFopnP.sem_fopns_equiv -sem_sopns_fopns_args /= => ->.
  move=> xmi heval_li heqi.

  (* Load from memory at address [xbase + tmp]. *)
  set w' := if b then zero_extend arm_reg_size w else wold.
  set vmi' := vmi.[x <- Vword w'].
  have [|xmi' heval_ldr heqi'] :=
    assemble_opsP
      (m' := with_vm s vmi') arm_eval_assemble_cond hldr erefl _ heqi.
  - rewrite /= (get_var_eq_ex (x := xbase) _ _ hvmi);
      last by apply/Sv.singleton_spec.
    rewrite hgetbase /= hwbase /= hgettmp /= truncate_word_u /= hread /=.
    rewrite (sem_rexpr_eq_ex (emem s) _ hvmi);
      last by rewrite disjoint_singleton.
    rewrite hsemcond /= (sem_rexprs_eq_ex _ hvmi);
      last by rewrite disjoint_singleton.
    by rewrite hsemres /=
      (uload_mn_of_wsize_ccP _ _ _ _ hmn (truncate_word_u w) hwold) //=
      set_var_truncate.
  subst vmi'.

  exists xmi'.
  - by rewrite foldM_cat heval_li.
  apply: (lom_eqv_ext _ heqi') => /= y.
  case: (v_var x =P y) => [<- | /eqP ?].
  - rewrite !Vm.setP_eq.
    subst w'.
    case: b hsemcond heqi' htruncx => //= _ _ _.
    by rewrite zero_extend_u.
  rewrite Vm.setP_neq // Vm.setP_neq //.
  case: (v_var tmp =P y) => [<- | /eqP ?].
  - move: hgettmp => /get_varP [<- _ _].
    rewrite Vm.setP_eq /= hty cmp_le_refl.
    by case: b w' hsemcond heqi' htruncx => //=.
  rewrite Vm.setP_neq //.
  rewrite hvmi //.
  by apply/Sv.singleton_spec/nesym/eqP.
Qed.

Lemma chk_assemble_large_storeP err ws woff ws' x xbase tmp eoff :
  chk_assemble_large_store err ws woff ws' x xbase tmp eoff = ok tt ->
  [/\ ws = ws'
    , forall vm, Let off := sem_fexpr vm eoff in to_word reg_size off = ok woff
    , v_var xbase <> v_var tmp
    , vtype tmp = sword reg_size
    , ~~ Sv.mem tmp (free_vars eoff)
    & v_var x <> v_var tmp
  ].
Proof.
  rewrite /chk_assemble_large_store.
  by t_xrbindP=> /chk_assemble_large_loadP [?????] /eqP.
Qed.

Lemma assemble_large_store_correct ws off :
  assemble_extra_correct (Olarge_store ws off).
Proof.
  move=> rip ii lvs args s vargs vres s' xm ops ops' hsemargs hexec hwrite h
    hops' heq.
  move: h.
  rewrite /= /assemble_large_store.
  t_xrbindP=> mn /o2rP hmn [tmp les] /uncons_LLvarP ?; subst lvs.
  t_xrbindP=> -[[[[al ws'] xbase] eoff] les'] /uncons_StoreP ?; subst les.
  t_xrbindP=> -[x res'] /uncons_rvarP ?; subst args.
  t_xrbindP=> /chk_assemble_large_storeP [? hsemeoff hneqbase hty _ hneqx] ?;
    subst ws' ops.
  move: hsemargs => /=.
  t_xrbindP=> vx hgetx vargs' hsemres' ?; subst vargs.
  move: hops'.
  rewrite -cats1 mapM_cat; t_xrbindP=> ops_li hli ops_ldr hstr ?; subst ops'.
  move: hexec.
  rewrite /exec_sopn /=.
  t_xrbindP.
  case: vargs' hsemres' => // hsemres' [_ _] w /to_wordI [ws' [wx [? hwx]]]
    [<- <-] ?; subst vx vres.
  move: hsemres' => /size_mapM /size0nil ?; subst res'.
  move: hwrite => /=.
  rewrite zero_extend_u.
  t_xrbindP=> _ vm /set_varP [_ htrunctmp ?] <- /= _ wbase vbase hgetbase hwbase
    woff voff hsemeoff' hwoff w' hw' m hwrite <- hs'; subst vm.
  rewrite get_var_neq in hgetbase; last by apply/nesym.
  move: (hsemeoff (evm s).[tmp <- Vword (wrepr arm_reg_size off)]).
  rewrite {}hsemeoff' /= hwoff => -[?]; subst woff.
  move: hw'.
  rewrite truncate_word_u => -[?]; subst w'.
  move: hs'.
  case: les' => // -[?]; subst s'.

  (* Load offset to [tmp]. *)
  have [vmi []] :=
    ARMFopn_coreP.li_lsem_1 s (vname (v_var tmp)) (v_info tmp) off.
  rewrite /= -hty -var_surj -var_i_surj => hsem_li hvmi hgettmp.
  have [] :=
    assemble_opsP (m' := with_vm s vmi) arm_eval_assemble_cond hli _ _ heq.
  - rewrite /ARMFopn_core.li. case: ifP => //. by case: ifP.
  - move: hsem_li.
    by rewrite ARMFopnP.sem_fopns_equiv -sem_sopns_fopns_args /= => ->.
  move=> xmi heval_li heqi.

  set si := with_vm s vmi.
  (* Store to memory at address [xbase + tmp]. *)
  have [|xmi' heval_str heqi'] :=
    assemble_opsP
      (m' := with_mem si m) arm_eval_assemble_cond hstr erefl _ heqi.
  - rewrite /= (get_var_eq_ex (x := x) _ _ hvmi);
      last by apply/Sv.singleton_spec.
    rewrite hgetx /= (store_mn_of_wsizeP hmn hwx) /=.
    rewrite (get_var_eq_ex (x := xbase) _ _ hvmi);
      last by apply/Sv.singleton_spec.
    by rewrite hgetbase /= hwbase /= hgettmp /= !truncate_word_u /= hwrite.
  subst si.

  exists xmi'.
  - by rewrite foldM_cat heval_li.
  apply: (lom_eqv_ext _ heqi') => /= y.
  case: (v_var tmp =P y) => [<- | /eqP ?].
  - move: hgettmp => /get_varP [<- _ _].
    by rewrite Vm.setP_eq /= hty cmp_le_refl.
  rewrite Vm.setP_neq //.
  rewrite hvmi //.
  by apply/Sv.singleton_spec/nesym/eqP.
Qed.

Lemma assemble_large_store_cc_correct ws off :
  assemble_extra_correct (Olarge_store_cc ws off).
Proof.
  move=> rip ii lvs args s vargs vres s' xm ops ops' hsemargs hexec hwrite h
    hops' heq.
  move: h.
  rewrite /= /assemble_large_store_cc.
  t_xrbindP=> mn /o2rP hmn [tmp les] /uncons_LLvarP ?; subst lvs.
  t_xrbindP=> -[[[[al ws'] xbase] eoff] les'] /uncons_StoreP ?; subst les.
  t_xrbindP=> -[x res'] /uncons_rvarP ?; subst args.
  t_xrbindP=> -[cond res] /unconsP ?; subst res'.
  t_xrbindP=> -[[[[al' ws''] xbase'] eoff'] res'] /uncons_LoadP ?; subst res.
  t_xrbindP=> hcond /andP [/eqP hxbase' heoff_eoff'] /chk_assemble_large_storeP
    [? hsemeoff hneqbase hty hneqoff hneqx] ?;
    subst ws' ops.

  move: hsemargs => /=.
  t_xrbindP=> vx hgetx _ varg hsemcond _ _ wbase' vbase'
    hgetbase' hwbase' woff' voff' hsemeoff' hwoff' w'' hread <- vres' hsemres'
    <- <- ?;
    subst vargs.
  move: hops'.
  rewrite -cats1 mapM_cat; t_xrbindP=> ops_li hli ops_ldr hstr ?; subst ops'.
  move: hexec.
  rewrite /exec_sopn /=.
  t_xrbindP.
  case: vres' hsemres' => // /size_mapM /size0nil ?; subst res'.
  move=> [/= w0 w] w1 /to_wordI [ws' [wx [? hwx]]] b /to_boolI ? wold
    hwold [??] ?;
    subst varg vres w0 w vx.
  move: hwrite => /=.
  rewrite truncate_word_u zero_extend_u.
  t_xrbindP=> _ vm /set_varP [_ htrunctmp ?] <- /= _ wbase vbase hgetbase hwbase
    woff voff hsemeoff0 hwoff _ <- m hwrite <- hs'; subst vm.
  rewrite get_var_neq in hgetbase; last by apply/nesym.
  move: (hsemeoff (evm s).[tmp <- Vword (wrepr arm_reg_size off)]).
  rewrite hsemeoff0 /= hwoff => -[?]; subst woff.
  move: hsemeoff0.
  rewrite (eq_fexpr_sem_fexpr _ heoff_eoff').
  rewrite (sem_fexpr_eq_ex (vm2 := evm s) (xs := Sv.singleton tmp)); first last.
  - by apply: eq_ex_set_l => // /Sv.singleton_spec.
  - by rewrite -(eq_fexpr_free_vars heoff_eoff') disjoint_singleton.
  rewrite hsemeoff' => -[?]; subst voff'.
  move: hwoff' => /to_wordI [ws0 [woff [? hwoff']]]; subst voff.
  move: hwoff' => /truncate_wordP [hws0 ?]; subst woff'.
  move: hwoff => /to_wordI [ws1 [woff' [h hwoff']]].
  move: h => /Vword_inj [?]; subst ws1.
  rewrite /= => ?; subst woff'.
  move: hwoff' => /truncate_wordP [_ hwoff].
  rewrite -hwoff in hread.
  move: hs'.
  case: les' => // -[?]; subst s'.

  (* Load offset to [tmp]. *)
  have [vmi []] :=
    ARMFopn_coreP.li_lsem_1 s (vname (v_var tmp)) (v_info tmp) off.
  rewrite /= -hty -var_surj -var_i_surj => hsem_li hvmi hgettmp.
  have [] :=
    assemble_opsP (m' := with_vm s vmi) arm_eval_assemble_cond hli _ _ heq.
  - rewrite /ARMFopn_core.li. case: ifP => //. by case: ifP.
  - move: hsem_li.
    by rewrite ARMFopnP.sem_fopns_equiv -sem_sopns_fopns_args /= => ->.
  move=> xmi heval_li heqi.

  set si := with_vm s vmi.
  (* Store to memory at address [xbase + tmp]. *)
  have [|xmi' heval_str heqi'] :=
    assemble_opsP
      (m' := with_mem si m) arm_eval_assemble_cond hstr erefl _ heqi.
  - rewrite /= (get_var_eq_ex (x := x) _ _ hvmi);
      last by apply/Sv.singleton_spec.
    rewrite hgetx /=.
    rewrite (sem_rexpr_eq_ex (emem s) _ hvmi);
      last by rewrite disjoint_singleton.
    rewrite hsemcond /=.
    rewrite (get_var_eq_ex (x := xbase) _ _ hvmi);
      last by apply/Sv.singleton_spec.
    rewrite hgetbase /= hwbase /= hgettmp /= truncate_word_u /=.
    rewrite (get_var_eq_ex (x := xbase') _ _ hvmi); first last.
    - rewrite -hxbase'. by apply/Sv.singleton_spec.
    rewrite hgetbase' /= hwbase' /= hread /=.
    by rewrite (store_mn_of_wsize_ccP (wold := wold) _ _ _ _ hmn hwx) //=
      truncate_word_u /= hwrite.
    subst si.

  exists xmi'.
  - by rewrite foldM_cat heval_li.
    apply: (lom_eqv_ext _ heqi') => /= y.
    case: (v_var tmp =P y) => [<- | /eqP ?].
  - move: hgettmp => /get_varP [<- _ _].
    by rewrite Vm.setP_eq /= hty cmp_le_refl.
    rewrite Vm.setP_neq //.
    rewrite hvmi //.
    by apply/Sv.singleton_spec/nesym/eqP.
Qed.

Lemma arm_assemble_extra_op op : assemble_extra_correct op.
Proof.
  case: op.
  + exact: assemble_swap_correct.
  + exact: assemble_add_large_imm_correct.
  + exact: assemble_smart_li_correct.
  + exact: assemble_smart_li_cc_correct.
  + exact: assemble_large_load_correct.
  + exact: assemble_large_store_correct.
  + exact: assemble_large_load_cc_correct.
  exact: assemble_large_store_cc_correct.
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

Definition arm_h_params : h_architecture_params arm_params :=
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
