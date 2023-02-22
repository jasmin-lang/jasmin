From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ.

Require Import
  arch_params_proof
  compiler_util
  expr
  psem
  psem_facts
  sem_one_varmap.
Require Import
  linearization
  linearization_proof
  lowering
  propagate_inline_proof
  stack_alloc
  stack_alloc_proof
  clear_stack
  clear_stack_proof.
Require
  arch_sem.
Require Import
  arch_decl
  arch_extra
  asm_gen
  asm_gen_proof.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl
  arm_lowering
  arm_lowering_proof.
Require Export arm_params.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Section.

Context
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {call_conv : calling_convention}.


Lemma arm_hcsparams : h_clear_stack_params arm_csparams.
Proof. done. Qed.

(* ------------------------------------------------------------------------ *)
(* Flag combination hypotheses. *)

Lemma arm_cf_xsemP gd s e0 e1 e2 e3 cf v :
  let: e := PappN (Ocombine_flags cf) [:: e0; e1; e2; e3 ] in
  let: e' := cf_xsem enot eand eor expr.eeq e0 e1 e2 e3 cf in
  sem_pexpr gd s e = ok v
  -> sem_pexpr gd s e' = ok v.
Proof.
  rewrite /=.

  t_xrbindP=> vs0 v0 hv0 vs1 v1 hv1 vs2 v2 hv2 vs3 v3 hv3 ? ? ? ?;
    subst vs0 vs1 vs2 vs3.
  rewrite /sem_opN /=.
  t_xrbindP=> b b0 hb0 b1 hb1 b2 hb2 b3 hb3 hb ?; subst v.
  move: hb0 => /to_boolI ?; subst v0.
  move: hb1 => /to_boolI ?; subst v1.
  move: hb2 => /to_boolI ?; subst v2.
  move: hb3 => /to_boolI ?; subst v3.

  move: hb.
  rewrite /sem_combine_flags.
  rewrite /cf_xsem.

  case: cf_tbl => -[] [] [?] /=; subst b.
  all: by rewrite ?hv0 ?hv1 ?hv2 ?hv3.
Qed.

Definition arm_hpiparams : h_propagate_inline_params :=
  {|
    pip_cf_xsemP := arm_cf_xsemP;
  |}.

(* ------------------------------------------------------------------------ *)
(* Stack alloc hypotheses. *)

Section STACK_ALLOC.

Context
  (P' : sprog)
  (P'_globs : p_globs P' = [::]).

Lemma addiP s1 e i x tag ofs w s2 :
  (Let i' := sem_pexpr [::] s1 e in to_pointer i') = ok i
  -> write_lval [::] x (Vword (i + wrepr _ ofs)) s1 = ok s2
  -> psem.sem_i (pT := progStack) P' w s1 (addi x tag e ofs) s2.
Proof.
  move=> he hx.
  constructor.
  rewrite /sem_sopn /=.
  rewrite P'_globs.
  rewrite /exec_sopn /=.
  move: he.
  t_xrbindP=> ? -> /= -> /=.
  rewrite zero_extend_u.
  by rewrite hx.
Qed.

End STACK_ALLOC.

Lemma arm_mov_ofsP (P': sprog) s1 e i x tag ofs w vpk s2 ins :
  p_globs P' = [::]
  -> (Let i' := sem_pexpr [::] s1 e in to_pointer i') = ok i
  -> sap_mov_ofs arm_saparams x tag vpk e ofs = Some ins
  -> write_lval [::] x (Vword (i + wrepr Uptr ofs)) s1 = ok s2
  -> psem.sem_i (pT := progStack) P' w s1 ins s2.
Proof.
  move=> P'_globs he.
  rewrite /arm_mov_ofs.
  move=> [<-].
  by apply: addiP.
Qed.

Definition arm_hsaparams is_regx :
  h_stack_alloc_params (ap_sap arm_params is_regx) :=
  {|
    mov_ofsP := arm_mov_ofsP;
  |}.


(* ------------------------------------------------------------------------ *)
(* Linearization hypotheses. *)

Section LINEARIZATION.

Context
  (lp : lprog)
  (s : estate)
  (sp_rsp : Ident.ident)
  (ii : instr_info)
  (fn : funname)
  (pc : nat).

Let vrsp : var := mk_ptr sp_rsp.
Let vrspi : var_i := VarI vrsp dummy_var_info.
Let vm := evm s.

Lemma arm_spec_lip_allocate_stack_frame ts sz :
  let args := lip_allocate_stack_frame arm_liparams vrspi sz in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  let ts' := pword_of_word (ts - wrepr Uptr sz) in
  let s' := with_vm s (vm.[vrsp <- ok ts'])%vmap in
  (vm.[vrsp])%vmap = ok (pword_of_word ts)
  -> eval_instr lp i (of_estate s fn pc)
     = ok (of_estate s' fn pc.+1).
Proof.
  move=> /= hvm.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite hvm /=.
  rewrite pword_of_wordE.
  rewrite wsub_wnot1.
  by rewrite zero_extend_u zero_extend_wrepr.
Qed.

Lemma arm_spec_lip_free_stack_frame ts sz :
  let args := lip_free_stack_frame arm_liparams vrspi sz in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  let ts' := pword_of_word (ts + wrepr Uptr sz) in
  let s' := with_vm s (vm.[vrsp <- ok ts'])%vmap in
  (vm.[vrsp])%vmap = ok (pword_of_word ts)
  -> eval_instr lp i (of_estate s fn pc)
     = ok (of_estate s' fn pc.+1).
Proof.
  move=> /= hvm.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite hvm /=.
  rewrite pword_of_wordE.
  by rewrite zero_extend_u zero_extend_wrepr.
Qed.

Lemma arm_spec_lip_ensure_rsp_alignment ws ts' :
  let al := align_word ws ts' in
  let args := lip_ensure_rsp_alignment arm_liparams vrspi ws in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  get_var (evm s) vrsp = ok (Vword ts')
  -> wf_vm (evm s)
  -> exists vm',
      [/\ eval_instr lp i (of_estate s fn pc)
          = ok (of_estate (with_vm s vm') fn pc.+1)
        , vm' = (evm s).[vrsp <- ok (pword_of_word al)]%vmap
              [\vflags]
        , forall x,
            Sv.In x vflags
            -> ~ is_ok (vm'.[x]%vmap)
            -> (evm s).[x]%vmap = vm'.[x]%vmap
        & wf_vm vm'
      ].
Proof.
  move=> /= hvrsp hwm1.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite /get_gvar /=.
  rewrite hvrsp /=.
  rewrite zero_extend_u zero_extend_wrepr; last done.
  rewrite pword_of_wordE.
  rewrite /with_vm /=.
  eexists; split=> //.
  + move=> x hin. rewrite !(@Fv.setP _ _ vrsp).
    case: (vrsp =P x) => //.
    by move=> ?; subst x.
  by apply wf_vm_set.
Qed.

Lemma store_mn_of_wsizeP ws ws' mn (w : word ws) (w' : word ws') :
  store_mn_of_wsize ws = Some mn
  -> truncate_word ws w' = ok w
  -> exec_sopn (Oarm (ARM_op mn default_opts)) [:: Vword w' ]
     = ok [:: Vword w ].
Proof.
  case: ws w => w // [?]; subst mn.
  all: rewrite /exec_sopn /=.
  all: move=> -> /=.
  all: by rewrite zero_extend_u.
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

Lemma arm_hlip_lassign
  (s1 s2 : estate) x e ws li ws' (w : word ws) (w' : word ws') :
  lassign arm_liparams x ws e = Some li
  -> sem_pexpr [::] s1 e = ok (Vword w')
  -> truncate_word ws w' = ok w
  -> write_lval [::] x (Vword w) s1 = ok s2
  -> eval_instr lp (MkLI ii li) (of_estate s1 fn pc)
     = ok (of_estate s2 fn pc.+1).
Proof.
  move=> hlassign hseme htrunc hwrite.

  move: hlassign.
  rewrite /lassign /= /arm_lassign.
  case: x hwrite => [| x | ? ? ? ||] hwrite //=; first last.
  {
    case hmn: store_mn_of_wsize => [mn|] // [?]; subst li.
    all: rewrite /eval_instr /= /sem_sopn /=.
    all: rewrite to_estate_of_estate.
    all: rewrite hseme {hseme} /=.
    all: rewrite (store_mn_of_wsizeP hmn htrunc) {hmn htrunc}.
    all: by rewrite /Result.bind /write_lvals /fold2 hwrite /=.
  }

  case: ws w htrunc hwrite => //= w htrunc hwrite.
  case: e hseme => [||| ? ||| ??? | op1 e |||] //= hseme.
  - move=> [?]; subst li.
    rewrite /eval_instr /= /sem_sopn /=.
    rewrite to_estate_of_estate.
    rewrite hseme {hseme} /=.
    rewrite /exec_sopn /=.
    rewrite htrunc {htrunc} /=.
    by rewrite hwrite {hwrite} /=.

  move=> [?]; subst li.
  rewrite /eval_instr /= /sem_sopn /=.
  rewrite to_estate_of_estate.
  rewrite hseme {hseme} /=.
  rewrite /exec_sopn /=.
  rewrite htrunc {htrunc} /=.
  rewrite zero_extend_u.
  by rewrite hwrite {hwrite} /=.
Qed.

End LINEARIZATION.

Definition arm_hliparams :
  h_linearization_params (ap_lip arm_params) :=
  {|
    spec_lip_allocate_stack_frame := arm_spec_lip_allocate_stack_frame;
    spec_lip_free_stack_frame := arm_spec_lip_free_stack_frame;
    spec_lip_ensure_rsp_alignment := arm_spec_lip_ensure_rsp_alignment;
    hlip_lassign := arm_hlip_lassign;
  |}.

Lemma arm_ok_lip_tmp :
  exists r : reg_t, of_string (lip_tmp (ap_lip arm_params)) = Some r.
Proof.
  exists R12.
  rewrite /=.
  change "r12"%string with (to_string R12).
  exact: to_stringK.
Qed.

(* ------------------------------------------------------------------------ *)
(* Lowering hypotheses. *)

Lemma arm_lower_callP
  (eft : eqType)
  (pT : progT eft)
  (sCP : semCallParams)
  (p : prog)
  (ev : extra_val_t)
  (options : lowering_options)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars)
  (is_var_in_memory : var_i -> bool)
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
         is_var_in_memory
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
  -> of_var_e ii (gv x) = ok r
  -> get_gvar [::] (evm m) x = ok v
  -> exists2 v',
       value_of_bool (eval_cond (get_rf rf) (condt_of_rflag r)) = ok v'
       & value_uincl v v'.
Proof.
  move=> eqf hr hv.
  have hincl := gxgetflag_ex eqf hr hv.
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
  -> of_var_e ii (gv x0) = ok r0
  -> get_gvar [::] (evm m) x0 = ok v0
  -> of_var_e ii (gv x1) = ok r1
  -> get_gvar [::] (evm m) x1 = ok v1
  -> sem_sop2 Obeq v0 v1 = ok v
  -> exists2 v',
       value_of_bool (eval_cond (get_rf rf) GE_ct) = ok v' & value_uincl v v'.
Proof.
  move=> hGE eqf hr0 hv0 hr1 hv1.

  move=> /sem_sop2I /= [b0 [b1 [b [hb0 hb1 hb ?]]]]; subst v.
  move: hb.
  rewrite /mk_sem_sop2 /=.
  move=> [?]; subst b.

  have hincl0 := gxgetflag_ex eqf hr0 hv0.
  have hincl1 := gxgetflag_ex eqf hr1 hv1.
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
  -> sem_pexpr [::] m e = ok v
  -> exists2 v',
       value_of_bool (eval_cond (get_rf rf) c) = ok v' & value_uincl v v'.
Proof.
  rewrite /=.
  elim: e c v => [||| x |||| op1 e hind | op2 e0 hind0 e1 hind1 ||] //= c v eqf.

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

Lemma arm_assemble_extra_op
  rip ii op lvs args op' lvs' args' op'' asm_args m m' s :
  sem_sopn [::] (Oasm (ExtOp op)) m lvs args = ok m'
  -> to_asm ii op lvs args = ok (op', lvs', args')
  -> assemble_asm_op arm_agparams rip ii op' lvs' args'
     = ok (op'', asm_args)
  -> lom_eqv rip m s
  -> exists2 s', eval_op op'' asm_args s = ok s' & lom_eqv rip m' s'.
Proof. by case: op. Qed.

Definition arm_hagparams : h_asm_gen_params (ap_agp arm_params) :=
  {|
    hagp_eval_assemble_cond := arm_eval_assemble_cond;
    hagp_assemble_extra_op := arm_assemble_extra_op;
  |}.

End ASM_GEN.


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
  rewrite /sopn_sem /=.
  rewrite /drop_semi_nzcv /=.
  move=> [<-] <-.
  apply: List.Forall2_cons; last done.
  exact: (word_uincl_zero_ext w' hws').
Qed.


(* ------------------------------------------------------------------------ *)

Definition arm_h_params : h_architecture_params arm_params :=
  {|
    hap_hpip := arm_hpiparams;
    hap_hsap := arm_hsaparams;
    hap_hlip := arm_hliparams;
    ok_lip_tmp := arm_ok_lip_tmp;
    hap_hlop := arm_hloparams;
    hap_hcsp := arm_hcsparams;
    hap_hagp := arm_hagparams;
    hap_is_move_opP := arm_is_move_opP;
  |}.

End Section.
