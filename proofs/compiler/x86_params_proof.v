From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ.

Require Import
  arch_params_proof
  compiler_util
  expr
  psem
  psem_facts
  one_varmap
  sem_one_varmap.
Require Import
  linearization
  linearization_proof
  lowering
  stack_alloc
  stack_alloc_proof.
Require
  arch_sem.
Require Import
  arch_decl
  arch_extra
  asm_gen
  asm_gen_proof.
Require Import
  x86_decl
  x86_extra
  x86_instr_decl
  x86_lowering
  x86_lowering_proof.
Require Export x86_params.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Section.
Context {syscall_state : Type} {sc_sem : syscall_sem syscall_state}. 
(* ------------------------------------------------------------------------ *)
(* Stack alloc hypotheses. *)

Section STACK_ALLOC.

  Variable (is_regx : var -> bool) (P' : sprog).
  Hypothesis P'_globs : P'.(p_globs) = [::].

  Lemma lea_ptrP s1 e i x tag ofs w s2 :
    (Let i' := sem_pexpr [::] s1 e in to_pointer i') = ok i
    -> write_lval [::] x (Vword (i + wrepr _ ofs)) s1 = ok s2
    -> psem.sem_i P' w s1 (lea_ptr x e tag ofs) s2.
  Proof.
    move=> he hx.
    constructor.
    rewrite /sem_sopn /= P'_globs /sem_sop2 /=.
    move: he; t_xrbindP=> _ -> /= -> /=.
    by rewrite !zero_extend_u hx.
  Qed.

End STACK_ALLOC.

Lemma x86_mov_ofsP (is_regx : var -> bool) (P' : sprog) s1 e i x tag ofs w vpk s2 ins :
  p_globs P' = [::]
  -> (Let i' := sem_pexpr [::] s1 e in to_pointer i') = ok i
  -> sap_mov_ofs (x86_saparams is_regx) x tag vpk e ofs = Some ins
  -> write_lval [::] x (Vword (i + wrepr Uptr ofs)) s1 = ok s2
  -> psem.sem_i P' w s1 ins s2.
Proof.
  move=> P'_globs he.
  rewrite /x86_saparams /= /x86_mov_ofs.
  case: (mk_mov vpk).
  - move=> [<-]. by apply lea_ptrP.
  case: eqP => [-> | _] [<-].
  + by rewrite wrepr0 GRing.addr0 -P'_globs; apply mov_wsP; rewrite // P'_globs.
  by apply lea_ptrP.
Qed.

Definition x86_hsaparams is_regx : h_stack_alloc_params (ap_sap x86_params is_regx) :=
  {|
    mov_ofsP := @x86_mov_ofsP is_regx;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization hypotheses. *)

Section LINEARIZATION.

Context
  {call_conv : calling_convention}
  (lp : lprog)
  (s : estate)
  (sp_rsp : Ident.ident)
  (ii : instr_info)
  (fn : funname)
  (pc : nat).

Let vrsp : var := mk_ptr sp_rsp.
Let vrspi : var_i := VarI vrsp dummy_var_info.
Let vm := evm s.

Definition x86_spec_lip_allocate_stack_frame ts sz :
  let args := lip_allocate_stack_frame x86_liparams vrspi sz in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  let ts' := pword_of_word (ts + wrepr Uptr sz) in
  let s' := with_vm s (vm.[vrsp <- ok ts'])%vmap in
  (vm.[vrsp])%vmap = ok (pword_of_word ts)
  -> eval_instr lp i (of_estate s fn pc)
     = ok (of_estate s' fn pc.+1).
Proof.
  move=> /= Hvm.
  rewrite /eval_instr /= /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite Hvm /=.
  rewrite pword_of_wordE.
  by rewrite 3!zero_extend_u.
Qed.

Definition x86_spec_lip_free_stack_frame ts sz :
  let args := lip_free_stack_frame x86_liparams vrspi sz in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  let ts' := pword_of_word (ts - wrepr Uptr sz) in
  let s' := with_vm s (vm.[vrsp <- ok ts'])%vmap in
  (vm.[vrsp])%vmap = ok (pword_of_word ts)
  -> eval_instr lp i (of_estate s fn pc)
    = ok (of_estate s' fn pc.+1).
Proof.
  move=> /= Hvm.
  rewrite /eval_instr /= /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite Hvm /=.
  rewrite pword_of_wordE.
  by rewrite 3!zero_extend_u.
Qed.

Definition x86_spec_lip_ensure_rsp_alignment ws ts' :
  let al := align_word ws ts' in
  let args := lip_ensure_rsp_alignment x86_liparams vrspi ws in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  get_var (evm s) vrsp = ok (Vword ts')
  -> wf_vm (evm s)
  -> exists vm',
      [/\ eval_instr lp i (of_estate s fn pc)
          = ok (of_estate (with_vm s vm') fn pc.+1)
        , vm' = (evm s).[vrsp <- ok (pword_of_word al)]%vmap
              [\one_varmap.vflags]
        , forall x,
            Sv.In x (one_varmap.vflags)
            -> ~ is_ok (vm'.[x]%vmap)
            -> (evm s).[x]%vmap = vm'.[x]%vmap
        & wf_vm vm'
      ].
Proof.
  move=> al /= Hvrsp.
  rewrite /eval_instr /= /sem_sopn /= /get_gvar /=.
  rewrite Hvrsp /=.
  rewrite !zero_extend_u pword_of_wordE /=.
  rewrite /with_vm /=.
  eexists; split; first by reflexivity.
  + move=> x hin. rewrite !(@Fv.setP _ _ vrsp).
    case: (vrsp =P x).
    + by move=> ?; subst x.
    move=> _.
    have hneq: forall (f : rflag), to_var f != x.
    + move=> f.
      apply/eqP => heq.
      apply /hin /sv_of_listP /mapP.
      exists f => //.
      rewrite /rflags /x86_decl.rflags.
      by rewrite (mem_cenum (cfinT := finC_rflag)).
    by rewrite !Fv.setP_neq.
  + move=> x /sv_of_listP /mapP [f _ ->].
    by case f;
      repeat (rewrite Fv.setP_eq || rewrite Fv.setP_neq //).
  by do! apply wf_vm_set.
Qed.

Definition x86_spec_lip_lassign
  (s1 s2 : estate) x e ws ws' (w : word ws) (w' : word ws') :
  let args := lip_lassign x86_liparams x ws e in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  sem_pexpr [::] s1 e = ok (Vword w')
  -> truncate_word ws w' = ok w
  -> write_lval [::] x (Vword w) s1 = ok s2
  -> eval_instr lp i (of_estate s1 fn pc)
     = ok (of_estate s2 fn pc.+1).
Proof.
  move=> /= Hsem_pexpr Htruncate_word Hwrite_lval.
  rewrite /eval_instr /= /sem_sopn /=.
  rewrite to_estate_of_estate.
  rewrite Hsem_pexpr /=.
  rewrite /exec_sopn /=.
  case: ws w Htruncate_word Hwrite_lval
    => /= ? Htruncate_word Hwrite_lval;
    rewrite Htruncate_word /=;
    rewrite Hwrite_lval /=;
    done.
Qed.

End LINEARIZATION.

Definition x86_hliparams {call_conv : calling_convention} : h_linearization_params (ap_lip x86_params) :=
  {|
    spec_lip_allocate_stack_frame := x86_spec_lip_allocate_stack_frame;
    spec_lip_free_stack_frame := x86_spec_lip_free_stack_frame;
    spec_lip_ensure_rsp_alignment := x86_spec_lip_ensure_rsp_alignment;
    spec_lip_lassign := x86_spec_lip_lassign;
  |}.

Lemma x86_ok_lip_tmp :
  exists r : reg_t, of_string (lip_tmp (ap_lip x86_params)) = Some r.
Proof.
  exists RAX.
  rewrite /=.
  change "RAX"%string with (to_string RAX).
  exact: to_stringK.
Qed.

(* ------------------------------------------------------------------------ *)
(* Lowering hypotheses. *)

Definition x86_hloparams : h_lowering_params (ap_lop x86_params).
Proof.
  split. exact: @lower_callP.
Defined.


(* ------------------------------------------------------------------------ *)
(* Assembly generation hypotheses. *)

(* FIXME: Is there a way of avoiding this import? *)
Import arch_sem.

Lemma not_condtP (c : cond_t) rf b :
  eval_cond rf c = ok b -> eval_cond rf (not_condt c) = ok (negb b).
Proof.
  case: c => /=.
  1,3,5,9,11: by case: (rf _) => //= ? [->].
  1,2,3,6,7: by case: (rf _) => //= ? [<-]; rewrite negbK.
  + by case: (rf CF) => //= ?; case: (rf _) => //= ? [<-]; rewrite negb_or.
  + by case: (rf CF) => //= ?; case: (rf _) => //= ? [<-]; rewrite -negb_or negbK.
  + by case: (rf SF) => //= ?; case: (rf _) => //= ? [<-]; rewrite negbK.
  + by case: (rf SF) => //= ?; case: (rf _) => //= ? [<-].
  + by case: (rf ZF) => //= ?; case: (rf SF) => //= ?; case: (rf _) => //= ? [<-]; rewrite negb_or negbK.
  by case: (rf ZF) => //= ?; case: (rf SF) => //= ?; case: (rf _) => //= ? [<-]; rewrite negb_and negbK.
Qed.

Lemma or_condtP ii e c1 c2 c rf b1 b2:
  or_condt ii e c1 c2 = ok c ->
  eval_cond rf c1 = ok b1 ->
  eval_cond rf c2 = ok b2 ->
  eval_cond rf c  = ok (b1 || b2).
Proof.
  case: c1 => //; case: c2 => //= -[<-] /=.
  + by case: (rf _) => // ? [->]; case: (rf _) => // ? [->].
  + by case: (rf _) => // ? [->]; case: (rf _) => // ? [->] /=; rewrite orbC.
  + by case: (rf ZF) => // ? [->]; case: (rf SF) => //= ?; case: (rf _) => //= ? [<-].
  by case: (rf SF) => //= ?; case: (rf _) => //= ? [<-]; case: (rf _) => //= ? [->]; rewrite orbC.
Qed.

Lemma and_condtP ii e c1 c2 c rf b1 b2:
  and_condt ii e c1 c2 = ok c ->
  eval_cond rf c1 = ok b1 ->
  eval_cond rf c2 = ok b2 ->
  eval_cond rf c  = ok (b1 && b2).
Proof.
  case: c1 => //; case: c2 => //= -[<-] /=.
  + by case: (rf _) => // ? [<-]; case: (rf _) => // ? [<-].
  + by case: (rf _) => // ? [<-]; case: (rf _) => // ? [<-] /=; rewrite andbC.
  + by case: (rf ZF) => // ? [<-]; case: (rf SF) => //= ?; case: (rf _) => //= ? [<-].
  by case: (rf SF) => //= ?; case: (rf _) => //= ? [<-]; case: (rf _) => //= ? [->]; rewrite andbC.
Qed.

Lemma of_var_e_boolP ii x f :
  of_var_e_bool ii x = ok f ->
  of_var_e ii x = ok f.
Proof. by rewrite /of_var_e_bool /of_var_e; case: of_var. Qed.

Lemma eval_assemble_cond ii m rf e c v:
  eqflags m rf
  -> agp_assemble_cond x86_agparams ii e = ok c
  -> sem_pexpr [::] m e = ok v
  -> let get x :=
       if rf x is Def b
       then ok b
       else undef_error
     in
     exists2 v', value_of_bool (eval_cond get c) = ok v' & value_uincl v v'.
Proof.
  rewrite /x86_agparams /eval_cond /=.
  move=> eqv; elim: e c v => //.
  + move=> x c v /=; t_xrbindP=> r /of_var_e_boolP ok_r ok_ct ok_v.
    have := gxgetflag_ex eqv ok_r ok_v.
    case: {ok_r ok_v} r ok_ct => // -[<-] {c} /= h;
      eexists;
      eauto;
      by case: (rf _).
  + case => //= e hrec; t_xrbindP => c v ce hce <- ve hve.
    rewrite /sem_sop1 /=; t_xrbindP => b hb <-.
    have := hrec _ _ hce hve.
    move=> /(value_of_bool_uincl hb).
    move=> -/not_condtP /=.
    move=> ->.
    by exists (~~b).
  + case => //=.
    + move=> e1 _ e2 _ c v.
      case: e1 => //= x1; case: e2 => //= x2; t_xrbindP => f1 /of_var_e_boolP ok_f1 f2 /of_var_e_boolP ok_f2.
      case: ifP => // /orP hor [<-] v1 /(gxgetflag eqv ok_f1) hv1 v2 /(gxgetflag eqv ok_f2) hv2.
      move=> /sem_sop2I /= [b1 [b2 [b3 [hb1 hb2 [<-] ->]]]].
      move: (hv1 _ hb1) (hv2 _ hb2) => hfb1 hfb2.
      exists (b1 == b2); last done.
      by case: hor => /andP [] /eqP ? /eqP ?; subst f1 f2; rewrite hfb1 hfb2 //= eq_sym.
    + move=> e1 hrec1 e2 hrec2 c v; t_xrbindP => c1 hc1 c2 hc2 hand v1 hv1 v2 hv2.
      move=> /sem_sop2I /= [b1 [b2 [b3 [hb1 hb2 [<-] ->]]]].
      have /(value_of_bool_uincl hb1) hec1 := hrec1 _ _ hc1 hv1.
      have /(value_of_bool_uincl hb2) hec2 := hrec2 _ _ hc2 hv2.
      have /= -> := and_condtP hand hec1 hec2.
      by exists (b1 && b2).
    move=> e1 hrec1 e2 hrec2 c v; t_xrbindP => c1 hc1 c2 hc2 hor v1 hv1 v2 hv2.
    move=> /sem_sop2I /= [b1 [b2 [b3 [hb1 hb2 [<-] ->]]]].
    have /(value_of_bool_uincl hb1) hec1 := hrec1 _ _ hc1 hv1.
    have /(value_of_bool_uincl hb2) hec2 := hrec2 _ _ hc2 hv2.
    have /= -> := or_condtP hor hec1 hec2.
    by exists (b1 || b2).
  move=> t e _ e1 _ e2 _ c v /=.
  case: e => //= v1; case: e1 => //= [v2 | [] //= e2'].
  + case: e2 => //= -[] // [] //= vn2; t_xrbindP => f1 /of_var_e_boolP hf1 f2 /of_var_e_boolP hf2 fn2 /of_var_e_boolP hfn2.
    case: ifP => // /orP hor [<-] b1 vv1 /(gxgetflag eqv hf1) hvb1/hvb1{hvb1}hvb1.
    move=> vv2 vv2' /(gxgetflag eqv hf2) hvb2 ht2.
    move=> ?? vvn2 /(gxgetflag eqv hfn2) hvnb2 /sem_sop1I /= [nb2 /hvnb2{hvnb2}hvnb2 ->].
    move=> /truncate_valE [??] ?; subst.
    move: ht2; rewrite /truncate_val /=; t_xrbindP => b2 /hvb2{hvb2}hvb2 ?; subst.
    exists (if b1 then Vbool b2 else ~~ nb2); last done.
    by case: hor => /and3P [/eqP ? /eqP ? /eqP ?]; subst; move: hvnb2; rewrite hvb1 hvb2 => -[<-] /=;
      case: (b1); case: (b2).
  case: e2' => //= v2; case: e2 => // vn2; t_xrbindP => f1 /of_var_e_boolP hf1 f2 /of_var_e_boolP hf2 fn2 /of_var_e_boolP hfn2.
  case: ifP => // /orP hor [<-] b1 vv1 /(gxgetflag eqv hf1) hvb1/hvb1{hvb1}hvb1.
  move=> ? vv2 vv2' /(gxgetflag eqv hf2) hvb2 /sem_sop1I /= [b2 /hvb2{hvb2}hvb2 ->].
  move=> /truncate_valE [??] ?; subst.
  move=> vvn2 /(gxgetflag eqv hfn2) hvnb2.
  rewrite /truncate_val /=; t_xrbindP => nb2 /hvnb2{hvnb2}hvnb2 ??; subst.
  exists (if b1 then Vbool (~~b2) else nb2); last done.
  by case: hor => /and3P [/eqP ? /eqP ? /eqP ?]; subst; move: hvnb2; rewrite hvb1 hvb2 => -[<-] /=;
      case: (b1); case: (b2).
Qed.

Lemma assemble_extra_op rip ii op lvs args op' lvs' args' op'' asm_args m m' s :
  sem_sopn [::] (Oasm (ExtOp op)) m lvs args = ok m'
  -> to_asm ii op lvs args = ok (op', lvs', args')
  -> assemble_asm_op x86_agparams rip ii op' lvs' args'
     = ok (op'', asm_args)
  -> lom_eqv rip m s
  -> exists2 s', eval_op op'' asm_args s = ok s' & lom_eqv rip m' s'.
Proof.
  rewrite /x86_agparams /=.
  case: op.
  + move=> sz; rewrite /sem_sopn /exec_sopn /sopn_sem /=.
    rewrite /Oset0_instr; case: ifP => /= hsz64.
    + t_xrbindP => ? []// ?? [<-] /= <-.
      move=> hw x hx <- <- <-; rewrite /assemble_asm_op.
      t_xrbindP => asm_args' _ hc.
      case hci: enforce_imm_i_args_kinds =>
        {asm_args} [asm_args|//] _ [<-] /andP [hca hcd] <- <-.
      have {hci} hidc := filter_i_args_kinds_no_imm_correct (enforce_imm_i_args_kinds_correct hci).
      move: hca; rewrite /check_sopn_args /= => /and3P [].
      rewrite /check_sopn_arg /=.
      case: asm_args hidc hcd => //= a0 [ // | ] a1 [] //= hidc hcd;
       last by rewrite /check_args_kinds /= !andbF.
      case ok_y: xreg_of_var => [y|//]; move /xreg_of_varI in ok_y.
      rewrite !andbT /compat_imm.
      case: y ok_y => // r xr; rewrite !orbF => /eqP ? /eqP ? _; subst a0 a1; only 2-3: by [].
      rewrite /eval_op /exec_instr_op /= /eval_instr_op /=.
      rewrite /truncate_word /x86_XOR /check_size_8_64 hsz64 /= wxor_xx.
      set id := instr_desc_op (XOR sz) => hlo.
      rewrite /SF_of_word msb0.
      by apply: (@compile_lvals _ _ _ _ _ _ _ _ _ _ _
             rip ii m lvs m' s [:: Reg r; Reg r]
             id.(id_out) id.(id_tout)
             (let vf := Some false in let: vt := Some true in (::vf, vf, vf, vt, vt & (0%R: word sz)))
             (reg_msb_flag sz) (refl_equal _) hw hlo hcd id.(id_check_dest)).
    t_xrbindP => ? []// ?? [<-] /= <-.
    move=> hw x hx <- <- <-; rewrite /assemble_asm_op.
    t_xrbindP => asm_args' _ hc.
    case hci: enforce_imm_i_args_kinds =>
      {asm_args} [asm_args|//] _ [<-] /andP [hca hcd] <- <-.
    have {hci} hidc := filter_i_args_kinds_no_imm_correct (enforce_imm_i_args_kinds_correct hci).
    move: hca; rewrite /check_sopn_args /= => /and3P [].
    rewrite /check_sopn_arg /=.
    case: asm_args hidc hcd => //= a0 [// | ] a1 [] //= a2 [] //=;
      last by rewrite /check_args_kinds /= !andbF.
    rewrite orbF => hidc hcd.
    case ok_y: xreg_of_var => [y|//]; move /xreg_of_varI in ok_y.
    rewrite !andbT /compat_imm.
    case: y ok_y => // r xr; rewrite !orbF => /eqP ? /eqP ? _; subst a1 a2.
    1-2: by move: hidc; rewrite /check_args_kinds /= andbF.
    rewrite /eval_op /exec_instr_op /= /eval_instr_op /=.
    rewrite /truncate_word /x86_VPXOR hidc /= /x86_u128_binop /check_size_128_256 wsize_ge_U256.
    have -> /= : (U128 ≤ sz)%CMP by case: (sz) hsz64.
    rewrite wxor_xx; set id := instr_desc_op (VPXOR sz) => hlo.
    by apply: (@compile_lvals _ _ _ _ _ _ _ _ _ _ _ 
               rip ii m lvs m' s [:: a0; XReg r; XReg r]
               id.(id_out) id.(id_tout)
               (0%R: word sz)
               (reg_msb_flag sz) (refl_equal _) hw hlo hcd id.(id_check_dest)).
  + t_xrbindP.
    case: args => // h [] // [] // x [] //=.
    rewrite /sem_sopn /exec_sopn /sopn_sem /=.
    t_xrbindP => ?? vh hvh ? vl hvl <- <- /= vd.
    t_xrbindP => wh hwh wl hwl <- <- /= hwr <- <- <-.
    rewrite /assemble_asm_op.

    t_xrbindP => asm_args' haux hc'.
    case hci: enforce_imm_i_args_kinds =>
      {asm_args} [asm_args|//] _ [<-] /andP [hca hcd] <- <- hlow.
    have {hci} hch := filter_i_args_kinds_no_imm_correct (enforce_imm_i_args_kinds_correct hci).
    have [s' hwm hlow'] :=
      compile_lvals (asm_e:=x86_extra)
       (id_out := [:: E 0]) (id_tout := [:: sword256]) MSB_CLEAR refl_equal hwr hlow hcd refl_equal.
    exists s'; last done.
    move: hca; rewrite /check_sopn_args /= => /and4P [] hE1 hE2 hE3 _.
Opaque eval_arg_in_v check_i_args_kinds.
    rewrite /eval_op /exec_instr_op /= /eval_instr_op /= hch.
    have [vh' -> /= hvh'] :=
      check_sopn_arg_sem_eval eval_assemble_cond hlow hE2 hvh hwh.
    have [v1 /= -> hv1 /=] :=
      check_sopn_arg_sem_eval eval_assemble_cond hlow hE3 refl_equal (truncate_word_u _).
Transparent eval_arg_in_v check_i_args_kinds.
    move: hE1; rewrite /check_sopn_arg /=.
    case: oseq.onth => // a.
    case: x hvl haux => x [] // hvl haux.
    case heq: xreg_of_var => [ a' | //] /andP[] hc _.
    have := xreg_of_varI heq => {heq}.
    case: a' hc => //= [ r | rx | xmm].
    + rewrite /compat_imm; case:a => //= r' /orP [/eqP [?]|//] hr; subst r'.
      have heq := of_varI hr.
      move: hvl.
      rewrite /get_gvar /= -heq => hvl.
      case: hlow => _ _ _ _ /(_ _ _ hvl) hu _ _ _.
      move: hwl hu; rewrite /to_word.
      case: (vl) => // [ ws w /=| []//].
      rewrite /truncate_word /word_uincl.
      case: ifP => // h1 _ /andP [] h2.
      by have := cmp_le_trans h1 h2.
    + rewrite /compat_imm; case:a => //= r' /orP [/eqP [?]|//] hr; subst r'.
      have heq := of_varI hr.
      move: hvl.
      rewrite /get_gvar /= -heq => hvl.
      case: hlow => _ _ _ _ _ /(_ _ _ hvl) hu _ _.
      move: hwl hu; rewrite /to_word.
      case: (vl) => // [ ws w /=| []//].
      rewrite /truncate_word /word_uincl.
      case: ifP => // h1 _ /andP [] h2.
      by have := cmp_le_trans h1 h2.
    rewrite /compat_imm; case:a => //= xmm' /orP [ /eqP[?]| //] hxmm;subst xmm'.
    rewrite hvh' hv1 /= -hwm /=; do 3! f_equal.
    have := xxgetreg_ex hlow hxmm hvl.
    rewrite zero_extend_u /winserti128 => hu.
    have -> : (lsb (wrepr U8 (wunsigned 1))) by done.
    do 2! f_equal; rewrite /split_vec /=.
    move: hwl hu; rewrite /to_word.
    case: (vl) => // [ws wl' /= | []//].
    rewrite /truncate_word /word_uincl mul0n.
    case: ifP => // hle.
    rewrite (@subword0 U128 U256) // => -[] <- /andP [] _ /eqP ->.
    by rewrite zero_extend_idem.
  case: lvs => // -[] // x [] //.
  rewrite /sem_sopn /exec_sopn /sopn_sem /=.
  case: args => //= a args.
  t_xrbindP => vs1 vs2 va hva vs3 h <- /=.
  case: args h => /=; t_xrbindP; last by move=> *; subst.
  move => <- ? wa htwa [<-] <-; t_xrbindP => m1 hwx ? <- <- <-;subst m1.
  rewrite /assemble_asm_op.
  t_xrbindP => asm_args' _ hc.
  case hci: enforce_imm_i_args_kinds =>
    {asm_args} [asm_args|//] _ [<-] /andP [hca hcd] <- <- hlo.
  have {hci} hidc := filter_i_args_kinds_no_imm_correct (enforce_imm_i_args_kinds_correct hci).
  case: asm_args hidc hcd hca => // a0 [] // a1 []// hidc hcd;
    last by rewrite /check_args_kinds /= !andbF.
  rewrite /check_sopn_args /= andbT => hca1.
  rewrite /eval_op /exec_instr_op /= /eval_instr_op /=.
  rewrite /= in hidc;rewrite hidc.
  have [v' /= -> /= -> /=] :=
    check_sopn_arg_sem_eval eval_assemble_cond hlo hca1 hva htwa.
  move: hcd; rewrite /check_sopn_dests /= /check_sopn_dest /= => /andP -[].
  case ok_y: xreg_of_var => [y|//]; move /xreg_of_varI in ok_y.
  rewrite andbT => /eqP ? _; subst a0.
  case: y hidc hca1 ok_y => // r hidc hca1 /of_varI xr.
  rewrite /mem_write_vals.
  eexists; first reflexivity.
  case: hlo => h0 h1 hrip hd h2 h2x h3 h4.
  move: hwx; rewrite /write_var /set_var.
  rewrite -xr => -[<-]{m'}.
  constructor => //=.
  + by rewrite /get_var Fv.setP_neq //; apply /eqP;case: hd.
  + move=> r' v''; rewrite /get_var /on_vu /= /RegMap.set ffunE.
    case: eqP => [-> | hne].
    + by rewrite Fv.setP_eq /reg_msb_flag /= word_extend_CLEAR zero_extend_u => -[<-].
    rewrite Fv.setP_neq; last by apply /eqP => h; apply hne; apply inj_to_var.
    by apply h2.
  + move=> r' v''; rewrite /get_var /on_vu /= Fv.setP_neq; first by apply h2x.
    by apply/eqP/to_var_reg_neq_regx.
  + move=> r' v''; rewrite /get_var /on_vu /=.
    by rewrite Fv.setP_neq //; apply h3.
  move=> f v''; rewrite /get_var /on_vu /=.
  by rewrite Fv.setP_neq //; apply h4.
Qed.

Definition x86_hagparams : h_asm_gen_params (ap_agp x86_params) :=
  {|
    hagp_eval_assemble_cond := eval_assemble_cond;
    hagp_assemble_extra_op := assemble_extra_op;
  |}.

(* ------------------------------------------------------------------------ *)
(* Shared hypotheses. *)

Definition x86_is_move_opP op vx v :
  ap_is_move_op x86_params op
  -> exec_sopn (Oasm op) [:: vx ] = ok v
  -> List.Forall2 value_uincl v [:: vx ].
Proof.
  by case: op => // -[] [] // [] //= ws _;
    rewrite /exec_sopn /=;
    t_xrbindP=> w ? /to_wordI' [ws' [wx [hle -> ->]]];
    rewrite /sopn_sem /=;
    match goal with
    | |- ?f (zero_extend _ _) = _ -> _ => rewrite /f
    end;
    t_xrbindP=> _ <- <-;
    (constructor; last by constructor);
    apply word_uincl_zero_ext.
Qed.


(* ------------------------------------------------------------------------ *)

Definition x86_h_params {call_conv : calling_convention} : h_architecture_params x86_params :=
  {|
    hap_hsap := x86_hsaparams;
    hap_hlip := x86_hliparams;
    ok_lip_tmp := x86_ok_lip_tmp;
    hap_hlop := x86_hloparams;
    hap_hagp := x86_hagparams;
    hap_is_move_opP := x86_is_move_opP;
  |}.

End Section.
