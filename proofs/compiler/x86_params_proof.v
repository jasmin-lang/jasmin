From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ.

Require Import
  arch_params_proof
  compiler_util
  expr
  fexpr
  fexpr_sem
  psem
  psem_facts
  one_varmap
  sem_one_varmap.
Require Import
  linearization
  linearization_proof
  lowering
  propagate_inline_proof
  stack_alloc
  stack_alloc_proof.
Require
  arch_sem.
Require Import
  arch_decl
  arch_extra
  asm_gen
  asm_gen_proof
  sem_params_of_arch_extra.
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
(* Flag combination hypotheses. *)

Lemma x86_cf_xsemP gd s e0 e1 e2 e3 cf v :
  let e := PappN (Ocombine_flags cf) [:: e0; e1; e2; e3 ] in
  let e' := cf_xsem enot eand eor expr.eeq e0 e1 e2 e3 cf in
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

Definition x86_hpiparams : h_propagate_inline_params :=
  {|
    pip_cf_xsemP := x86_cf_xsemP;
  |}.

(* ------------------------------------------------------------------------ *)
(* Stack alloc hypotheses. *)

Section STACK_ALLOC.

  Variable (is_regx : var -> bool) (P' : sprog).
  Hypothesis P'_globs : P'.(p_globs) = [::].

  Lemma lea_ptrP s1 e i x tag ofs w s2 :
    (Let i' := sem_pexpr [::] s1 e in to_pointer i') = ok i
    -> write_lval [::] x (Vword (i + wrepr _ ofs)) s1 = ok s2
    -> psem.sem_i (pT := progStack) P' w s1 (lea_ptr x e tag ofs) s2.
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
  -> psem.sem_i (pT := progStack) P' w s1 ins s2.
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
    mov_ofsP := x86_mov_ofsP (is_regx := is_regx);
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization hypotheses. *)

Section LINEARIZATION.

Definition x86_lassign_eval_instr
  {call_conv : calling_convention}
  (lp : lprog)
  s0 s1 fn pc ii x e ws ws' w (w' : word ws') :
  sem_rexpr (emem s0) (evm s0) e = ok (Vword w')
  -> truncate_word ws w' = ok w
  -> write_lexpr x (Vword w) s0 = ok s1
  -> let: li := li_of_copn_args ii (x86_lassign x ws e) in
     let: ls0 := of_estate s0 fn pc in
     let: ls1 := of_estate s1 fn (pc + 1) in
     eval_instr lp li ls0 = ok ls1.
Proof.
  move=> hseme hw hwritex.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite to_estate_of_estate.
  rewrite hseme {hseme} /=.

  case: ws w hw hwritex => /= w hw hwritex.
  all: rewrite /exec_sopn /=.
  all: rewrite hw {hw} /=.
  all: rewrite hwritex {hwritex} /=.
  all: by rewrite addn1.
Qed.

Definition x86_op_align_eval_instr
  {call_conv : calling_convention}
  (lp : lprog)
  ls ii xname vi ws al w :
  let: x :=
    {|
      v_var := {| vname := xname; vtype := sword ws; |};
      v_info := vi;
    |}
  in
  (ws <= U64)%CMP
  -> get_var (lvm ls) (v_var x) = ok (Vword w)
  -> let: li := li_of_copn_args ii (x86_op_align x ws al) in
     let w' := align_word al w in
     let: vm' :=
       (lvm ls)
         .[to_var OF <- ok false]
         .[to_var CF <- ok false]
         .[to_var SF <- ok (SF_of_word w')]
         .[to_var PF <- ok (PF_of_word w')]
         .[to_var ZF <- ok (ZF_of_word w')]
         .[v_var x <- ok (pword_of_word w')]%vmap
     in
     let: ls' :=
       {|
         lscs := lscs ls;
         lmem := lmem ls;
         lvm := vm';
         lfn := lfn ls;
         lpc := lpc ls + 1;
       |}
     in
     eval_instr lp li ls = ok ls'.
Proof.
  set x := {| vname := xname; |}.
  set xi := {| v_var := x; |}.
  set w' := align_word _ _.
  move=> hws hgetx.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite /get_gvar /=.
  rewrite hgetx {hgetx} /=.
  rewrite /exec_sopn /=.
  rewrite !truncate_word_u /=.
  rewrite /sopn_sem /=.
  rewrite /x86_AND /check_size_8_64.
  rewrite hws {hws} /=.
  rewrite sumbool_of_boolET.
  rewrite /with_vm /of_estate pword_of_wordE -/(align_word al w) /=.
  by rewrite addn1.
Qed.


Context
  {call_conv : calling_convention}
  (lp : lprog)
  (sp_rsp : Ident.ident)
  (fn : funname).

Let vrsp : var := mk_ptr sp_rsp.
Let vrspi : var_i := VarI vrsp dummy_var_info.
Let vtmp : var := mk_ptr (lip_tmp x86_liparams).
Let vtmpi : var_i := VarI vtmp dummy_var_info.

Definition x86_spec_lip_allocate_stack_frame s pc ii ts sz :
  let: args := lip_allocate_stack_frame x86_liparams vrspi sz in
  let: i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  let: ts' := pword_of_word (ts - wrepr Uptr sz) in
  let: s' := with_vm s (evm s).[vrsp <- ok ts']%vmap in
  (evm s).[vrsp]%vmap = ok (pword_of_word ts)
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

Definition x86_spec_lip_free_stack_frame s pc ii ts sz :
  let args := lip_free_stack_frame x86_liparams vrspi sz in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  let ts' := pword_of_word (ts + wrepr Uptr sz) in
  let s' := with_vm s (evm s).[vrsp <- ok ts']%vmap in
  (evm s).[vrsp]%vmap = ok (pword_of_word ts)
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

Lemma x86_spec_lip_set_up_sp_register s r ts al sz P Q :
  let: ts' := align_word al (ts - wrepr Uptr sz) in
  let: lcmd := set_up_sp_register x86_liparams vrspi sz al r in
  is_linear_of lp fn (P ++ lcmd ++ Q)
  -> isSome (lip_set_up_sp_register x86_liparams vrspi sz al r)
  -> vtype r = sword Uptr
  -> vtmp <> vrsp
  -> vname (v_var r) \notin (lip_not_saved_stack x86_liparams)
  -> v_var r <> vrsp
  -> get_var (evm s) vrsp = ok (Vword ts)
  -> wf_vm (evm s)
  -> exists vm',
       let: ls := of_estate s fn (size P) in
       let: s' := with_vm s vm' in
       let: ls' := of_estate s' fn (size P + size lcmd) in
       [/\ lsem lp ls ls'
         , wf_vm vm'
         , vm' = (evm s)
             [\ Sv.add (v_var r) (Sv.add vtmp (Sv.add vrsp vflags)) ]
         , get_var vm' vrsp = ok (Vword ts')
         , get_var vm' (v_var r) = ok (Vword ts)
         & forall x,
             Sv.In x vflags
             -> ~ is_ok (vm'.[x]%vmap)
             -> (evm s).[x]%vmap = vm'.[x]%vmap
       ].
Proof.
  move=> hbody _ hr.
  set ts' := align_word _ _.
  move: r hr hbody => [[rtype rname] rinfo] /= ?; subst rtype.
  set r := {| v_info := rinfo; |}.
  move=> hbody _ _ hneq_r_rsp hgetrsp hwf_vm.

  move: hbody.
  set i_mov_r := _ _ (x86_lassign (LLvar r) _ _).
  set i_sub_rsp := _ _ (x86_allocate_stack_frame vrspi _).
  set i_align_rsp := _ _ (x86_op_align vrspi _ _).
  move=> hbody.

  set vm0 := (evm s).[v_var r <- ok (pword_of_word ts)]%vmap.
  set vm2 := vm0.[vrsp <- ok (pword_of_word (ts - wrepr Uptr sz))]%vmap.

  eexists.
  split.

  - apply: lsem_step3; rewrite /lsem1 /step.

    (* R[r] := R[rsp]; *)
    + rewrite -{1}(addn0 (size P)).
      rewrite (find_instr_skip hbody) /=.
      apply: x86_lassign_eval_instr.
      * exact: hgetrsp.
      * exact: truncate_word_u.
        rewrite /write_lval /write_var /=.
        rewrite /with_vm pword_of_wordE -/vm0.
        reflexivity.

    (* R[rsp] := R[rsp] - sz; *)
    + rewrite (find_instr_skip hbody) /=.
      apply: x86_spec_lip_allocate_stack_frame.
      rewrite Fv.setP_neq; last by apply/eqP.
      move: hgetrsp.
      rewrite get_varE.
      case: _.[_]%vmap => //= -[pws w ?].
      move=> [?]; subst pws.
      move=> [?]; subst w.
      rewrite pword_of_wordE.
      reflexivity.

    (* R[rsp] := R[rsp] & alignment; *)
    rewrite addn1 -addn2.
    rewrite (find_instr_skip hbody) /=.
    rewrite -(addn1 2) addnA.
    rewrite -/vm2.
    apply:
      (x86_op_align_eval_instr
         (w := ts - wrepr Uptr sz)
         _ _ _
         (cmp_le_refl _)).
    by t_get_var.

  - repeat apply: wf_vm_set. exact: hwf_vm.

  - move=> x. t_notin_add. by t_vm_get.

  - by t_get_var.

  - by t_get_var.

  rewrite /= -/ts'.
  move=> x /sv_of_listP /mapP [f _ ->].
  case: f; by t_vm_get.
Qed.

Lemma x86_spec_lip_set_up_sp_stack s ts m' al sz off P Q :
  let: ts' := align_word al (ts - wrepr Uptr sz) in
  let: lcmd := set_up_sp_stack x86_liparams vrspi sz al off in
  is_linear_of lp fn (P ++ lcmd ++ Q)
  -> isSome (lip_set_up_sp_stack x86_liparams vrspi sz al off)
  -> vtmp <> vrsp
  -> get_var (evm s) vrsp = ok (Vword ts)
  -> wf_vm (evm s)
  -> write (emem s) (ts' + wrepr Uptr off)%R ts = ok m'
  -> exists vm',
       let: ls := of_estate s fn (size P) in
       let: s' := {| escs := escs s; evm := vm'; emem := m'; |} in
       let: ls' := of_estate s' fn (size P + size lcmd) in
       [/\ lsem (spp := mk_spp) lp ls ls'
         , wf_vm vm'
         , vm' = (evm s) [\ Sv.add vtmp (Sv.add vrsp vflags) ]
         , get_var vm' vrsp = ok (Vword ts')
         & forall x,
             Sv.In x vflags
             -> ~ is_ok (vm'.[x]%vmap)
             -> (evm s).[x]%vmap = vm'.[x]%vmap
       ].
Proof.
  set ts' := align_word _ _.
  move=> hbody _ hneq_tmp_rsp hgetrsp hwf_vm hwrite.

  move: hbody.
  rewrite /=.
  rewrite -[[:: _, _, _, _ & Q]]/([:: _; _; _ ] ++ [:: _ & Q]).
  rewrite -[[:: _; _; _]]/(map _ (x86_set_up_sp_register vrspi sz al vtmpi)).
  move=> hbody.

  have [vm0 [hsem hwf_vm0 hvm0 hgetrsp0 hgettmp0 hflags]] :=
    x86_spec_lip_set_up_sp_register
      (r := vtmpi)
      hbody
      erefl
      erefl
      hneq_tmp_rsp
      erefl
      hneq_tmp_rsp
      hgetrsp
      hwf_vm.

  exists vm0.
  split.

  - apply: (lsem_trans hsem).
    apply: LSem_step.
    rewrite /lsem1 /step /=.
    rewrite (find_instr_skip hbody) /=.
    rewrite
      (x86_lassign_eval_instr
         _
         (s1 := {| escs := escs s; emem := m'; evm := vm0; |})
         _ _ _
         (w := ts)
         (w' := ts)).
    + by rewrite -addnA addn1.
    + exact: hgettmp0.
    + exact: truncate_word_u.
    + rewrite /=.
      rewrite hgetrsp0 {hgetrsp0} /=.
      rewrite !zero_extend_u.
      rewrite -/ts'.
      by rewrite hwrite {hwrite}.

  - exact: hwf_vm0.

  - move=> x hx.
    rewrite hvm0; first done.
    rewrite Sv_equal_add_add.
    exact: hx.

  - exact: hgetrsp0.

  exact: hflags.
Qed.

Definition x86_hlip_lassign
  (s1 s2 : estate) pc ii x e ws li ws' (w : word ws) (w' : word ws') :
  lassign x86_liparams x ws e = Some li
  -> sem_rexpr (emem s1) (evm s1) e = ok (Vword w')
  -> truncate_word ws w' = ok w
  -> write_lexpr x (Vword w) s1 = ok s2
  -> eval_instr lp (MkLI ii li) (of_estate s1 fn pc)
     = ok (of_estate s2 fn pc.+1).
Proof.
  move=> [<-] hseme hw hwritex.
  rewrite (x86_lassign_eval_instr _ _ _ _ hseme hw hwritex).
  by rewrite addn1.
Qed.

End LINEARIZATION.

Definition x86_hliparams {call_conv : calling_convention} : h_linearization_params (ap_lip x86_params) :=
  {|
    spec_lip_allocate_stack_frame := x86_spec_lip_allocate_stack_frame;
    spec_lip_free_stack_frame := x86_spec_lip_free_stack_frame;
    spec_lip_set_up_sp_register := x86_spec_lip_set_up_sp_register;
    spec_lip_set_up_sp_stack := x86_spec_lip_set_up_sp_stack;
    hlip_lassign := x86_hlip_lassign;
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

(* Due to the order of the parameters we can't defined this as a record. *)
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
  -> sem_fexpr (evm m) e = ok v
  -> exists2 v',
       value_of_bool (eval_cond (get_rf rf) c) = ok v' & value_uincl v v'.
Proof.
  rewrite /x86_agparams /eval_cond /get_rf /=.
  move=> eqv; elim: e c v => //.
  + move=> x c v /=; t_xrbindP=> r /of_var_e_boolP ok_r ok_ct ok_v.
    have := xgetflag_ex eqv ok_r ok_v.
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
  case => //=.
  + move=> e1 _ e2 _ c v.
    case: e1 => //= x1; case: e2 => //= x2; t_xrbindP => f1 /of_var_e_boolP ok_f1 f2 /of_var_e_boolP ok_f2.
    case: ifP => // /orP hor [<-] v1 /(xgetflag eqv ok_f1) hv1 v2 /(xgetflag eqv ok_f2) hv2.
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
Qed.

Lemma assemble_extra_op rip ii op lvs args op' lvs' args' op'' asm_args m xs ys m' s :
  sem_rexprs m args = ok xs
  -> exec_sopn (Oasm (ExtOp op)) xs = ok ys
  -> write_lexprs lvs ys m = ok m'
  -> to_asm ii op lvs args = ok (op', lvs', args')
  -> assemble_asm_op x86_agparams rip ii op' lvs' args'
     = ok (op'', asm_args)
  -> lom_eqv rip m s
  -> exists2 s', eval_op op'' asm_args s = ok s' & lom_eqv rip m' s'.
Proof.
  case: op.
  + move=> sz; rewrite /exec_sopn /sopn_sem /=.
    rewrite /Oset0_instr; case: ifP => /= hsz64.
    + case: args => /=; t_xrbindP; last by move => *; subst.
      move => <-{xs} _ /ok_inj <- /= <-{ys}.
      move => hw x.
      case: rev => [ // | [ // | d ] ds ] /ok_inj <-{x} <-{op'} <-{lvs'} <-{args'}.
      rewrite /assemble_asm_op.
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
    case: xs => // ok_xs /ok_inj <-{ys} hw.
    case: rev => [ // | [ // | d ] ds ] /ok_inj[] <-{op'} <-{lvs'} <-{args'}.
    rewrite /assemble_asm_op.
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
    exact: (@compile_lvals _ _ _ _ _ _ _ _ _ _ _
               rip ii m lvs m' s [:: a0; XReg r; XReg r]
               id.(id_out) id.(id_tout)
               (0%R: word sz)
               (reg_msb_flag sz) (refl_equal _) hw hlo hcd id.(id_check_dest)).
  + case: args => // h [] // [] // [] // x [] //=.
    rewrite /exec_sopn /sopn_sem /=.
    t_xrbindP => vh hvh _ vl hvl <- <-{xs} ?.
    t_xrbindP => ? hwh ? hwl <- <-{ys} /= hwr <-{op'} <-{lvs'} <-{args'}.
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
    rewrite zero_extend_u /winserti128 => hu /=.
    do 2! f_equal; rewrite /split_vec /=.
    move: hwl hu; rewrite /to_word.
    case: (vl) => // [ws wl' /= | []//].
    rewrite /truncate_word /word_uincl mul0n.
    case: ifP => // hle.
    rewrite (@subword0 U128 U256) // => -[] <- /andP [] _ /eqP ->.
    by rewrite zero_extend_idem.
  case: lvs => // -[] // x [] //.
  rewrite /exec_sopn /sopn_sem /=.
  case: xs => //; t_xrbindP => vs1 [] // hva _ va htwa /ok_inj <- <-{ys}.
  t_xrbindP => _ m1 hwx <- <-{m'} <-{op'} <-{lvs'} <-{args'}.
  rewrite /assemble_asm_op.
  t_xrbindP => asm_args' _ hc.
  case hci: enforce_imm_i_args_kinds =>
    {asm_args} [asm_args|//] _ [<-] /andP [hca hcd] <- <- hlo.
  have {hci} hidc := filter_i_args_kinds_no_imm_correct (enforce_imm_i_args_kinds_correct hci).
  case: asm_args hidc hcd hca => // a0 [ | a1 [] ]; only 1, 3: by rewrite /check_args_kinds /= !andbF.
  move => hidc hcd.
  have := size_mapM hva.
  case: args hva => // r0 [] //=; t_xrbindP => q hva ? _; subst q.
  rewrite andbT => hca1.
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
  rewrite -xr => -[<-]{m1}.
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
    hap_hpip := x86_hpiparams;
    hap_hsap := x86_hsaparams;
    hap_hlip := x86_hliparams;
    ok_lip_tmp := x86_ok_lip_tmp;
    hap_hlop := x86_hloparams;
    hap_hagp := x86_hagparams;
    hap_is_move_opP := x86_is_move_opP;
  |}.

End Section.
