From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype finfun.
From mathcomp Require Import ssralg word_ssrZ.

Require Import
  arch_params_proof
  compiler_util
  expr
  fexpr
  fexpr_sem
  fexpr_facts
  psem
  psem_facts
  one_varmap
  sem_one_varmap.
Require Import
  linearization
  linearization_proof
  lowering
  slh_lowering
  slh_lowering_proof
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
  x86_decl
  x86_extra
  x86_instr_decl
  x86
  x86_lowering
  x86_lowering_proof
  x86_stack_zeroization_proof.
Require Export x86_params.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Existing Instance withsubword.

Section Section.
Context {atoI : arch_toIdent} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.


(* ------------------------------------------------------------------------ *)
(* Stack alloc hypotheses. *)

Section STACK_ALLOC.
Context {dc : DirectCall} (P' : sprog).

Lemma lea_ptrP s1 e i x tag ofs w s2 :
  P'.(p_globs) = [::]
  -> (Let i' := sem_pexpr true [::] s1 e in to_pointer i') = ok i
  -> write_lval true [::] x (Vword (i + wrepr _ ofs)) s1 = ok s2
  -> psem.sem_i (pT := progStack) P' w s1 (lea_ptr x e tag ofs) s2.
Proof.
  move=> P'_globs he hx.
  constructor.
  rewrite /sem_sopn /= P'_globs /sem_sop2 /=.
  move: he; t_xrbindP=> _ -> /= -> /=.
  by rewrite /exec_sopn truncate_word_u /= truncate_word_u /= hx.
Qed.

Lemma x86_mov_ofsP_aux s1 e i x tag ofs w vpk s2 ins :
  p_globs P' = [::]
  -> (Let i' := sem_pexpr true [::] s1 e in to_pointer i') = ok i
  -> sap_mov_ofs x86_saparams x tag vpk e ofs = Some ins
  -> write_lval true [::] x (Vword (i + wrepr Uptr ofs)) s1 = ok s2
  -> psem.sem_i (pT := progStack) P' w s1 ins s2.
Proof.
  move=> P'_globs he.
  rewrite /x86_saparams /= /x86_mov_ofs => -[<-] /=.
  case: (mk_mov vpk).
  - exact: lea_ptrP.
  case: eqP => [-> | _].
  + rewrite wrepr0 GRing.addr0 -P'_globs.
    by apply :(mov_wsP (sCP := sCP_stack)); rewrite // P'_globs.
  exact: lea_ptrP.
Qed.

Lemma x86_mov_ofsP s1 e i x tag ofs w vpk s2 ins :
  p_globs P' = [::]
  -> (Let i' := sem_pexpr true [::] s1 e in to_pointer i') = ok i
  -> sap_mov_ofs x86_saparams x tag vpk e ofs = Some ins
  -> write_lval true [::] x (Vword (i + wrepr Uptr ofs)) s1 = ok s2
  -> exists2 vm2, psem.sem_i (pT := progStack) P' w s1 ins (with_vm s2 vm2) & evm s2 =1 vm2.
Proof.
  move=> heq he hmov hw; exists (evm s2) => //.
  rewrite with_vm_same.
  apply: x86_mov_ofsP_aux heq he hmov hw.
Qed.

Lemma x86_immediateP w s (x: var_i) z :
  vtype x = sword Uptr
  -> psem.sem_i (pT := progStack) P' w s (x86_immediate x z) (with_vm s (evm s).[x <- Vword (wrepr Uptr z)]).
Proof.
  case: x => - [] [] // [] // x xi _ /=.
  have := mov_wsP (pT := progStack) AT_none _ (cmp_le_refl _).
  move => /(_ _ _ _ _ _ _ _ P').
  apply; last reflexivity.
  by rewrite /= truncate_word_u.
Qed.

Lemma x86_swapP rip s tag (x y z w : var_i) (pz pw: pointer):
  vtype x = spointer -> vtype y = spointer ->
  vtype z = spointer -> vtype w = spointer ->
  (evm s).[z] = Vword pz ->
  (evm s).[w] = Vword pw ->
  psem.sem_i (pT := progStack) P' rip s (x86_swap tag x y z w)
       (with_vm s ((evm s).[x <- Vword pw]).[y <- Vword pz]).
Proof.
  move=> hxty hyty hzty hwty hz hw.
  constructor; rewrite /sem_sopn /= /get_gvar /= /get_var /= hz hw /=.
  rewrite /exec_sopn /= !truncate_word_u /= /write_var /set_var /=.
  rewrite hxty hyty //=.
Qed.

End STACK_ALLOC.

Definition x86_hsaparams {dc : DirectCall} : h_stack_alloc_params (ap_sap x86_params) :=
  {|
    mov_ofsP := x86_mov_ofsP;
    sap_immediateP := x86_immediateP;
    sap_swapP := x86_swapP;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization hypotheses. *)

Section LINEARIZATION.

Definition vm_op_align
  (vm : Vm.t) (x : var) (ws : wsize) (w : word ws) : Vm.t :=
  vm
    .[to_var OF <- false]
    .[to_var CF <- false]
    .[to_var SF <- SF_of_word w]
    .[to_var PF <- PF_of_word w]
    .[to_var ZF <- ZF_of_word w]
    .[x <- Vword w].

Context {call_conv : calling_convention}.

Lemma x86_spec_lip_allocate_stack_frame :
  allocate_stack_frame_correct x86_liparams.
Proof.
  move=> sp_rsp tmp s ts sz _ Hvm.
  rewrite /= Hvm /= /eval_instr /= /sem_sopn /sem_sop2 /exec_sopn /= !truncate_word_u /= truncate_word_u /=.
  eexists; split; first reflexivity.
  + by move=> z hz; rewrite Vm.setP_neq //; apply /eqP; SvD.fsetdec.
  by rewrite Vm.setP_eq vm_truncate_val_eq.
Qed.

Lemma x86_spec_lip_free_stack_frame :
  free_stack_frame_correct x86_liparams.
Proof.
  move=> sp_rsp tmp s ts sz _ Hvm.
  rewrite /= Hvm /= /eval_instr /= /sem_sopn /sem_sop2 /exec_sopn /= !truncate_word_u /= truncate_word_u /=.
  eexists; split; first reflexivity.
  + by move=> z hz; rewrite Vm.setP_neq //; apply /eqP; SvD.fsetdec.
  by rewrite Vm.setP_eq vm_truncate_val_eq.
Qed.

Lemma x86_spec_lip_set_up_sp_register :
  set_up_sp_register_correct x86_liparams.
Proof.
  move=> [ [? nrsp] vi1] [[ ? nr] vi2] tmp ts al sz s + /= ?? _ _ +  _ /=; subst.
  set vrsp := {| vname := nrsp |}; set rsp := {| v_var := vrsp |}.
  set r := {| vname := nr |} => hget hne.
  rewrite hget /= /exec_sopn /= truncate_word_u /=.
  rewrite -cats1 sem_fopns_args_cat.
  set vm0 := (evm s).[r <- Vword ts].
  set vm2 := if sz != 0%Z then vm0.[vrsp <- Vword (ts - wrepr Uptr sz)] else vm0.
  set ts' := align_word _ _.
  set vm3 := vm_op_align vm2 vrsp ts'.
  have -> /= :
    sem_fopns_args (with_vm s vm0)
       (if sz != 0%Z then x86_allocate_stack_frame rsp None sz else [::]) = ok (with_vm s vm2).
  + rewrite /vm2; case: eqP => hsz //=.
    rewrite get_var_neq // hget /= /sem_sop2 /= !truncate_word_u /=.
    by rewrite /exec_sopn /= truncate_word_u /=.
  have -> /= : get_var true vm2 vrsp = ok (Vword (ts - wrepr U64 sz)).
  + rewrite /vm2; case: eqP => ? /=.
    + by subst sz; rewrite get_var_neq // hget wrepr0 GRing.subr0.
    by rewrite get_var_eq.
  rewrite /exec_sopn /= !truncate_word_u /=; exists vm3; split => //.
  - move=> x. t_notin_add.
    by t_vm_get; rewrite /vm2; case: ifP; t_vm_get.

  - by t_get_var.

  - t_get_var; rewrite /vm2 /vm0 => {vm3 vm2 vm0}.
    by t_get_var; case: ifP; t_get_var.

  rewrite /= -/ts'.
  move=> x /sv_of_listP /mapP [f _ ->].
  rewrite Vm.setP_neq //.
  case: f;
    by repeat (rewrite Vm.setP_neq; last by apply /eqP => h; have := inj_to_var h); rewrite Vm.setP_eq.
Qed.

Lemma x86_lassign_correct s x ws e (w : word ws) s':
  let lcmd := x86_lassign x ws e in
  sem_rexpr (emem s) (evm s) e >>= to_word ws = ok w ->
  write_lexpr x (Vword w) s = ok s' ->
  sem_fopn_args lcmd s = ok s'.
Proof.
  move=> /=; t_xrbindP => v -> /= hv hwr.
  rewrite /exec_sopn /=.
  case: ifP => /= h; rewrite hv /= /sopn_sem /=.
  + by rewrite /x86_MOV /= /check_size_8_64 h /= hwr.
  by rewrite /x86_VMOVDQ (wsize_nle_u64_check_128_256 h) /= hwr.
Qed.

Lemma x86_lmove_correct : lmove_correct x86_liparams.
Proof.
  move=> xd xs w ws w' s htxd htxs hget htr.
  rewrite /x86_liparams /lip_lmove /x86_lmove.
  rewrite htxd; apply: x86_lassign_correct => /=.
  + by rewrite hget /= htr.
  by rewrite set_var_eq_type ?htxd.
Qed.

Lemma x86_lstore_correct : lstore_correct_aux x86_check_ws x86_lstore.
Proof.
  move=> xd xs ofs ws w wp s m htxs _ hgetd hgets hwr.
  rewrite /x86_lstore htxs.
  apply: x86_lassign_correct => /=; first by apply hgets.
  by rewrite hgetd /= !truncate_word_u /= hwr.
Qed.

Lemma x86_lstores_correct : lstores_correct x86_liparams.
Proof. apply/lstores_dfl_correct/x86_lstore_correct. Qed.

Lemma x86_lload_correct : lload_correct_aux (lip_check_ws x86_liparams) x86_lload.
Proof.
  move=> xd xs ofs s vm top hgets.
  case heq: vtype => [|||ws] //; t_xrbindP.
  move=> _ <- hchk w hread hset.
  rewrite /x86_lload heq.
  apply: x86_lassign_correct => /=.
  + by rewrite hgets /= truncate_word_u /= hread /= truncate_word_u.
  by rewrite hset.
Qed.

Lemma x86_lloads_correct : lloads_correct x86_liparams.
Proof. apply/lloads_dfl_correct/x86_lload_correct. Qed.

Lemma x86_tmp_correct : lip_tmp x86_liparams <> lip_tmp2 x86_liparams.
Proof. by move=> h; assert (h1 := inj_to_ident h). Qed.

Lemma x86_check_ws_correct : lip_check_ws x86_liparams Uptr.
Proof. done. Qed.

End LINEARIZATION.

Definition x86_hliparams {call_conv : calling_convention} : h_linearization_params (ap_lip x86_params) :=
  {|
    spec_lip_allocate_stack_frame := x86_spec_lip_allocate_stack_frame;
    spec_lip_free_stack_frame     := x86_spec_lip_free_stack_frame;
    spec_lip_set_up_sp_register   := x86_spec_lip_set_up_sp_register;
    spec_lip_lmove                := x86_lmove_correct;
    spec_lip_lstore               := x86_lstore_correct;
    spec_lip_lstores              := x86_lstores_correct;
    spec_lip_lloads               := x86_lloads_correct;
    spec_lip_tmp                  := x86_tmp_correct;
    spec_lip_check_ws             := x86_check_ws_correct;
  |}.

Lemma x86_ok_lip_tmp :
  exists r : reg_t, of_ident (lip_tmp (ap_lip x86_params)) = Some r.
Proof.
  by exists RAX; rewrite /= to_identK.
Qed.

Lemma x86_ok_lip_tmp2 :
  exists r : reg_t, of_ident (lip_tmp2 (ap_lip x86_params)) = Some r.
Proof.
  by exists R10; rewrite /= to_identK.
Qed.

(* ------------------------------------------------------------------------ *)
(* Lowering hypotheses. *)

(* Due to the order of the parameters we can't defined this as a record. *)
Definition x86_hloparams {dc : DirectCall} : h_lowering_params (ap_lop x86_params).
Proof.
  split. exact: @lower_callP.
Defined.

(* ------------------------------------------------------------------------ *)
(* Assembly generation hypotheses. *)

Section ASM_GEN.

Notation assemble_extra_correct :=
  (assemble_extra_correct x86_agparams) (only parsing).


(* FIXME: Is there a way of avoiding this import? *)
Import arch_sem.

Lemma not_condtP (c : cond_t) rf b :
  x86_eval_cond rf c = ok b -> x86_eval_cond rf (not_condt c) = ok (negb b).
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
  x86_eval_cond rf c1 = ok b1 ->
  x86_eval_cond rf c2 = ok b2 ->
  x86_eval_cond rf c  = ok (b1 || b2).
Proof.
  case: c1 => //; case: c2 => //= -[<-] /=.
  + by case: (rf _) => // ? [->]; case: (rf _) => // ? [->].
  + by case: (rf _) => // ? [->]; case: (rf _) => // ? [->] /=; rewrite orbC.
  + by case: (rf ZF) => // ? [->]; case: (rf SF) => //= ?; case: (rf _) => //= ? [<-].
  by case: (rf SF) => //= ?; case: (rf _) => //= ? [<-]; case: (rf _) => //= ? [->]; rewrite orbC.
Qed.

Lemma and_condtP ii e c1 c2 c rf b1 b2:
  and_condt ii e c1 c2 = ok c ->
  x86_eval_cond rf c1 = ok b1 ->
  x86_eval_cond rf c2 = ok b2 ->
  x86_eval_cond rf c  = ok (b1 && b2).
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

Lemma eval_assemble_cond : assemble_cond_spec x86_agparams.
Proof.
  move=> ii m rr rf e c v; rewrite /x86_agparams /x86_eval_cond /get_rf /=.
  move=> eqr eqv; elim: e c v => //.
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

Lemma assemble_mov ii rip m m' s i x op args:
  lom_eqv rip m s ->
  write_lexpr x (Vword (wrepr U64 i)) m = ok m' ->
  assemble_asm_op x86_agparams rip ii (None, MOV U64) [:: x] [:: re_i U64 i] = ok (op, args) ->
  exists2 s' : asmmem, Let acc := eval_op op args s in ok acc = ok s' & lom_eqv rip m' s'.
Proof.
  move=> hlo hw hass; assert (h := assemble_asm_opI hass).
  case: h => hca hcd hidc -> /=.
  have he : sem_rexprs m [:: re_i U64 i] = ok [:: Vword (wrepr U64 i)] by done.
  have hws : write_lexprs [:: x] [::Vword (wrepr U64 i)] m = ok m' by rewrite /= hw.
  have [] := compile_asm_opn_aux eval_assemble_cond he _ hws hca hcd hidc hlo.
  + by rewrite /exec_sopn /= truncate_word_u.
  by rewrite /eval_op => s' -> ?; exists s'.
Qed.

Lemma lom_eqv_set_xreg rip (xr : xreg_t) m s :
  lom_eqv rip m s ->
  lom_eqv rip (with_vm m (evm m).[to_var xr <- Vword (asm_xreg s xr)]) s.
Proof.
  case => h1 h2 h3 h4 h5 h6 h7 h9; split => //; rewrite /eqflags /get_var /=.
  + by rewrite Vm.setP_neq //; apply/eqP; case: h4; auto.
  1,2,4: by move=> x; rewrite Vm.setP_neq; auto.
  move=> x; case: (to_var xr =P to_var x) => [h | /eqP hne].
  + move: (inj_to_var h) => ->. by rewrite Vm.setP_eq.
  by rewrite Vm.setP_neq; auto.
Qed.

Lemma check_sopn_args_xmm rip ii oargs es ads cond n k ws:
  check_sopn_args x86_agparams rip ii oargs es ads ->
  check_i_args_kinds [::cond] oargs ->
  nth (Eu 0, sword8) ads n = (Eu k, sword ws) ->
  nth xmm cond k = xmm ->
  n < size es ->
  exists (r: xreg_t),
   exists2 vi,
    nth (Rexpr (Fconst 0)) es n = Rexpr (Fvar {| v_var := to_var r;  v_info := vi |}) &
    oseq.onth oargs k = Some (XReg r).
Proof.
  rewrite /= orbF => hca hc hE hxmm hn.
  have /(_ n):= all2_nth (Rexpr (Fconst 0)) (Eu 0, sword8) _ hca.
  rewrite hn => /(_ erefl) ha.
  assert (hcIaux := check_sopn_argP ha).
  move: hcIaux; rewrite hE => h; inversion_clear h.
  rewrite H; move: H => /(oseq.onthP (Imm (wrepr U8 0))) /andP [hk] /eqP heqa.
  have : check_arg_kinds (nth (Imm (wrepr U8 0)) oargs k) (nth xmm cond k).
  + by have /(_ k) := all2_nth (Imm (wrepr U8 0)) xmm _ hc; rewrite hk; apply.
  rewrite heqa hxmm.
  rewrite /check_arg_kinds /= orbF.
  move: H1; rewrite /compat_imm /= => {heqa H2}.
  case: a => // r /orP [/eqP ? _ | ]; last by case a'.
  subst a'; case: nth H0 => /=; first by t_xrbindP.
  case => //; last by case=> // ? -[] //=; t_xrbindP.
  move=> [v vi] h;
    assert (h1 := xreg_of_varI h);
    move: (of_varI h1) => /= <-;
    eauto.
Qed.

Lemma check_sopn_dests_xmm rip ii oargs xs ads cond n al k ws:
  check_sopn_dests x86_agparams rip ii oargs xs ads ->
  check_i_args_kinds [::cond] oargs ->
  nth (Ea 0, sword8) ads n = (ADExplicit (AK_mem al) k None, sword ws) ->
  nth xmm cond k = xmm ->
  n < size xs ->
  exists (r: xreg_t),
   exists2 vi,
    nth (LLvar (mk_var_i rip)) xs n =
       LLvar {| v_var := to_var r;  v_info := vi |} &
    oseq.onth oargs k = Some (XReg r).
Proof.
  rewrite /= orbF => hca hc hE hxmm hn.
  have /(_ n):= all2_nth (Rexpr (Fconst 0)) (Ea 0, sword8) _ hca.
  rewrite size_map hn => /(_ erefl).
  rewrite (nth_map (LLvar (mk_var_i rip))) //.
  set e := nth (LLvar _) _ _.
  rewrite /check_sopn_dest hE /=.
  case H : oseq.onth => [a | //].
  move: H => /(oseq.onthP (Imm (wrepr U8 0))) /andP [hk] /eqP heqa.
  have : check_arg_kinds (nth (Imm (wrepr U8 0)) oargs k) (nth xmm cond k).
  + by have /(_ k) := all2_nth (Imm (wrepr U8 0)) xmm _ hc; rewrite hk; apply.
  rewrite heqa hxmm.
  case heq : assemble_word_load => [ a' | //]; rewrite andbT.
  rewrite /check_arg_kinds /= orbF => ha /eqP ?; subst a' => {heqa}.
  case: a heq ha => // r heq _; exists r.
  case: e heq => /=; t_xrbindP => //.
  move=> [v vi] h;
    assert (h1 := xreg_of_varI h);
    move: (of_varI h1) => /= <-;
    eauto.
Qed.

Lemma assemble_extra_concat128 rip ii lvs args m xs ys m' s ops ops' :
  sem_rexprs m args = ok xs ->
  exec_sopn (Oasm (ExtOp Oconcat128)) xs = ok ys ->
  write_lexprs lvs ys m = ok m' ->
  to_asm ii Oconcat128 lvs args = ok ops ->
  mapM (fun '(op0, ls, rs) => assemble_asm_op x86_agparams rip ii op0 ls rs) ops = ok ops' ->
  lom_eqv rip m s ->
  exists2 s' : asmmem,
    foldM (fun '(op'', asm_args) => [eta eval_op op'' asm_args]) s ops' = ok s' & lom_eqv rip m' s'.
Proof.
  case: args => // h [] // [] // [] // [l li] [] //=.
  rewrite /exec_sopn /sopn_sem /=.
  t_xrbindP => vh hvh _ vl hvl <- <-{xs}.
  t_xrbindP => _ wh hwh wl hwl <- <-{ys} /=.
  case: lvs => // y [] /=; t_xrbindP => // z hw ? hops hmap hlow; subst z.
  have hwr : write_lexprs [::y] [::Vword (make_vec U256 [:: wl; wh])] m = ok m' by rewrite /= hw.
  move: hmap; rewrite -hops /=; t_xrbindP => -[op oargs] hass hops'.
  assert (h1 := assemble_asm_opI hass); case: h1 => hca hcd hidc ?; subst op => {hass}.
  have [lr [vi /= [??] hlr]]:= check_sopn_args_xmm (n:= 0) hca hidc erefl erefl erefl; subst l vi.
  have [yr [vi /= ? hyr]] := check_sopn_dests_xmm (n:=0) hcd hidc erefl erefl erefl; subst y ops ops'.
  have [s' hwm hlow'] :=
    compile_lvals (asm_e:=x86_extra)
     (id_out := [:: Eu 0]) (id_tout := [:: sword256]) MSB_CLEAR refl_equal hwr hlow hcd refl_equal.
  exists s'; last done.
  move: hca; rewrite /check_sopn_args /= => /and4P [] _ hE2 hE3 _.
  have [vh' hev2 /= hvh']:= check_sopn_arg_sem_eval eval_assemble_cond hlow hE2 hvh hwh.
  have := check_sopn_arg_sem_eval eval_assemble_cond hlow hE3.
  move=> /(_ (Vword (wrepr U8 1)) (wrepr U8 1) erefl (truncate_word_u _)) [v1 hev3 /= hv1] {hcd hwr hlow' hE2 hE3 hw}.
  move: hidc hyr hlr hev2 hev3 hwm.
  case: oargs => // a0 [] // a1 [] // a2 [] // a3 l hcheck /= [?] [?] hev2 hev3 /= hwm; subst a0 a1.
  rewrite /eval_op /= /exec_instr_op /= /eval_instr_op hcheck /= hev2 hev3 /= hvh' hv1 /=.
  move: hwm; rewrite /mem_write_vals /= /mem_write_val /= !truncate_word_u /= truncate_word_u /= => <-; do 2!f_equal.
  rewrite  /winserti128 /split_vec /=; f_equal.
  congr (fun x => [::x; wh]).
  case: hlow => _ _ _ _ _ _ hu _.
  move /get_varP: hvl => -[]/= ? hd _; subst vl.
  have := hu lr.
  case: (evm m).[to_var lr] hd hwl => //= ws wl' _ /truncate_wordP [] hle ? /andP[] _ /eqP ?; subst.
  rewrite /word_uincl mul0n.
  by rewrite (@subword0 U128 U256) zero_extend_idem.
Qed.

Lemma assemble_slh_move_correct : assemble_extra_correct Ox86SLHmove.
Proof.
  move=> rip ii les res m xs ys m' s ops ops' hes hexec hwrite [?] hmap hlo;
    subst ops.
  apply: (assemble_opsP eval_assemble_cond hmap erefl _ hlo).
  clear hmap hlo.

  move: hexec.
  rewrite /= hes /exec_sopn /= /sopn_sem /=.
  clear hes.

  case: xs => //.
  t_xrbindP=> vx [|//] w w' hw [?] ?; subst w' ys.
  case: ifP => _; by rewrite /= hw /= hwrite.
Qed.

Lemma assemble_extra_op op : assemble_extra_correct op.
Proof.
  move=> rip ii lvs args m xs ys m' s ops ops'.
  case: op => //.
  (* Oset0 *)
  + move=> sz; rewrite /exec_sopn /sopn_sem /=.
    rewrite /Oset0_instr; case: ifP => /= hsz64.
    + case: args => /=; t_xrbindP; last by move => *; subst.
      move => <-{xs} _ /ok_inj <- /= <-{ys} hw x.
      case: rev => [ // | [ // | d ] ds ] /ok_inj <-{x} <- /=.
      t_xrbindP => -[op' asm_args] hass <- hlo /=.
      assert (h := assemble_asm_opI hass); case: h=> hca hcd hidc -> /= {hass}.
      move: hca; rewrite /check_sopn_args /= => /and3P [].
      rewrite /check_sopn_arg /=.
      case: asm_args hidc hcd => //= a0 [ // | ] a1 [] //= hidc hcd;
       last by rewrite /check_args_kinds /= !andbF.
      case ok_y: xreg_of_var => [y|//].
      assert (h := xreg_of_varI ok_y); move: h => {ok_y} ok_y.
      rewrite !andbT /compat_imm.
      case: y ok_y => // r xr; rewrite !orbF => /eqP ? /eqP ? _; subst a0 a1; only 2-3: by [].
      rewrite /eval_op /exec_instr_op /= /eval_instr_op /=.
      rewrite truncate_word_le // /x86_XOR /check_size_8_64 hsz64 /= wxor_xx.
      set id := instr_desc_op (XOR sz).
      rewrite /SF_of_word msb0.
      by have [s' -> /= ?]:= (@compile_lvals _ _ _ _ _ _ _ _ _ _ _
             rip ii m lvs m' s [:: Reg r; Reg r]
             id.(id_out) id.(id_tout)
             (let vf := Some false in let: vt := Some true in (::vf, vf, vf, vt, vt & (0%R: word sz)))
             (reg_msb_flag sz) (refl_equal _) hw hlo hcd id.(id_check_dest)); eauto.
    case: xs => // ok_xs /ok_inj <-{ys} hw.
    case: rev => [ // | [ // | d ] ds ] /ok_inj <-{ops} /=.
    t_xrbindP => -[op' asm_args] hass <- hlo /=.
    assert (h := assemble_asm_opI hass); case: h=> hca hcd hidc -> /= {hass}.
    move: hca; rewrite /check_sopn_args /= => /and3P [].
    rewrite /check_sopn_arg /=.
    case: asm_args hidc hcd => //= a0 [// | ] a1 [] //= a2 [] //=;
      last by rewrite /check_args_kinds /= !andbF.
    rewrite orbF => hidc hcd.
    case ok_y: xreg_of_var => [y|//].
    assert (h := xreg_of_varI ok_y); move: h => {ok_y} ok_y.
    rewrite !andbT /compat_imm.
    case: y ok_y => // r xr; rewrite !orbF => /eqP ? /eqP ? _; subst a1 a2.
    1-2: by move: hidc; rewrite /check_args_kinds /= andbF.
    rewrite /eval_op /exec_instr_op /= /eval_instr_op /=.
    rewrite truncate_word_le; last exact: wsize_ge_U256.
    rewrite /x86_VPXOR hidc /= /x86_u128_binop /check_size_128_256 wsize_ge_U256.
    have -> /= : (U128 ≤ sz)%CMP by case: (sz) hsz64.
    rewrite wxor_xx; set id := instr_desc_op (VPXOR sz).
    by have [s' -> /= ?] := (@compile_lvals _ _ _ _ _ _ _ _ _ _ _
               rip ii m lvs m' s [:: a0; XReg r; XReg r]
               id.(id_out) id.(id_tout)
               (0%R: word sz)
               (reg_msb_flag sz) (refl_equal _) hw hlo hcd id.(id_check_dest)); eauto.
  (* Oconcat128 *)
  + by apply assemble_extra_concat128.

  (* Ox86MOVZX32 *)
  + case: lvs => // -[] // x [] //.
    rewrite /exec_sopn /sopn_sem /=.
    case: xs => //; t_xrbindP => vs1 [] // hva _ va htwa /ok_inj <- <-{ys}.
    t_xrbindP => _ m1 hwx <- <-{m'} <-{ops} /=.
    t_xrbindP => -[op' asm_args] hass <- hlow /=.
    assert (h1 := assemble_asm_opI hass); case: h1 => hca hcd hidc -> /= {hass}.
    case: asm_args hidc hcd hca => // a0 [ | a1 [] ]; only 1, 3: by rewrite /check_args_kinds /= !andbF.
    move => hidc hcd.
    have := size_mapM hva.
    case: args hva => // r0 [] //=; t_xrbindP => q hva ? _; subst q.
    rewrite andbT => hca1.
    rewrite /eval_op /exec_instr_op /= /eval_instr_op /=.
    rewrite /= in hidc;rewrite hidc.
    have [v' /= -> /= -> /=] :=
      check_sopn_arg_sem_eval eval_assemble_cond hlow hca1 hva htwa.
    move: hcd; rewrite /check_sopn_dests /= /check_sopn_dest /= => /andP -[].
    case ok_y: xreg_of_var => [y|//].
    assert (h := xreg_of_varI ok_y); move: h => {ok_y} ok_y.
    rewrite andbT => /eqP ? _; subst a0.
    case: y hidc hca1 ok_y => // r hidc hca1 xr.
    have {xr} xr := of_varI xr.
    rewrite /mem_write_vals.
    eexists.
    * by rewrite /mem_write_val /= truncate_word_u /=.
    move: hwx; rewrite /write_var /set_var.
    rewrite -xr => -[<-]{m1}.
    apply: (lom_eqv_write_reg _ _ hlow).
    by right.

  (* Ox86MULX *)
  + move=> sz. rewrite /exec_sopn /sopn_sem /=.
    case lvs => // -[] // hi [] // [] // lo [] //.
    t_xrbindP => hargs whilo hwhilo <- /=.
    t_xrbindP => _ _ /set_varP [hdb1 htr1 ->] <- _ _ /set_varP [hdb2 htr2 ->] <- <- _ hne <- <- /=.
    t_xrbindP => -[op' asm_args] hass <- hlow /=.
    assert (h1 := assemble_asm_opI hass); case: h1 => hca hcd hidc -> /= {hass}.
    have hex: exec_sopn (Oasm (BaseOp (None, MULX_lo_hi sz))) xs = ok [:: Vword whilo.2; Vword whilo.1].
    + rewrite /exec_sopn /sopn_sem /=.
      case: (xs) hwhilo => // v1; t_xrbindP => -[] // v2; t_xrbindP => -[] // w1 -> w2 ->.
      by rewrite /x86_MULX /x86_MULX_lo_hi; t_xrbindP => -> /= <- /=.
    have hw' :
       write_lexprs [:: LLvar lo; LLvar hi] [:: Vword whilo.2; Vword whilo.1] m =
       ok (with_vm m ((evm m).[lo <- Vword whilo.2]).[hi <- Vword whilo.1]).
    + by rewrite /= /set_var hdb1 htr1 hdb2 htr2 /= with_vm_idem.
    have [s' {hw' hex hca hcd hidc} /=] :=
      compile_asm_opn_aux eval_assemble_cond hargs hex hw' hca hcd hidc hlow.
    rewrite /eval_op /= => -> /= hlow'.
    exists s' => //; apply: lom_eqv_ext hlow' => /= z.
    by rewrite !Vm.setP; case eqP => [<- | //]; rewrite (negbTE hne).

  (* Ox86MULX_hi *)
  + move=> sz. rewrite /exec_sopn /sopn_sem /=.
    case lvs => // -[] // hi [] //.
    t_xrbindP => hargs whi hwhi <- /=.
    t_xrbindP => _ _ /set_varP [hdb1 htr1 ->] <- <- _ <- <- /=.
    t_xrbindP => -[op' asm_args] hass <- hlow /=.
    assert (h1 := assemble_asm_opI hass); case: h1 => hca hcd hidc -> /= {hass}.
    case: xs hargs hwhi => // v1; t_xrbindP => -[] // v2; t_xrbindP => -[] // hargs w1 hv1 w2 hv2.
    rewrite /x86_MULX_hi; t_xrbindP => hsz hwhi; pose wlo := (wumul w1 w2).2.
    have hex: exec_sopn (Oasm (BaseOp (None, MULX_lo_hi sz))) [:: v1; v2] = ok [:: Vword wlo; Vword whi].
    + by rewrite /exec_sopn /sopn_sem /= hv1 hv2 /= /x86_MULX_lo_hi hsz /= -hwhi /wlo /wmulhu /wumul /=.
    have hw' :
       write_lexprs [:: LLvar hi; LLvar hi] [:: Vword wlo; Vword whi] m =
       ok (with_vm m ((evm m).[hi <- Vword wlo]).[hi <- Vword whi]).
    + by rewrite /= /set_var hdb1 htr1 /=; move: htr1 => /=; case: vtype.
    have [s' {hw' hex hca hcd hidc} /=] :=
      compile_asm_opn_aux eval_assemble_cond hargs hex hw' hca hcd hidc hlow.
    rewrite /eval_op /= => -> /= hlow'.
    exists s' => //; apply: lom_eqv_ext hlow' => /= z.
    by rewrite !Vm.setP; case eqP.

  (* SLHinit *)
  + rewrite /exec_sopn /= /sopn_sem /assemble_slh_init /=; t_xrbindP.
    case: xs => // hargs _ [<-] <-.
    case: lvs => // x [] /=; t_xrbindP => // m1 hw ? <- /=; subst m1.
    t_xrbindP => z [op oargs] hass <- <- hlo /=.
    by rewrite -(wrepr0 U64) in hw; apply (assemble_mov hlo hw hass).

  (* SLHupdate *)
  + rewrite /exec_sopn /= /sopn_sem /= /x86_se_update_sem /=; t_xrbindP.
    case: xs => // vb; t_xrbindP => -[] // vw; t_xrbindP => -[] // hargs.
    move=> _ b hb w hw [<-] <- /=.
    case: lvs => //= aux; t_xrbindP => -[] //= x []; t_xrbindP => //=.
    move=> m1 hw1 m2 hw2 [<-].
    rewrite /assemble_slh_update.
    case: aux hw1 => // vaux hw1.
    case: args hargs => // -[] // eb [] // emsf [] // hargs.
    t_xrbindP => /andP []; rewrite negb_or => /andP [] haux1 haux2 /eqP haux <- /=.
    t_xrbindP => -[op oargs] hass _ [op' oargs'] hasscmov <- <- hlo /=.
    have [s1 {hass hlo}] := assemble_mov hlo hw1 hass.
    t_xrbindP => _ -> -> hlo /=.
    assert (h := assemble_asm_opI hasscmov); case: h => hca hcd hidc -> /= {hasscmov}.
    move: hw1 => /=; t_xrbindP => vm hset ?; subst m1.
    have hes : sem_rexprs (with_vm m vm) [:: Rexpr (Fapp1 Onot eb); Rexpr (Fvar vaux); emsf] =
                 ok [:: Vbool (~~b); Vword (wrepr U64 (-1)); vw].
    + move: hargs => /=; t_xrbindP.
      rewrite (free_varsP (vm2:= vm)); last by apply: set_var_disjoint_eq_on haux1 hset.
      rewrite (free_vars_rP (vm2:= vm) (vm1:=evm m) (r:=emsf) (emem m));
        last by apply: set_var_disjoint_eq_on haux2 hset.
      move=> _ -> _ _ -> <- -> [->] /=.
      by move/set_varP : hset => -[?? ->];rewrite /get_var /= Vm.setP_eq /sem_sop1 /= hb haux.
    have hws : write_lexprs [:: x] [:: Vword (if ~~ b then wrepr U64 (-1) else w)] (with_vm m vm) = ok m2.
    + by rewrite /= hw2.
    have []:= compile_asm_opn_aux eval_assemble_cond hes _ hws hca hcd hidc hlo.
    + by rewrite /exec_sopn /= hw /sopn_sem /= /x86_CMOVcc /= truncate_word_u; case: ifP.
    by rewrite /eval_op => s' -> ?; exists s'.

  - exact: assemble_slh_move_correct.

  (* SLHprotect *)
Opaque cat.
  rewrite /exec_sopn /= /sopn_sem /= /Ox86SLHprotect_instr /Uptr /assemble_slh_protect /= => ws.
  case: ifP => /= Hws; t_xrbindP.
    (* ws <= U64 *)
  + case: xs => // vw; t_xrbindP => -[] // vmsf; t_xrbindP => // -[] // hes tr w hw wmsf hmsf.
    rewrite /se_protect_small_sem /x86_OR /check_size_8_64 Hws => -[?]? hws ? hmap hlo; subst tr ys ops.
    apply: (assemble_opsP eval_assemble_cond hmap erefl _ hlo).
    by rewrite /= hes /exec_sopn /= hw hmsf /= /sopn_sem /= /x86_OR /check_size_8_64 Hws /= hws.
  (* ws >= U64 *)
  have {Hws} Hws : (U64 < ws)%CMP by rewrite -cmp_nle_lt Hws.
  have Hws' : (U128 <= ws)%CMP by case: (ws) Hws.
  case: xs => // vw; t_xrbindP => -[] // vmsf; t_xrbindP => // -[] // hes tr w hw wmsf hmsf.
  rewrite /se_protect_large_sem Hws /= => -[?]?; subst tr ys.
  case: lvs => // -[] // [aux iaux] [] // y [] // hws.
  case: args hes => // ew [] // emsf [] // hes1.
  t_xrbindP; rewrite negb_or => /andP [] haux1 haux2 hops /dup[] + hmap hlo.
Transparent cat.
  rewrite -hops /=; t_xrbindP => -[op1 oargs1] hass1 z0 z1 _ z2.
  rewrite mapM_cat /=; t_xrbindP => _ _ _ -[op2 oargs2] hass2 _ _ _ _ {z0 z1 z2}.
Opaque cat.
  assert (h := assemble_asm_opI hass1); case: h => hca hcd hidc _ /= {hass1}.
  have [xr [vi /= [??] _]] := check_sopn_args_xmm (n:= 0) hca hidc erefl erefl erefl.
  subst vi aux => {op1 oargs1 hidc hcd hca}.
  set aux := {| v_var := to_var xr; v_info := iaux |}.
  assert (h := assemble_asm_opI hass2); case: h => hca hcd hidc _ /= {hass2}.
  have [yr [vi /= hy _ ]] := check_sopn_dests_xmm (n:= 0) hcd hidc erefl erefl erefl.

  pose v0 := (s.(asm_xreg) xr).
  pose (vm0 := (evm m).[to_var xr <- Vword v0]).
  pose (m0 := with_vm m vm0).
  have hlo0: lom_eqv rip m0 s by apply lom_eqv_set_xreg.

  move: hes1 => /=; t_xrbindP => z hew _ z1 hemsf <- ? [?]; subst z z1.
  have heqvm0 : vm0 =[free_vars_r emsf] evm m.
  + by apply/eq_onS/(set_var_disjoint_eq_on (wdb:=true) (x:= to_var xr) (v:= Vword (s.(asm_xreg) xr))).
  move: hmap; rewrite -hops !mapM_cat; t_xrbindP.
  move=> ops1' hmap1 _ ops2' hmap2 ops3' hmap3 <- <-.
  rewrite foldM_cat.
  (* first instruction *)
  pose v1 := wpinsr (zero_extend U128 (s.(asm_xreg) xr)) wmsf (wrepr U8 0).
  pose (vm1 := ((evm m0).[to_var xr <- Vword v1])).
  pose (m1 := with_vm m vm1).
  (* second instruction *)
  pose v2 := wpbroadcast U128 wmsf.
  pose (vm2 := ((evm m1).[to_var xr <- Vword v2])).
  pose (m2 := with_vm m vm2).

  have /(_ m2) [|s2 -> hlo2] /= :=
    assemble_opsP eval_assemble_cond hmap1 erefl _ hlo0.
  + have -> /=: get_var true vm0 (to_var xr) = ok (Vword (s.(asm_xreg) xr)).
    + by rewrite /get_var /vm0 Vm.setP_eq /=.
    have -> /= : sem_rexpr (emem m) vm0 emsf = ok vmsf.
    + by rewrite -hemsf; apply: free_vars_rP.
    rewrite /exec_sopn /= hmsf /= !truncate_word_le // /=.
    have -> : wand (wrepr U8 0) (x86_nelem_mask U64 U128) = wrepr U8 0.
    + by apply/wunsigned_inj/(wand_modulo _ 1).
    have -> /=: get_var true vm1 (to_var xr) = ok (Vword v1).
    + by rewrite /get_var /vm0 Vm.setP_eq /=.
    have -> /= : sem_rexpr (emem m) vm1 emsf = ok vmsf.
    + rewrite -hemsf; apply: free_vars_rP.
      apply/(eq_onT (vm2:= vm0)) => //.
      by apply/eq_onS/(set_var_disjoint_eq_on (wdb := true) (x:= to_var xr) (v:= Vword v1)).
    rewrite /exec_sopn /= hmsf /= !truncate_word_u /=.
    have -> : wand (wrepr U8 1) (x86_nelem_mask U64 U128) = wrepr U8 1.
    + by apply/wunsigned_inj/(wand_modulo _ 1).
    rewrite /m2 /= /vm2 /v2 /with_vm /=.
    do 5! f_equal.
    rewrite /wpinsr /v2 /wpbroadcast /= /v1 /wpinsr /=.
    by rewrite subword_make_vec_bits_low.
  rewrite foldM_cat => {hmap1 hops}.
  (* third write *)
  pose v3 := wpbroadcast ws wmsf.
  pose (vm3 := ((evm m2).[to_var xr <- Vword v3])).
  pose (m3 := with_vm m2 vm3).
  have : exists2 s3,
      foldM (fun '(op'', asm_args) => [eta eval_op op'' asm_args]) s2 ops2' = ok s3 &
      lom_eqv rip m3 s3.
  + move: hmap2; case: eqP => [? | ]; last first.
    + move=> /= hws1 [?]; subst ops2' => /=.
      eexists; first reflexivity.
      apply: (lom_eqv_ext _ hlo2).
      move=> z; rewrite /vm3.
      case: (to_var xr =P z) => [<- | /eqP ?]; last by rewrite Vm.setP_neq.
      rewrite /m2 /vm2 /= !Vm.setP_eq.
      have ? : ws = U128 by case: (ws) hws1 Hws.
      by subst ws.
    subst ws => hmap2.
    apply: (@assemble_extra_concat128 rip ii [:: LLvar aux] [:: Rexpr (Fvar aux); Rexpr (Fvar aux)]
            m2 [:: Vword v2; Vword v2] [:: Vword (wpbroadcast U256 wmsf)] m3 s2 _ ops2') hmap2 hlo2 => //=.
    + by rewrite /get_var /vm2 Vm.setP_eq.
    rewrite /exec_sopn /= truncate_word_u /=; do 3!f_equal.
    rewrite /v2 /wpbroadcast /=.
    exact: make_vec_4x64.
Transparent cat.
  move=> [s3 -> hlo3] /= {hmap2}.
  (* fourth instruction *)
  move: hws; subst y => /=.
  rewrite /with_vm /=.
  set v4 := wor _ _.
  set vm1' := ((evm m).[ _ <- _]) => -[<-].
  pose (vm4 := (vm3 .[ to_var yr <- Vword v4])).
  have /(_ (with_vm m vm4)) [|s' -> hlo4] /= :=
    assemble_opsP eval_assemble_cond hmap3 erefl _ hlo3.
  + have -> /=: get_var true vm3 (to_var xr) = ok (Vword v3).
    + by rewrite /get_var /vm3 Vm.setP_eq /= wsize_ge_U256.
    have -> /= : sem_rexpr (emem m) vm3 ew = ok vw.
    + rewrite -hew; apply: free_vars_rP.
      apply/eq_onS/(eq_onT (vm2:= vm2)); [ apply/(eq_onT (vm2:= vm1)); [ apply/(eq_onT (vm2:= vm0)) | ] | ].
      + by apply(set_var_disjoint_eq_on (wdb := true) (x:= to_var xr) (v:= Vword v0)).
      + by apply(set_var_disjoint_eq_on (wdb := true) (x:= to_var xr) (v:= Vword v1)).
      + by apply(set_var_disjoint_eq_on (wdb := true) (x:= to_var xr) (v:= Vword v2)).
      apply/(set_var_disjoint_eq_on (wdb := true) (x:= to_var xr) (v:= Vword v3)) => //.
    by rewrite /exec_sopn /= truncate_word_u hw /= /sopn_sem /= /x86_VPOR /x86_u128_binop
         /check_size_128_256 Hws' /= (wsize_ge_U256 ws) /=.
  exists s' => //; apply: lom_eqv_ext hlo4 => z /=.
  rewrite /vm4; case: (to_var yr =P z) => [ | /eqP] ?;first by subst z; rewrite !Vm.setP_eq.
  rewrite Vm.setP_neq // Vm.setP_neq // /vm3 /m2 /vm2 /m1 /vm1 /m0 /vm0 /vm1' /=.
  case: (to_var xr =P z) => [<- | /eqP ?]; first by rewrite !Vm.setP_eq.
  by rewrite !Vm.setP_neq.
Qed.

Definition x86_hagparams : h_asm_gen_params (ap_agp x86_params) :=
  {|
    hagp_eval_assemble_cond := eval_assemble_cond;
    hagp_assemble_extra_op := assemble_extra_op;
  |}.

End ASM_GEN.

(* ------------------------------------------------------------------------ *)
(* Speculative execution. *)

Lemma x86_spec_shp_lower :
  spec_shp_lower (shp_lower x86_shparams).
Proof.
  move=> s s' gd lvs slho es args res lvs' op' es'.
  case: slho => [|||[]||] //= [???] hargs;
     subst lvs' op' es'; rewrite /sem_sopn /exec_sopn /= => ->;
     move: args hargs; destruct_opn_args=> /=.
  - by move=> _ _ [<-] <-.
  - by move=> [->] _ _ [<-] ? -> [<-] <-.
  - by move=> _ _ ? -> [<-] <-.
  all: move=> [v [] ? hv]; subst v; rewrite hv.
  all: move=>  _ ? -> _ [<-] [<-] <- /=.
  1,2,3:
   move/to_wordI: hv => [sz [w] [? /truncate_wordP [hle hze]]]; subst => /=;
   rewrite truncate_word_le ?(cmp_le_trans _ hle) //
      -(zero_extend_idem (s2:= U64)) // -hze zero_extend0 /=.
  all: by rewrite ?wpbroadcast0 worC wor0.
Qed.

Definition x86_hshparams : h_sh_params (ap_shp x86_params) :=
  {|
    hshp_spec_lower := x86_spec_shp_lower;
  |}.


(* ------------------------------------------------------------------------ *)
(* Stack zeroization. *)

Section STACK_ZEROIZATION.

Context {call_conv : calling_convention}.

Lemma x86_hszparams : h_stack_zeroization_params (ap_szp x86_params).
Proof.
  split.
  + exact: x86_stack_zero_cmd_no_ext_lbl.
  exact: x86_stack_zero_cmdP.
Qed.

End STACK_ZEROIZATION.


(* ------------------------------------------------------------------------ *)
(* Shared hypotheses. *)

Definition x86_is_move_opP op vx v :
  ap_is_move_op x86_params op
  -> exec_sopn (Oasm op) [:: vx ] = ok v
  -> List.Forall2 value_uincl v [:: vx ].
Proof.
  case: op => [[[|] [] ws] | []] // _.

  all: rewrite /exec_sopn /=.
  all: t_xrbindP=> w w0 /to_wordI' [ws' [wx [hle ??]]];
         subst vx w0.

  all: rewrite /sopn_sem /=.
  all: match goal with
       | [ |- ?f (zero_extend _ _) = _ -> _ ] => rewrite /f
       end.
  all: t_xrbindP=> *.
  all: t_simpl_rewrites; subst.

  all: constructor; last by constructor.
  all: exact: word_uincl_zero_ext.
Qed.


(* ------------------------------------------------------------------------ *)

Definition x86_h_params {dc : DirectCall} {call_conv : calling_convention} : h_architecture_params x86_params :=
  {|
    hap_hsap        := x86_hsaparams;
    hap_hlip        := x86_hliparams;
    ok_lip_tmp      := x86_ok_lip_tmp;
    ok_lip_tmp2     := x86_ok_lip_tmp2;
    hap_hlop        := x86_hloparams;
    hap_hagp        := x86_hagparams;
    hap_hshp        := x86_hshparams;
    hap_hszp        := x86_hszparams;
    hap_is_move_opP := x86_is_move_opP;
  |}.

End Section.
