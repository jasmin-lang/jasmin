(* Correctness of the ARMv8-A architecture parameters, mirroring
   [arm_params_proof.v].

   Proven so far: the stack-alloc hypotheses ([armv8a_hsaparams]) and the
   complete linearization hypotheses ([armv8a_hliparams], including
   [lloads_correct] for the custom [armv8a_lloads]), together with the
   scratch-register facts and the (trivial) lower-addressing hypotheses.

   All hypotheses are proven; the complete record is [armv8a_h_params]. *)
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
  it_linearization_proof
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
  armv8a_decl
  armv8a_extra
  armv8a_instr_decl
  armv8a
  armv8a_lowering
  armv8a_lowering_proof
  armv8a_params_core
  armv8a_params_core_proof
  armv8a_params_common_proof
  armv8a_stack_zeroization_proof.
Require Export armv8a_params.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

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

Lemma shift_of_scaleP scale shift w :
  shift_of_scale scale = Some shift ->
  wshl w (wunsigned (wrepr U8 (Z.of_nat shift))) = (wrepr Uptr scale * w)%R.
Proof.
  by case: scale => // -[|[|[|[]|]|]|] //= [<-]; rewrite wshl_sem /=.
Qed.

Lemma armv8a_mov_ofsP : mov_ofs_correct armv8a_saparams.(sap_mov_ofs).
Proof.
  move=> P' ev s1 e w ofs pofs x tag mk ii ins s2 P'_globs.
  t_xrbindP=> ve ok_ve ok_w vofs ok_vofs ok_pofs.
  rewrite /sap_mov_ofs /= /armv8a_mov_ofs.
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
        rewrite /armv8a_ADD_semi ?add_wordE.
        move: lea_sem; rewrite wrepr0 GRing.addr0 => ->.
        by rewrite hw /= with_vm_same.
      move=> [<-] hw.
      exists (evm s2) => //.
      rewrite /sem_sopn P'_globs /= /get_gvar /= ok_vb ok_vo /=
        /exec_sopn /= ok_wb ok_wo truncate_word_u /=.
      rewrite (shift_of_scaleP wo hshift).
      rewrite /armv8a_ADD_semi ?add_wordE.
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
        rewrite /armv8a_ADD_semi ?add_wordE.
      move: lea_sem; rewrite GRing.mulr0 GRing.addr0 => ->.
      by rewrite hw /= with_vm_same.
    move=> [<-] hw.
    exists s2.(evm) => //.
    rewrite /sem_sopn P'_globs /= /get_gvar /= ok_vb /=
      /exec_sopn /= ok_wb truncate_word_u /=.
    rewrite /armv8a_ADD_semi ?add_wordE.
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

Lemma armv8a_immediateP : immediate_correct armv8a_saparams.(sap_immediate).
Proof.
  move=> P' ev s ii x z hty.
  rewrite /= /sem_sopn /= /exec_sopn /= truncate_word_u /=.
  by rewrite /write_var set_var_eq_type ?hty.
Qed.

Lemma armv8a_swapP : swap_correct armv8a_saparams.(sap_swap).
Proof.
  move=> P' ev s ii tag x y z w pz pw hxty hyty hzty hwty hz hw.
  rewrite /= /sem_sopn /= /get_gvar /= /get_var /= hz hw /=.
  rewrite /exec_sopn /= !truncate_word_u /= /write_var /set_var /=.
  rewrite (convertible_eval_atype hxty) (convertible_eval_atype hyty) //=.
Qed.

End STACK_ALLOC.

Definition armv8a_hsaparams :
  h_stack_alloc_params (ap_sap armv8a_params) :=
  {|
    mov_ofsP := armv8a_mov_ofsP;
    sap_immediateP := armv8a_immediateP;
    sap_swapP := armv8a_swapP;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization hypotheses. *)

Section LINEARIZATION.

Lemma convertible_rsp : convertible (aword Uptr) (aword armv8a_reg_size).
Proof. by vm_compute. Qed.

Lemma sem_fopns_args_1 s (a : fopn_args) :
  sem_fopns_args s [:: a ] = sem_fopn_args a s.
Proof. by rewrite /sem_fopns_args /=; case: sem_fopn_args. Qed.

Lemma bind_ok_estate (s1 : estate) (f : estate -> exec estate) :
  (Let s2 := ok s1 in f s2) = f s1.
Proof. by []. Qed.

Lemma foldM_1 (T R E : Type) (f : T -> R -> result E R) (acc : R) (a : T) :
  foldM f acc [:: a ] = f a acc.
Proof. by rewrite /=; case: (f a acc). Qed.

Lemma armv8a_spec_lip_allocate_stack_frame :
  allocate_stack_frame_correct armv8a_liparams.
Proof.
  move=> sp_rsp tmp s ts sz htmp hget /=.
  rewrite /armv8a_allocate_stack_frame.
  case: tmp htmp => [tmp [h1 h2]| _].
  + have [? [-> ? /get_varP [-> _ _]]] := [elaborate
      ARMv8AFopnP.smart_subi_tmp_sem_fopn_args
        (xi := vid sp_rsp) sz convertible_rsp h1 h2 (to_word_get_var hget)
    ].
    by eexists.
  rewrite sem_fopns_args_1
    (ARMv8AFopnP.subi_sem_fopn_args (xi := vid sp_rsp) convertible_rsp
       (to_word_get_var hget)).
  eexists; split; first reflexivity.
  + move=> z hz; rewrite Vm.setP_neq //.
    by apply/eqP => heq; apply: hz; rewrite -heq; apply/Sv.add_spec; left.
  by rewrite Vm.setP_eq vm_truncate_val_eq.
Qed.

Lemma armv8a_spec_lip_free_stack_frame :
  free_stack_frame_correct armv8a_liparams.
Proof.
  move=> sp_rsp tmp s ts sz htmp hget /=.
  rewrite /armv8a_free_stack_frame.
  case: tmp htmp => [tmp [h1 h2]| _].
  + have [? [-> ? /get_varP [-> _ _]]] := [elaborate
      ARMv8AFopnP.smart_addi_tmp_sem_fopn_args
        (xi := vid sp_rsp) sz convertible_rsp h1 h2 (to_word_get_var hget)
    ].
    by eexists.
  rewrite sem_fopns_args_1
    (ARMv8AFopnP.addi_sem_fopn_args (xi := vid sp_rsp) convertible_rsp
       (to_word_get_var hget)).
  eexists; split; first reflexivity.
  + move=> z hz; rewrite Vm.setP_neq //.
    by apply/eqP => heq; apply: hz; rewrite -heq; apply/Sv.add_spec; left.
  by rewrite Vm.setP_eq vm_truncate_val_eq.
Qed.

Lemma armv8a_spec_lip_set_up_sp_register :
  set_up_sp_register_correct armv8a_liparams.
Proof.
  Opaque sem_fopn_args.
  move=> vrsp r tmp ts al sz s hget htyrsp htyr htytmp hnetr hner hnert /=.
  rewrite /armv8a_set_up_sp_register sem_fopns_args_cat /=.
  set ts' := align_word _ _.
  have := ARMv8AFopnP.smart_subi_sem_fopn_args
            (xi := tmp) (y := vrsp) (imm := sz) _ _ (to_word_get_var hget).
  move=> [] //.
  + by rewrite htytmp.
  + by right.
  move=> vm1 [] -> heq1 hget1 /=.
  set s1 := with_vm _ _.
  have -> /= := ARMv8AFopnP.align_sem_fopn_args
                 (xi := tmp) (y := tmp) (al := al) (s := s1)
                 _ (to_word_get_var hget1).
  + set s2 := with_vm _ _.
    have hget2 : get_var true (evm s2) vrsp = ok (Vword ts).
    + rewrite get_var_neq; last by [].
      rewrite (get_var_eq_ex _ _ heq1); first by [].
      by apply: Sv_neq_not_in_singleton.
    have -> /= := ARMv8AFopnP.mov_sem_fopn_args (xi := r) _ (to_word_get_var hget2).
    + set s3 := with_vm _ _.
      have hget3 : get_var true (evm s3) tmp = ok (Vword ts').
      + by t_get_var => /=; rewrite htytmp /=.
      have -> /= := ARMv8AFopnP.mov_sem_fopn_args (xi := vrsp) _ (to_word_get_var hget3).
      + set s4 := with_vm _ _.
        Transparent sem_fopn_args.
        eexists; split => //.
        - move=> x; t_notin_add; t_vm_get; rewrite heq1; first by t_vm_get.
          by apply/Sv_neq_not_in_singleton/nesym.
        - by t_get_var => /=; rewrite htyrsp /=.
        - by t_get_var => /=; rewrite (convertible_eval_atype htyr) /=.
        move=> x hx _.
        move: hx => /vflagsP hxtype.
        have [*] : [/\ v_var vrsp <> x, v_var tmp <> x & v_var r <> x].
        - split; apply/eqP/vtype_diff; rewrite hxtype //.
          + by rewrite htyrsp.
          + by rewrite htytmp.
          by apply /eqP => /= h; move: htyr; rewrite h.
        t_vm_get; rewrite heq1 //.
        by apply: Sv_neq_not_in_singleton.
      by rewrite htyrsp.
    by rewrite htyr.
  by rewrite htytmp.
Qed.

Lemma armv8a_lmove_correct : lmove_correct armv8a_liparams.
Proof.
  move=> xd xs ws w s /eqP hws htxd; t_xrbindP => z hget htr; subst.
  rewrite /armv8a_liparams /lip_lmove /armv8a_lmove /= hget /=.
  rewrite /exec_sopn /= htr /= /set_var /=.
  by case: vtype htxd.
Qed.

Lemma armv8a_lstore_correct : lstore_correct_aux armv8a_check_ws armv8a_lstore.
Proof.
  move=> xd xs ofs ws w wp s m /eqP hchk; t_xrbindP; subst ws.
  move=> vd hgetd htrd vs hgets htrs hwr.
  rewrite /armv8a_lstore /= hgets hgetd /= /exec_sopn /= htrs /=.
  rewrite /sem_sop2 /= htrd /= !truncate_word_u /= truncate_word_u /=.
  by rewrite zero_extend_u hwr.
Qed.

Lemma armv8a_smart_addi_correct : ladd_imm_correct_aux ARMv8AFopn_smart_addi.
Proof.
  move=> x1 x2 s w ofs hty hne hget.
  apply: ARMv8AFopnP.smart_addi_sem_fopn_args hget => //; last by right.
  by rewrite hty.
Qed.

Lemma armv8a_lstores_correct : lstores_correct armv8a_liparams.
Proof.
  apply/lstores_imm_dfl_correct.
  + by apply armv8a_lstore_correct.
  apply armv8a_smart_addi_correct.
Qed.

Lemma armv8a_lload_correct :
  lload_correct_aux (lip_check_ws armv8a_liparams) armv8a_lload.
Proof.
  move=> xd xs ofs ws top s w vm hcheck; t_xrbindP => ? hgets hto hread hset.
  move/eqP: hcheck => ?; subst ws.
  rewrite /armv8a_lload /= hgets /= /sem_sop2 /= hto /= !truncate_word_u /=
    truncate_word_u /= hread /=.
  by rewrite /exec_sopn /= truncate_word_u /= zero_extend_u hset.
Qed.

Lemma armv8a_tmp_correct : lip_tmp armv8a_liparams <> lip_tmp2 armv8a_liparams.
Proof. by move=> h; assert (h1 := inj_to_ident h). Qed.

Lemma armv8a_check_ws_correct : lip_check_ws armv8a_liparams Uptr.
Proof. done. Qed.

(* [lloads_correct] for the custom [armv8a_lloads], which restores the
   saved stack pointer through the scratch register X17 and a MOV, since
   an A64 load writes through the X[] accessor for which register number
   31 is ZR, not SP (see armv8a_params.v). *)

Section LLOADS.

Notation vtmp2i := (mk_var_i (to_var R17)).

Let foldM_restore m1 (top' : word Uptr) :=
  foldM (fun '(x, ofs1) (vm : Vm.t) =>
    Let ws := if vtype x is aword ws then ok ws else Error ErrType in
    Let _ := assert (armv8a_check_ws ws) ErrType in
    Let w := read m1 Aligned (top' + wrepr Uptr ofs1)%R ws in
    set_var true vm x (Vword w)).

(* A restore [foldM] only modifies the variables it sets. *)
Lemma lloads_foldM_eq_ex m1 (top' : word Uptr) (l : seq (var * Z)) vm vm' :
  foldM_restore m1 top' vm l = ok vm' ->
  forall z, z \notin map fst l -> vm'.[z] = vm.[z].
Proof.
  rewrite /foldM_restore.
  elim: l vm => /= [ | [x ofs1] l ih] vm.
  + by move=> [<-].
  case heqt: vtype => [|||ws] //=; t_xrbindP => vm1 _ w _ hset /ih hex z.
  rewrite in_cons negb_or => /andP [hzx hzl].
  rewrite (hex _ hzl).
  move/set_varP: hset => [_ _ ->].
  by rewrite Vm.setP_neq // eq_sym.
Qed.

Lemma armv8a_lloads_correct : lloads_correct armv8a_liparams.
Proof.
  move=> rspi to_save ofs s top vm2 /= hnin hnin2 hne hget.
  rewrite foldM_cat /=; t_xrbindP => vm_r hf.
  case heqt: (vtype rspi) => [|||ws] //=; t_xrbindP
    => vm2' wsx hwsx hchk w_sp hread hset heqv.
  subst wsx vm2.
  move/eqP: (hchk) => ?; subst ws.
  move/set_varP: hset => [_ _ ?]; subst vm2'.

  have hsetvar : forall (vm : Vm.t) (w : word Uptr),
      set_var true vm vtmp2i (Vword w) = ok vm.[v_var vtmp2i <- Vword w].
  - by move=> vm w; apply: set_var_eq_type.
  have hconv2 : convertible (vtype (v_var vtmp2i)) (aword reg_size).
  - by vm_compute.

  (* The SP-restoring tail, from any varmap holding [top] in [rspi]. *)
  have hsp : forall vmr,
      get_var true vmr rspi >>= to_word Uptr = ok top ->
      exists2 vm,
        sem_fopns_args (with_vm s vmr)
          (if is_arith_small ofs
           then [:: armv8a_lload Uptr vtmp2i rspi ofs; armv8a_lmove Uptr rspi vtmp2i ]
           else ARMv8AFopn_smart_addi vtmp2i rspi ofs
                ++ [:: armv8a_lload Uptr vtmp2i vtmp2i 0%Z; armv8a_lmove Uptr rspi vtmp2i ])
          = ok (with_vm s vm)
        & vm =[\ Sv.singleton (v_var vtmp2i) ] vmr.[v_var rspi <- Vword w_sp].
  - move=> vmr hget_r.
    case: ifP => _.
    + (* Small offset: LDR from [rspi] directly. *)
      rewrite -cat1s sem_fopns_args_cat !sem_fopns_args_1.
      rewrite (armv8a_lload_correct (xd := vtmp2i) (xs := rspi)
                 (s := with_vm s vmr)
                 armv8a_check_ws_correct hget_r hread (hsetvar _ _)).
      rewrite /= get_var_eq /=; last by [].
      rewrite /exec_sopn /= truncate_word_u /=.
      rewrite set_var_eq_type /=; first last.
      + by rewrite heqt.
      + by [].
      rewrite /armv8a_MOV_semi.
      eexists; first by [].
      move=> z /Sv.singleton_spec hz.
      rewrite !Vm.setP; case: eqP => // _.
      by case: eqP => // heqz; case: (hz (esym heqz)).
    (* Large offset: materialize [rspi + ofs] into the scratch register. *)
    rewrite /sem_fopns_args foldM_cat -!/sem_fopns_args.
    have [vma [hsema heqa hgeta]] :=
      ARMv8AFopnP.smart_addi_sem_fopn_args (xi := vtmp2i) (y := rspi)
        (imm := ofs) (s := with_vm s vmr) hconv2 (or_intror hne) hget_r.
    rewrite hsema bind_ok_estate.
    rewrite -cat1s /sem_fopns_args foldM_cat !foldM_1 -!/sem_fopns_args.
    have hread0 :
      read (emem s) Aligned ((top + wrepr Uptr ofs) + wrepr Uptr 0)%R reg_size
      = ok w_sp.
    + by rewrite wrepr0 GRing.addr0.
    rewrite (armv8a_lload_correct (xd := vtmp2i) (xs := vtmp2i)
               (s := with_vm (with_vm s vmr) vma)
               armv8a_check_ws_correct _ hread0 (hsetvar _ _)); first last.
    + by rewrite hgeta /= truncate_word_u.
    rewrite /= get_var_eq /=; last by [].
    rewrite /exec_sopn /= truncate_word_u /=.
    rewrite set_var_eq_type /=; first last.
    + by rewrite heqt.
    + by [].
    rewrite /armv8a_MOV_semi.
    eexists; first by [].
    move=> z /Sv.singleton_spec hz.
    rewrite !Vm.setP; case: eqP => // _.
    case: eqP => [heqz | _]; first by case: (hz (esym heqz)).
    by rewrite heqa //; apply/Sv.singleton_spec.

  rewrite /lip_lloads /armv8a_lloads.
  rewrite /sem_fopns_args foldM_cat -!/sem_fopns_args.
  case hall: (all (fun '(_, ofs1) => is_arith_small ofs1) to_save).

  (* All offsets small: LDR directly from [rspi]. *)
  - have [hsem1 hget1] := lloads_aux_correct armv8a_lload_correct hnin hget hf.
    rewrite -[X in sem_fopns_args _ X]/(lloads_aux armv8a_lload rspi to_save).
    rewrite hsem1 bind_ok_estate.
    have [vm -> hvm] := hsp _ hget1.
    exists vm => //.
    move=> z hz.
    by rewrite (hvm _ hz).

  (* Rebase through the scratch register. *)
  rewrite -[X in sem_fopns_args _ X]/(
    ARMv8AFopn_smart_addi vtmp2i rspi (head (v_var rspi, 0%Z) to_save).2 ++
    lloads_aux armv8a_lload vtmp2i
      (map (fun '(x1, ofs1) =>
              (x1, (ofs1 - (head (v_var rspi, 0%Z) to_save).2)%Z)) to_save)).
  move: (head _ _).2 => ofs0.
  rewrite /sem_fopns_args foldM_cat -!/sem_fopns_args.
  have [vma [hsema heqa hgeta]] :=
    ARMv8AFopnP.smart_addi_sem_fopn_args (xi := vtmp2i) (y := rspi)
      (imm := ofs0) (s := s) hconv2 (or_intror hne) hget.
  rewrite hsema /=.
  have hnin_reb : forall (x : var),
      ~~ Sv.mem x (sv_of_list fst to_save) ->
      ~~ Sv.mem x (sv_of_list fst
                     (map (fun '(x1, ofs1) => (x1, (ofs1 - ofs0)%Z)) to_save)).
  - move=> x /Sv_memP hx; apply/Sv_memP => /sv_of_listP; rewrite -map_comp.
    move=> /mapP [p hin hx']; apply: hx; apply/sv_of_listP; apply/mapP.
    by exists p => //; rewrite hx'; case: (p).
  have [vm_r' hf' heqx] : exists2 vm_r',
      foldM_restore (emem s) (top + wrepr Uptr ofs0)%R vma
        (map (fun '(x1, ofs1) => (x1, (ofs1 - ofs0)%Z)) to_save) = ok vm_r'
      & vm_r =[\ Sv.singleton (v_var vtmp2i) ] vm_r'.
  - rewrite /foldM_restore.
    move: heqa hf; move: (evm s) (vma) (to_save) => vm_o vma' l heqa hf.
    elim: l vm_o vma' heqa hf => /=.
    + by move=> vm_o vma' heqa [<-]; exists vma' => //; apply: eq_exS.
    move=> [x ofs1] to_save' ih vm_o vma' heqa.
    case heqtx: vtype => [|||wsx] //=; t_xrbindP.
    move=> vm_o1 -> /= w hreadx hsetx hfx.
    rewrite -GRing.addrA -wrepr_add.
    have -> : (ofs0 + (ofs1 - ofs0))%Z = ofs1 by ring.
    rewrite hreadx /= set_var_eq_type //=; last by rewrite heqtx.
    apply: (ih _ _ _ hfx).
    move=> z hz.
    move/set_varP: hsetx => [_ _ ->].
    rewrite !Vm.setP heqtx vm_truncate_val_eq //.
    case: eqP => // _.
    by apply: heqa.
  have hget_r' : get_var true vm_r' rspi >>= to_word Uptr = ok top.
  - have -> : get_var true vm_r' rspi = get_var true (evm s) rspi.
    + rewrite /get_var (lloads_foldM_eq_ex hf'); last first.
      * by have /Sv_memP/sv_of_listP := hnin_reb _ hnin.
      by rewrite heqa //; apply: Sv_neq_not_in_singleton.
    exact: hget.
  have hgeta2 : get_var true vma (v_var vtmp2i) >>= to_word Uptr
                = ok (top + wrepr Uptr ofs0)%R.
  - by rewrite hgeta /= truncate_word_u.
  have hnin2' : ~~ Sv.mem (v_var vtmp2i)
      (sv_of_list fst (map (fun '(x1, ofs1) => (x1, (ofs1 - ofs0)%Z)) to_save)).
  - exact: (hnin_reb _ hnin2).
  have [hsem1 _] := lloads_aux_correct armv8a_lload_correct
                      (rspi := vtmp2i)
                      (to_restore := map (fun '(x1, ofs1) =>
                                            (x1, (ofs1 - ofs0)%Z)) to_save)
                      (s := with_vm s vma) hnin2' hgeta2 hf'.
  rewrite -[X in sem_fopns_args _ X]/(lloads_aux armv8a_lload vtmp2i
      (map (fun '(x1, ofs1) => (x1, (ofs1 - ofs0)%Z)) to_save)).
  rewrite hsem1 bind_ok_estate.
  have [vm -> hvm] := hsp _ hget_r'.
  exists vm => //.
  move=> z hz.
  rewrite (hvm _ hz) !Vm.setP.
  case: eqP => // _.
  by apply: heqx.
Qed.

End LLOADS.

End LINEARIZATION.

Definition armv8a_hliparams :
  h_linearization_params (ap_lip armv8a_params) :=
  {|
    spec_lip_allocate_stack_frame := armv8a_spec_lip_allocate_stack_frame;
    spec_lip_free_stack_frame     := armv8a_spec_lip_free_stack_frame;
    spec_lip_set_up_sp_register   := armv8a_spec_lip_set_up_sp_register;
    spec_lip_lmove                := armv8a_lmove_correct;
    spec_lip_lstore               := armv8a_lstore_correct;
    spec_lip_lload                := armv8a_lload_correct;
    spec_lip_lstores              := armv8a_lstores_correct;
    spec_lip_lloads               := armv8a_lloads_correct;
    spec_lip_tmp                  := armv8a_tmp_correct;
    spec_lip_check_ws             := armv8a_check_ws_correct;
  |}.

Lemma armv8a_ok_lip_tmp :
  exists r : reg_t, of_ident (lip_tmp (ap_lip armv8a_params)) = Some r.
Proof. exists R16; exact: to_identK. Qed.

Lemma armv8a_ok_lip_tmp2 :
  exists r : reg_t, of_ident (lip_tmp2 (ap_lip armv8a_params)) = Some r.
Proof. exists R17; exact: to_identK. Qed.

(* ------------------------------------------------------------------------ *)
(* Lowering hypotheses. *)

Definition armv8a_hloparams : h_lowering_params (ap_lop armv8a_params).
Proof. constructor => *; exact: it_lower_callP. Qed.

(* ------------------------------------------------------------------------ *)
(* Lowering of complex addressing mode for RISC-V.
   It is the identity on armv8a, so the proof is trivial. *)

Lemma armv8a_hlaparams : h_lower_addressing_params (ap_lap armv8a_params).
Proof.
  split=> /=.
  + by move=> _ ? _ [<-].
  + move=> _ ? _ [<-] _ fd ->; by exists fd.
  move=> ???? _ ? _ ?? [<-]; exact: (wiequiv_f_eq (scP := sCP_stack)).
Qed.

(* ------------------------------------------------------------------------ *)
(* Assembly generation hypotheses. *)

Section ASM_GEN.

Notation assemble_extra_correct :=
  (assemble_extra_correct armv8a_agparams) (only parsing).

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
       value_of_bool (arm_eval_cond (get_rf rf) GE_ct) = ok v'
       & value_uincl v v'.
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
       value_of_bool (arm_eval_cond (get_rf rf) c) = ok v'
       & value_uincl v v'.
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
       value_of_bool (arm_eval_cond (get_rf rf) c) = ok v'
       & value_uincl v v'.
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

Lemma armv8a_eval_assemble_cond : assemble_cond_spec armv8a_agparams.
Proof.
  move=> ii m rr rf e c v; rewrite /armv8a_agparams /arm_eval_cond /get_rf /=.
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

Import arch_sem.

Lemma sem_sopns_fopns_args s lc :
  sem_sopns s [seq (None, o, d, e) | '(d, o, e) <- lc] =
  sem_fopns_args s (map to_opn lc).
Proof.
  elim: lc s => //= -[[xs o] es ] lc ih s.
  rewrite /sem_fopn_args /sem_sopn_t /=; case: sem_rexprs => //= >.
  by rewrite /exec_sopn /= /sopn_sem /Oarmv8a; case: i_valid => //=;
    case : app_sopn => //= >; case write_lexprs.
Qed.

Lemma assemble_swap_correct ws : assemble_extra_correct (Oarmv8a_swap ws).
Proof.
  move=> rip ii lvs args m xs ys m' s ops ops' /=.
  case: eqP => // -> {ws}.
  case: lvs => // -[] // x [] // -[] // y [] //.
  case: args => // -[] // [] // z [] // [] // [] // w [] //=.
  t_xrbindP => vz hz _ vw hw <- <-.
  rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /= /swap_semi.
  t_xrbindP => /= _ wz hvz ww hvw <- <- /=.
  t_xrbindP => _ vm1 /set_varP [_ htrx ->] <- _ vm2 /set_varP [_ htry ->] <- <-
    /eqP hxw /eqP hyx /and4P [hxt hyt hzt hwt] <-.
  move=> hmap hlom.
  have h := (assemble_opsP armv8a_eval_assemble_cond hmap erefl _ hlom).
  set m1 := (with_vm m (((evm m).[x <- Vword (wxor wz ww)])
               .[y <- Vword (wxor (wxor wz ww) ww)])
               .[x <- Vword (wxor (wxor wz ww) (wxor (wxor wz ww) ww))]).
  case: (h m1) => {h}.
  + rewrite /= hz /= hw /= /exec_sopn /= hvz hvw /=.
    rewrite set_var_truncate //= !get_var_eq //= (convertible_eval_atype hxt) /=.
    rewrite get_var_neq // hw /= truncate_word_u /= hvw /=.
    rewrite set_var_truncate //= !get_var_eq //= (convertible_eval_atype hyt) /=.
    rewrite get_var_neq // get_var_eq //= (convertible_eval_atype hxt) /=
      !truncate_word_u /=.
    rewrite set_var_truncate //= !with_vm_idem.
  move=> s' hfold hlom'; exists s' => //; apply: lom_eqv_ext hlom'.
  move=> i /=; rewrite !Vm.setP; case: eqP => [<- | ?].
  + by move/eqP/negbTE: hyx => -> /=; rewrite (convertible_eval_atype hxt) /=
      wxorA wxor_xx wxor0.
  by case: eqP => // _; rewrite -wxorA wxor_xx wxorC wxor0.
Qed.

Lemma assemble_add_large_imm_correct :
  assemble_extra_correct Oarmv8a_add_large_imm.
Proof.
  move=> rip ii lvs args m xs ys m' s ops ops' /=.
  case: lvs => // -[] // [[xt xn] xii] [] //.
  set xi := {| v_var := _ |}.
  case: args => // -[] // [] // y [] // [] // [] // [] // w [] // imm [] //=.
  t_xrbindP => vy hvy <-.
  rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /=; t_xrbindP
    => /= n w1 hw1 w2 hw2 ? <- /=; subst n.
  t_xrbindP => ? vm1 hsetx <- <- /= /eqP hne.
  move=> /andP [] hxtty /andP [] hyty _ <- hmap hlom.
  move/to_wordI: hw1 => [ws [w' [?]]] /truncate_wordP [hle1 ?]; subst vy w1.
  move/get_varP: (hvy) => [_ _ /compat_valE] /=;
    rewrite (convertible_eval_atype hyty) => -[_ [] <- hle2].
  have ? := cmp_le_antisym hle1 hle2; subst ws => {hle1 hle2}.
  have := ARMv8AFopnP.smart_addi_sem_fopn_args (xi := xi) (y := y) (imm := imm)
            hxtty (or_intror _ hne) (to_word_get_var hvy).
  move=> [vm []]; rewrite -sem_sopns_fopns_args => hsem heqex /get_varP [hvmx _ _].
  have [] := (assemble_opsP armv8a_eval_assemble_cond hmap _ hsem hlom).
  + by rewrite all_map; apply/allT => -[[]].
  move=> s' -> hlo; exists s' => //.
  apply: lom_eqv_ext hlo => z /=.
  move/get_varP: hvy => -[hvmy _ _].
  move: hsetx; rewrite set_var_eq_type //;
    last by rewrite (convertible_eval_atype hxtty).
  move=> -[<-].
  rewrite Vm.setP.
  case: eqP => heqx.
  + rewrite (convertible_eval_atype hxtty) -heqx -hvmx zero_extend_u /=.
    move: hw2 => /truncate_wordP [? ].
    by rewrite zero_extend_wrepr // => ->.
  by apply heqex; move=> /=; clear -heqx; SvD.fsetdec.
Qed.

Lemma uncons_LLvarP ii les x les' :
  uncons_LLvar ii les = ok (x, les') ->
  les = LLvar x :: les'.
Proof. by case: les => [// | [// | ?] ?] [-> ->]. Qed.

Lemma uncons_wconstP ii les imm les' :
  uncons_wconst ii les = ok (imm, les') ->
  exists ws, les = rconst ws imm :: les'.
Proof.
  case: les => [// | [//|]] [] // [] // ? [] // ?? [-> ->]. by eexists.
Qed.

Lemma smart_li_argsP ii ws les res x imm res' :
  smart_li_args ii ws les res = ok (x, imm, res') ->
  [/\ (ws == U64) || (ws == U32)
    , les = [:: LLvar x ]
    , convertible (vtype (v_var x)) (aword reg_size)
    & exists ws', res = rconst ws' imm :: res'
  ].
Proof.
  rewrite /smart_li_args.
  t_xrbindP=> -> -[??] /uncons_LLvarP ->.
  t_xrbindP=> ? /nilP -> [??] /uncons_wconstP [? ->].
  t_xrbindP=> ???; subst.
  split=> //=.
  by eexists.
Qed.

Lemma assemble_smart_li_correct ws : assemble_extra_correct (Oarmv8a_smart_li ws).
Proof.
  move=> rip ii lvs args m xs ys m' s ops ops'.
  move=> hsemargs hexec hwrite.
  rewrite /= /assemble_smart_li.
  t_xrbindP=> -[[x imm] ?] /smart_li_argsP [hws ? hty [ws' ?]] [?] hops heq;
    subst lvs args ops.
  case/orP: hws => /eqP ?; subst ws.
  (* U64 *)
  - have [vm []] := ARMv8AFopn_coreP.li_lsem_1 m imm hty.
    move=> hsem hvm hgetx.
    have [] :=
      assemble_opsP (m' := with_vm m vm) armv8a_eval_assemble_cond hops _ _ heq.
    - by rewrite all_map; apply/allT => -[[]].
    - move: hsem.
      by rewrite ARMv8AFopnP.sem_fopns_equiv -sem_sopns_fopns_args /= => ->.
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
    rewrite set_var_eq_type //; last by rewrite (convertible_eval_atype hty).
    move=> [<-].
    rewrite Vm.setP.
    case: eqP => [? | hne].
    - subst y.
      by rewrite (convertible_eval_atype hty) /= zero_extend_wrepr.
    rewrite hvm //.
    by apply/Sv.singleton_spec/nesym.
  (* U32: a W write stores the 32-bit value in the register-typed variable
     (allowed by the [withsubword] discipline); the assembly level clears
     the upper bits, which [value_uincl] absorbs. *)
  have [vm []] := ARMv8AFopn_coreP.li_lsem_1_w32 m imm hty.
  move=> hsem hvm hgetx.
  have [] :=
    assemble_opsP (m' := with_vm m vm) armv8a_eval_assemble_cond hops _ _ heq.
  - by rewrite all_map; apply/allT => -[[]].
  - move: hsem.
    by rewrite ARMv8AFopnP.sem_fopns_equiv -sem_sopns_fopns_args /= => ->.
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
  move/set_varP: hsetx => [_ _ ->].
  rewrite Vm.setP.
  case: eqP => [? | hne].
  - subst y.
    by rewrite (convertible_eval_atype hty) /= zero_extend_wrepr.
  rewrite hvm //.
  by apply/Sv.singleton_spec/nesym.
Qed.

Lemma armv8a_assemble_extra_op op : assemble_extra_correct op.
Proof.
  case: op.
  + exact: assemble_swap_correct.
  + exact: assemble_add_large_imm_correct.
  exact: assemble_smart_li_correct.
Qed.

Lemma armv8a_assemble_extra_sz ii op lvs args ops :
   to_asm ii op lvs args = ok ops -> ssrnat.leq 1 (size ops).
Proof.
  rewrite /to_asm /= /assemble_extra /=.
  case: op.
  + move=> w; case: eqP => // _.
    case: lvs => // -[] // ? [] // -[] // ? [] //.
    case: args => // -[] // [] // ? [] // [] // [] // ? [] //.
    by t_xrbindP => _ _ _ <-.
  + case: lvs => // -[] // ? [] //.
    case: args => // -[] // [] // ? [] // [] // [] // [] // ? [] // ? [] //.
    t_xrbindP => /negPf hne _ <-.
    rewrite /asm_args_of_opn_args /= /ARMv8AFopn_core.smart_addi /=.
    rewrite /ARMv8AFopn_core.gen_smart_opi /ARMv8AFopn_core.smart_mov.
    case: ifP => //.
    + by rewrite hne.
    case: ifP => //.
    by rewrite size_map size_rcons.
  move=> w. rewrite /assemble_smart_li /= /smart_li_args.
  t_xrbindP => ?? -[] ???.
  t_xrbindP => ?? -[] ??? [<-] [<-].
  rewrite /asm_args_of_opn_args /= /ARMv8AFopn_core.li.
  case: ifP => //; case: ifP => //.
Qed.

Definition armv8a_hagparams : h_asm_gen_params (ap_agp armv8a_params) :=
  {|
    hagp_eval_assemble_cond := armv8a_eval_assemble_cond;
    hagp_assemble_extra_op := armv8a_assemble_extra_op;
    hagp_assemble_extra_sz := armv8a_assemble_extra_sz;
  |}.

End ASM_GEN.

(* ------------------------------------------------------------------------ *)
(* Speculative execution. *)

Lemma armv8a_hshp : slh_lowering_proof.h_sh_params (ap_shp armv8a_params).
Proof. by constructor; move=> ???? []. Qed.

(* ------------------------------------------------------------------------ *)
(* Stack zeroization. *)

Section STACK_ZEROIZATION.

Lemma armv8a_hszparams : h_stack_zeroization_params (ap_szp armv8a_params).
Proof.
  split.
  + exact: armv8a_stack_zero_cmd_not_ext_lbl.
  exact: armv8a_stack_zero_cmdP.
Qed.

End STACK_ZEROIZATION.

(* ------------------------------------------------------------------------ *)
(* Shared hypotheses. *)

Definition armv8a_is_move_opP op vx v :
  ap_is_move_op armv8a_params op
  -> exec_sopn (Oasm op) [:: vx ] = ok v
  -> values_uincl v [:: vx ].
Proof.
  case: op => // -[[] // [mn opt]] /=.
  case: ifP => // hmn /negPf hs.
  case: opt hmn hs => sho sz hmn /= hs.
  case: sho hs => [sk | ] hs; first by [].
  rewrite /exec_sopn /sopn_sem /sopn_sem_ /=.
  rewrite /semi_to_atype.
  move: (computational_eq _) (computational_eq _) => e1 e2.
  rewrite <- e1, <- e2.
  clear e1 e2.
  (* To avoid duplication, we prove that [mn] returns [to_word ws vx] for
     some [ws]. *)
  have ->:
    Let semi := assert (id_valid (mn_desc {| has_shift := None; opts_size := sz |} mn)) ErrType >>
                ok (id_semi (mn_desc {| has_shift := None; opts_size := sz |} mn)) in
    (Let t := app_sopn (map eval_ltype (id_tin (mn_desc {| has_shift := None; opts_size := sz |} mn))) semi [:: vx] in
    ok (list_ltuple t)) =
      Let _ := assert (id_valid (mn_desc {| has_shift := None; opts_size := sz |} mn)) ErrType in
      Let ws := if head lbool (id_tout (mn_desc {| has_shift := None; opts_size := sz |} mn)) is lword ws
                then ok ws else type_error in
      Let wx := to_word ws vx in
      ok [:: Vword wx].
  + by case: mn hmn => //= _;
      case: sz => //=;
      case: to_word => //= ?;
      rewrite /armv8a_MOV_semi ?zero_extend_u.
  t_xrbindP=> _ ws0 _ w0 hw0 hv.
  move/to_wordI: hw0 => [ws [w [? htr]]]; subst vx.
  rewrite -hv.
  constructor=> //=.
  by apply (truncate_word_uincl htr).
Qed.

(* ------------------------------------------------------------------------ *)

Definition armv8a_h_params : h_architecture_params armv8a_params :=
  {|
    hap_hsap        := armv8a_hsaparams;
    hap_hlip        := armv8a_hliparams;
    ok_lip_tmp      := armv8a_ok_lip_tmp;
    ok_lip_tmp2     := armv8a_ok_lip_tmp2;
    hap_hlop        := armv8a_hloparams;
    hap_hlap        := armv8a_hlaparams;
    hap_hagp        := armv8a_hagparams;
    hap_hshp        := armv8a_hshp;
    hap_hszp        := armv8a_hszparams;
    hap_is_move_opP := armv8a_is_move_opP;
  |}.

End Section.
