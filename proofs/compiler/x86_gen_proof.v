From mathcomp
Require Import all_ssreflect all_algebra.
Require Import psem compiler_util asm_gen_proof.
Require Import arch_extra linear_sem.
Require Import x86_instr_decl x86_extra x86_gen.

Import Utf8.
Import Relation_Operators.
Import linear linear_sem label x86_decl x86_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma assemble_progP p p' :
  assemble_prog p = ok p' →
  let rip := mk_ptr (lp_rip p) in
  let rsp := mk_ptr (lp_rsp p) in
  [/\ disj_rip rip
    , asm_globs p' = lp_globs p
    & map_cfprog_linear (assemble_fd assemble_cond rip rsp) p.(lp_funcs)
      = ok (asm_funcs p')
  ].
Proof.
  rewrite /assemble_prog.
  t_xrbindP => _ /assertP /eqP ok_rip _ /assertP /eqP _ fds ok_fds <-{p'}.
  split => //.
  split => r heq //.
  move: ok_rip.
  by rewrite -heq /to_reg to_varK.
Qed.

Lemma assemble_prog_RSP p p' :
  assemble_prog p = ok p' -> to_string RSP = lp_rsp p.
Proof.
  rewrite /assemble_prog.
  t_xrbindP => _ _ _ /assertP /eqP ok_rsp.
  move=> _ _ _.
  exact: of_stringI ok_rsp.
Qed.

Section PROG.

Context (p: lprog) (p': asm_prog) (ok_p': assemble_prog p = ok p').

Lemma not_condtP (c:condt) rf b :
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

Lemma eval_assemble_cond ii m rf e c v:
  eqflags m rf
  -> assemble_cond ii e = ok c
  -> sem_pexpr [::] m e = ok v
  -> let get x := if rf x is Def b
                  then ok b
                  else undef_error in
     exists2 v', value_of_bool (eval_cond get c) = ok v' & value_uincl v v'.
Proof.
  move=> eqv; elim: e c v => //.
  + move=> x c v /=; t_xrbindP=> r ok_r ok_ct ok_v.
    have := gxgetflag_ex eqv ok_r ok_v.
    case: {ok_r ok_v} r ok_ct => // -[<-] {c} /= h;
      eexists;
      eauto;
      by case: (rf _).
  + case => //= e hrec; t_xrbindP => c v ce hce <- ve hve.
    rewrite /sem_sop1 /=; t_xrbindP => b hb <-.
    have /(value_of_bool_uincl hb) -/not_condtP /= -> := hrec _ _ hce hve.
    by exists (~~b).
  + case => //=.
    + move=> e1 _ e2 _ c v.
      case: e1 => //= x1; case: e2 => //= x2; t_xrbindP => f1 ok_f1 f2 ok_f2.
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
  + case: e2 => //= -[] // [] //= vn2; t_xrbindP => f1 hf1 f2 hf2 fn2 hfn2.
    case: ifP => // /orP hor [<-] b1 vv1 /(gxgetflag eqv hf1) hvb1/hvb1{hvb1}hvb1.
    move=> vv2 vv2' /(gxgetflag eqv hf2) hvb2 ht2.
    move=> ?? vvn2 /(gxgetflag eqv hfn2) hvnb2 /sem_sop1I /= [nb2 /hvnb2{hvnb2}hvnb2 ->].
    move=> /truncate_val_bool [??] ?; subst.
    move: ht2; rewrite /truncate_val /=; t_xrbindP => b2 /hvb2{hvb2}hvb2 ?; subst.
    exists (if b1 then Vbool b2 else ~~ nb2); last done.
    by case: hor => /and3P [/eqP ? /eqP ? /eqP ?]; subst; move: hvnb2; rewrite hvb1 hvb2 => -[<-] /=;
      case: (b1); case: (b2).
  case: e2' => //= v2; case: e2 => // vn2; t_xrbindP => f1 hf1 f2 hf2 fn2 hfn2.
  case: ifP => // /orP hor [<-] b1 vv1 /(gxgetflag eqv hf1) hvb1/hvb1{hvb1}hvb1.
  move=> ? vv2 vv2' /(gxgetflag eqv hf2) hvb2 /sem_sop1I /= [b2 /hvb2{hvb2}hvb2 ->].
  move=> /truncate_val_bool [??] ?; subst.
  move=> vvn2 /(gxgetflag eqv hfn2) hvnb2.
  rewrite /truncate_val /=; t_xrbindP => nb2 /hvnb2{hvnb2}hvnb2 ??; subst.
  exists (if b1 then Vbool (~~b2) else nb2); last done.
  by case: hor => /and3P [/eqP ? /eqP ? /eqP ?]; subst; move: hvnb2; rewrite hvb1 hvb2 => -[<-] /=;
      case: (b1); case: (b2).
Qed.

Lemma assemble_extra_op rip ii op lvs args op' lvs' args' op'' asm_args m m' s :
  sem_sopn [::] (Oasm (ExtOp op)) m lvs args = ok m' ->
  to_asm ii op lvs args = ok (op', lvs', args') ->
  assemble_asm_op assemble_cond rip ii op' lvs' args' = ok (op'', asm_args) ->
  lom_eqv rip m s ->
  exists2 s', eval_op op'' asm_args s = ok s' & lom_eqv rip m' s'.
Proof.
  case: op.
  + move=> sz; rewrite /sem_sopn /exec_sopn /sopn_sem /=.
    rewrite /Oset0_instr; case: ifP => /= hsz64.
    + t_xrbindP => ? []// ?? [<-] /= <-.
      move=> hw x hx <- <- <-; rewrite /assemble_asm_op.
      t_xrbindP => asm_args' _ _ /assertP hc.
      case hci: enforce_imm_i_args_kinds =>
        {asm_args} [asm_args|//] _ [<-] _ /assertP /andP [hca hcd] <- <-.
      have {hci} hidc := filter_i_args_kinds_no_imm_correct (enforce_imm_i_args_kinds_correct hci).
      move: hca; rewrite /check_sopn_args /= => /and3P [].
      rewrite /check_sopn_arg /=.
      case: asm_args hidc hcd => //= a0 [ // | ] a1 [] //= hidc hcd;
       last by rewrite /check_args_kinds /= !andbF.
      case ok_y: xreg_of_var => [y|//]; move /xreg_of_varI in ok_y.
      rewrite !andbT /compat_imm.
      case: y ok_y => // r xr; rewrite !orbF => /eqP ? /eqP ? _; subst a0 a1; last by [].
      rewrite /eval_op /exec_instr_op /= /eval_instr_op /=.
      rewrite /truncate_word /x86_XOR /check_size_8_64 hsz64 /= wxor_xx.
      set id := instr_desc_op (XOR sz) => hlo.
      rewrite /SF_of_word msb0.
      by apply: (@compile_lvals _ _ _ _ _ _ _ _
             rip ii m lvs m' s [:: Reg r; Reg r]
             id.(id_out) id.(id_tout)
             (let vf := Some false in let: vt := Some true in (::vf, vf, vf, vt, vt & (0%R: word sz)))
             (reg_msb_flag sz) (refl_equal _) hw hlo hcd id.(id_check_dest)).
    t_xrbindP => ? []// ?? [<-] /= <-.
    move=> hw x hx <- <- <-; rewrite /assemble_asm_op.
    t_xrbindP => asm_args' _ _ /assertP hc.
    case hci: enforce_imm_i_args_kinds =>
      {asm_args} [asm_args|//] _ [<-] _ /assertP /andP [hca hcd] <- <-.
    have {hci} hidc := filter_i_args_kinds_no_imm_correct (enforce_imm_i_args_kinds_correct hci).
    move: hca; rewrite /check_sopn_args /= => /and3P [].
    rewrite /check_sopn_arg /=.
    case: asm_args hidc hcd => //= a0 [// | ] a1 [] //= a2 [] //=;
      last by rewrite /check_args_kinds /= !andbF.
    rewrite orbF => hidc hcd.
    case ok_y: xreg_of_var => [y|//]; move /xreg_of_varI in ok_y.
    rewrite !andbT /compat_imm.
    case: y ok_y => // r xr; rewrite !orbF => /eqP ? /eqP ? _; subst a1 a2.
    + by move: hidc; rewrite /check_args_kinds /= andbF.
    rewrite /eval_op /exec_instr_op /= /eval_instr_op /=.
    rewrite /truncate_word /x86_VPXOR hidc /= /x86_u128_binop /check_size_128_256 wsize_ge_U256.
    have -> /= : (U128 ≤ sz)%CMP by case: (sz) hsz64.
    rewrite wxor_xx; set id := instr_desc_op (VPXOR sz) => hlo.
    by apply: (@compile_lvals _ _ _ _ _ _ _ _
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

    t_xrbindP => asm_args' haux _ /assertP hc'.
    case hci: enforce_imm_i_args_kinds =>
      {asm_args} [asm_args|//] _ [<-] _ /assertP /andP [hca hcd] <- <- hlow.
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
    case: a' hc => //= [ r | xmm].
    + rewrite /compat_imm; case:a => //= r' /orP [/eqP [?]|//] hr; subst r'.
      have heq := of_varI hr.
      move: hvl.
      rewrite /get_gvar /= -heq => hvl.
      case: hlow => _ _ _ /(_ _ _ hvl) hu _ _.
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
  t_xrbindP => asm_args' _ _ /assertP hc.
  case hci: enforce_imm_i_args_kinds =>
    {asm_args} [asm_args|//] _ [<-] _ /assertP /andP [hca hcd] <- <- hlo.
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
  case: hlo => h1 hrip hd h2 h3 h4.
  move: hwx; rewrite /write_var /set_var.
  rewrite -xr => -[<-]{m'}.
  constructor => //=.
  + by rewrite /get_var Fv.setP_neq //; apply /eqP;case: hd.
  + move=> r' v''; rewrite /get_var /on_vu /= /RegMap.set ffunE.
    case: eqP => [-> | hne].
    + by rewrite Fv.setP_eq /reg_msb_flag /= word_extend_CLEAR zero_extend_u => -[<-].
    rewrite Fv.setP_neq; last by apply /eqP => h; apply hne; apply inj_to_var.
    by apply h2.
  + move=> r' v''; rewrite /get_var /on_vu /=.
    by rewrite Fv.setP_neq //; apply h3.
  move=> f v''; rewrite /get_var /on_vu /=.
  by rewrite Fv.setP_neq //; apply h4.
Qed.

(*
Lemma assemble_fdP wrip m1 fn va m2 vr :
  lsem_fd p wrip m1 fn va m2 vr →
  ∃ fd va',
    get_fundef p.(lp_funcs) fn = Some fd ∧
    mapM2 ErrType truncate_val (lfd_tyin fd) va = ok va' ∧
  ∃ fd', get_fundef p'.(xp_funcs) fn = Some fd' ∧
    ∀ st1,
      List.Forall2 value_uincl va' (get_arg_values st1 fd'.(xfd_arg)) →
      st1.(xmem) = m1 →
      ∃ st2,
        x86sem_fd p' wrip fn st1 st2 ∧
        List.Forall2 value_uincl vr (get_arg_values st2 fd'.(xfd_res)) ∧
        st2.(xmem) = m2.
Proof.
case => m1' fd va' vm2 m2' s1 s2 vr' ok_fd ok_m1' /= [<-] {s1} ok_va'.
rewrite /with_vm /=.
set vm1 := (vm in {| evm := vm |}).
move => ok_s2 hexec ok_vr' ok_vr -> {m2}.
exists fd, va'. split; first exact: ok_fd. split; first exact: ok_va'.
have [ hrip _ ok_sp ok_fds ] := assemble_progP ok_p'.
have [fd' [h ok_fd']] := get_map_cfprog_gen ok_fds ok_fd.
exists fd'; split => //.
move => s1 hargs ?; subst m1.
move: h; rewrite /assemble_fd; t_xrbindP => body ok_body.
t_xrbindP => args ok_args dsts ok_dsts _ /assertP hsp tosave ? savedstk ? [?]; subst fd'.
set xr1 := mem_write_reg RSP (top_stack m1') {| xmem := m1' ; xreg := s1.(xreg) ; xrip := wrip; xxreg := s1.(xxreg) ; xrf := rflagmap0 |}.
have eqm1 : lom_eqv rip {| emem := m1' ; evm := vm1 |} xr1.
+ constructor => //.
  - by rewrite /get_var /= /vm1 /= Fv.setP_eq.
  - rewrite /vm1 /= => r v.
    rewrite (inj_reg_of_string ok_sp (reg_of_stringK RSP)).
    rewrite /get_var /var_of_register /RegMap.set ffunE; case: eqP.
    * move => -> {r} /=.
      rewrite Fv.setP_neq; last first.
      + by apply /eqP => -[] heq; case: hrip => /(_ RSP); rewrite /var_of_register /= -heq.
      rewrite Fv.setP_eq word_extend_reg_id // zero_extend_u => -[<-];
      exact: word_uincl_refl.
    move => ne; rewrite /= Fv.setP_neq; last first.
    + by apply /eqP => -[] heq; case: hrip => /(_ r); rewrite /var_of_register -heq.
    rewrite Fv.setP_neq /vmap0 ?Fv.get0 //.
    by apply/eqP => -[] /(@inj_string_of_register RSP) ?; apply: ne.
  - by move => r v; rewrite /vm1 /= /get_var !Fv.setP_neq // /vmap0 Fv.get0.
  move => f v /=; rewrite /vm1 /rflagmap0 ffunE /=.
  by rewrite /var_of_flag /get_var /= !Fv.setP_neq // /vmap0 Fv.get0.
have h1 : get_arg_values xr1 args = get_arg_values s1 args.
+ rewrite /get_arg_values /get_arg_value /xr1 /=.
  apply: map_ext => // r /xseq.InP hr; f_equal.
  case: r hr => // r hr.
  rewrite ffunE; case: eqP => // e.
  by elim: (elimN idP hsp); rewrite -e.
rewrite -h1 in hargs => {h1}.
have eqm2 : lom_eqv rip s2 xr1.
+ by apply: write_vars_uincl; eauto.
have ms : match_state rip (of_estate s2 fn fd.(lfd_body) 0) {| xm := xr1 ; xfn := fn ; xc := body ; xip := 0 |}.
+ by constructor => //=; rewrite to_estate_of_estate.
have [[[om or orip oxr orf] ofn oc opc] [xexec]] := match_state_sem hexec ms.
rewrite (size_mapM ok_body).
case => eqm' /= ?.
rewrite ok_body => -[?] ?; subst ofn oc opc.
eexists; split; first by econstructor; eauto.
case: eqm' => /= ?; subst om => eqr' _; split => //.
rewrite /get_arg_values /get_arg_value /=.
apply: (Forall2_trans value_uincl_trans).
+ apply: (mapM2_Forall2 _ ok_vr) => a b r _; exact: truncate_val_uincl.
apply: get_xreg_of_vars_uincl; eassumption.
Qed.
*)

End PROG.
