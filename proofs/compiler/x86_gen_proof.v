From mathcomp
Require Import all_ssreflect all_algebra.
Require Import psem compiler_util asm_gen_proof.
Require Import arch_extra linear_sem.
Require Import x86_instr_decl x86_extra x86_gen x86_linear_sem.

Import Utf8.
Import Relation_Operators.
Import linear linear_sem label x86_decl x86_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma assemble_fdI sp rip fd fd' :
  assemble_fd sp rip fd = ok fd' →
  [/\
    to_var sp \notin [seq v_var x | x <- lfd_arg fd]
  ,  all (λ x, if asm_typed_reg_of_var x is Ok (ARReg _) then true else false) (lfd_callee_saved fd)
  & ∃ c arg res,
    [/\ assemble_c rip fd.(lfd_body) = ok c
    , mapM (λ x : var_i, asm_typed_reg_of_var x) (lfd_arg fd) = ok arg
    , mapM (λ x : var_i, asm_typed_reg_of_var x) (lfd_res fd) = ok res
    & fd' = {| asm_fd_align := lfd_align fd ; asm_fd_arg := arg ; asm_fd_body := c ; asm_fd_res := res ; asm_fd_export := lfd_export fd ; asm_fd_total_stack := lfd_total_stack fd |}
    ]
  ].
Proof.
  rewrite /assemble_fd; t_xrbindP => c ok_c _ /assertP ok_sp _ /assertP ok_callee_saved arg ok_arg res ok_res <-; split.
  - exact: ok_sp.
  - exact: ok_callee_saved.
  by exists c, arg, res.
Qed.

Lemma assemble_progP p p' :
  assemble_prog p = ok p' →
  let rip := mk_rip p.(lp_rip) in
  [/\ disj_rip rip,
   to_var RSP = Var (sword Uptr) p.(lp_rsp),
   asm_globs p' = lp_globs p &
   map_cfprog_linear (assemble_fd RSP rip) p.(lp_funcs) = ok (asm_funcs p') ].
Proof.
  rewrite /assemble_prog.
  t_xrbindP => u /assertP /eqP ok_rip u' /assertP /eqP ok_rsp fds ok_fds <-{p'}.
  split => //; last by rewrite -(of_stringI ok_rsp).
  split => r heq //.
  by move: ok_rip; rewrite -heq /to_reg to_varK.
  move: ok_rip; rewrite /= /to_reg -heq. admit. 
Admitted.


(* Assembling preserves labels *)

Lemma assemble_c_labels rip a b :
  assemble_c rip a = ok b →
  label_in_lcmd a = label_in_asm b.
Proof.
  move => /mapM_Forall2; elim => // { a b }.
  move => x y a b ok_y _ ih.
  rewrite /label_in_lcmd -cat1s pmap_cat.
  rewrite /label_in_asm -(cat1s y) pmap_cat.
  congr (_ ++ _); last exact: ih.
  by case: x ok_y { ih } => ii [] /=; t_xrbindP => *; subst.
Qed.

Lemma assemble_fd_labels rsp rip (fn: funname) fd fd' :
  assemble_fd rsp rip fd = ok fd' →
  [seq (fn, lbl) | lbl <- label_in_lcmd (lfd_body fd)] = [seq (fn, lbl) | lbl <- label_in_asm (asm_fd_body fd')].
Proof.
  case/assemble_fdI => _ _ [] c [] _ [] _ [] ok_c _ _ -> /=.
  by rewrite (assemble_c_labels ok_c).
Qed.

Lemma assemble_prog_labels p p' :
  assemble_prog p = ok p' →
  label_in_lprog p = label_in_asm_prog p'.
Proof.
  case/assemble_progP => _ _ _ /mapM_Forall2.
  rewrite /label_in_lprog /label_in_asm_prog.
  elim => //; t_xrbindP => - [] fn lfd fn' lfds xfds xfd /= ok_xfd <- {fn'} _ ih.
  congr (_ ++ _); last exact: ih.
  exact: assemble_fd_labels ok_xfd.
Qed.

Variant match_state rip (ls: lstate) (lc : lcmd) (xs: x86_state) : Prop :=
| MS
  `(lom_eqv rip (to_estate ls) (asm_m xs))
  `(lfn ls = asm_f xs)
  `(assemble_c rip lc = ok (asm_c xs))
  `(lpc ls = asm_ip xs)
.

Lemma assemble_i_is_label rip a b lbl :
  assemble_i rip a = ok b →
  linear.is_label lbl a = arch_sem.is_label lbl b.
Proof.
by (rewrite /assemble_i /linear.is_label ; case a =>  ii []; t_xrbindP) => /=
  [????? <- | <- | ? <- | ? <- | _ _ _ ? _ <- | _ ?? _ <- | ???? <-].
Qed.

Lemma assemble_c_find_is_label rip c i lbl:
  assemble_c rip c = ok i →
  find (linear.is_label lbl) c = find (arch_sem.is_label lbl) i.
Proof.
rewrite /assemble_c.
elim: c i.
- by move => i [<-].
move => a c ih i' /=; t_xrbindP => b ok_b i ok_i <- {i'} /=.
by rewrite (ih i ok_i) (assemble_i_is_label lbl ok_b).
Qed.

Lemma assemble_c_find_label rip c i lbl:
  assemble_c rip c = ok i →
  linear.find_label lbl c = arch_sem.find_label lbl i.
Proof.
rewrite /assemble_c /linear.find_label /arch_sem.find_label => ok_i.
by rewrite (size_mapM ok_i) (assemble_c_find_is_label lbl ok_i).
Qed.

(* -------------------------------------------------------------------- *)

Lemma eval_assemble_word rip ii sz e a s xs v :
  lom_eqv rip s xs →
  (if e is Papp1 _ _ then false else true) →
  assemble_word_load rip ii sz e = ok a →
  sem_pexpr [::] s e = ok v →
  exists2 v', eval_asm_arg AK_mem xs a (sword sz) = ok v' & value_uincl v v'.
Proof.
  rewrite /assemble_word /eval_asm_arg => eqm.
  case: e => //=; t_xrbindP.
  - move => x _ _ /assertP ok_x /(xreg_of_varI (asm_e := x86_extra)) h.
    rewrite /get_gvar ok_x => ok_v.
    case: a h => // r ok_r; (eexists; first reflexivity).
    + exact: (xgetreg_ex eqm ok_r ok_v).  
    +  exact: (xgetregx_ex eqm ok_r ok_v).
    exact: (xxgetreg_ex eqm ok_r ok_v).
  move => sz' ?? _; case: eqP => // <-{sz'}; t_xrbindP => _ _ d ok_d <- ptr w ok_w ok_ptr uptr u ok_u ok_uptr ? ok_rd ?; subst v => /=.
  case: (eqm) => eqmem _ _ _ _ _.
  rewrite (addr_of_xpexprP eqm ok_d ok_w ok_ptr ok_u ok_uptr) -eqmem ok_rd.
  eexists; first reflexivity.
  exact: word_uincl_refl.
Qed.

Section PROG.

Context (p: lprog) (p': asm_prog) (ok_p': assemble_prog p = ok p').

Lemma ok_get_fundef fn fd :
  get_fundef (lp_funcs p) fn = Some fd →
  exists2 fd', get_fundef (asm_funcs p') fn = Some fd' & assemble_fd RSP (mk_rip p.(lp_rip)) fd = ok fd'.
Proof.
  have [_ _ _ x y ] := assemble_progP ok_p'.
  have [fd' ??] := get_map_cfprog_gen x y.
  by exists fd'.
Qed.

Lemma lom_eqv_write_var f rip s xs (x: var_i) sz (w: word sz) s' r :
  lom_eqv rip s xs →
  write_var x (Vword w) s = ok s' →
  to_var r = x →
  lom_eqv rip s' (mem_write_reg f r w xs).
Proof.
  case => eqm ok_rip [ dr drx dx df ] eqr eqrx eqx eqf.
  rewrite /mem_write_reg /write_var; t_xrbindP.
  case: s' => m vm' vm ok_vm [] <- <- hx.
  constructor => //=.
  2-4: move => r' v'.
  1-4: rewrite (get_var_set_var _ ok_vm) -hx.
  4: exact: eqx.
  1: by move: dr => /(_ r) /eqP /negbTE ->.
  1: rewrite /RegMap.set ffunE.
  case: eqP => h; last first.
  - case: eqP => [ ? | _ ]; last exact: eqr.
    by elim h; congr to_var.
  move /inj_to_var : h => ->; rewrite eqxx; t_xrbindP => /= w' ok_w' <- /=.
  case: Sumbool.sumbool_of_bool ok_w' => hsz [] <-{w'} /=.
  + by apply word_uincl_word_extend.
  by rewrite word_extend_big // hsz.
  - admit.
  rewrite /=. move: get_set_var=> hg. move: (hg (evm s) x (Vword w) vm x ok_vm).
  case: ifP=> /eqP hxeq //=. admit.
Admitted.

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

Lemma value_of_bool_uincl vb ve (b:bool) : 
  to_bool vb = ok b ->
  (∃ v' : value, value_of_bool ve = ok v' ∧ value_uincl vb v') ->
  ve = ok b.
Proof.
  move=> h [v' [] hvb /(value_uincl_bool) -/(_ _ h) [??]]; subst vb v'.
  by case: ve hvb => /= [ ? [->] | []].
Qed.

Lemma eval_assemble_cond_r ii m rf e c v:
  eqflags m rf →
  assemble_cond_r ii e = ok c →
  sem_pexpr [::] m e = ok v →
  let get x :=
    if rf x is Def b then ok b else undef_error in
  ∃ v', value_of_bool (eval_cond get c) = ok v' ∧ value_uincl v v'.
Proof.
move=> eqv; elim: e c v => //.
+ move => x c v /=; t_xrbindP => r ok_r ok_ct ok_v.
  have := gxgetflag_ex eqv ok_r ok_v.
  by case: {ok_r ok_v} r ok_ct => // -[<-] {c} /= h; eexists; split; eauto; case: (rf _).
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
    exists (b1 == b2); split => //.
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
  exists (if b1 then Vbool b2 else ~~ nb2); split => //.
  by case: hor => /and3P [/eqP ? /eqP ? /eqP ?]; subst; move: hvnb2; rewrite hvb1 hvb2 => -[<-] /=;
    case: (b1); case: (b2).
case: e2' => //= v2; case: e2 => // vn2; t_xrbindP => f1 hf1 f2 hf2 fn2 hfn2.
case: ifP => // /orP hor [<-] b1 vv1 /(gxgetflag eqv hf1) hvb1/hvb1{hvb1}hvb1.
move=> ? vv2 vv2' /(gxgetflag eqv hf2) hvb2 /sem_sop1I /= [b2 /hvb2{hvb2}hvb2 ->].
move=> /truncate_val_bool [??] ?; subst.
move=> vvn2 /(gxgetflag eqv hfn2) hvnb2.
rewrite /truncate_val /=; t_xrbindP => nb2 /hvnb2{hvnb2}hvnb2 ??; subst.
exists (if b1 then Vbool (~~b2) else nb2); split => //.
by case: hor => /and3P [/eqP ? /eqP ? /eqP ?]; subst; move: hvnb2; rewrite hvb1 hvb2 => -[<-] /=;
    case: (b1); case: (b2).
Qed.

Lemma eval_assemble_cond ii m rf e c v:
  eqflags m rf →
  assemble_cond ii e = ok c →
  sem_pexpr [::] m e = ok v →
  let get x :=
    if rf x is Def b then ok b else undef_error in
  ∃ v', value_of_bool (eval_cond get c) = ok v' ∧ value_uincl v v'.
Proof. apply eval_assemble_cond_r. Qed.

Lemma assemble_extra_op rip ii op lvs args op' lvs' args' op'' asm_args m m' s :
  sem_sopn [::] (Oasm (ExtOp op)) m lvs args = ok m' ->
  to_asm ii op lvs args = ok (op', lvs', args') ->
  assemble_asm_op assemble_cond rip ii op' lvs' args' = ok (op'', asm_args) ->
  lom_eqv rip m s ->
  exists s', eval_op op'' asm_args s = ok s' /\ lom_eqv rip m' s'.
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
      case: y ok_y => // r xr; rewrite !orbF => /eqP ? /eqP ? _; subst a0 a1; last by []; last by [].
      rewrite /eval_op /exec_instr_op /= /eval_instr_op /=.
      rewrite /truncate_word /x86_XOR /check_size_8_64 hsz64 /= wxor_xx.
      set id := instr_desc_op (XOR sz) => hlo.
      rewrite /SF_of_word msb0.
      apply: (@compile_lvals _ _ _ _ _ _ _ _ _ _ _
             rip ii m lvs m' s [:: Reg r; Reg r]
             id.(id_out) id.(id_tout)
             (let vf := Some false in let: vt := Some true in (::vf, vf, vf, vt, vt & (0%R: word sz)))
             (reg_msb_flag sz) (refl_equal _) hw hlo hcd id.(id_check_dest)).
      + move=> ii0 m0 rf e c v hf hasm hes h; subst. apply: eval_assemble_cond.
        + by apply hf.
        + by apply hasm.
        by apply hes.
      by apply erefl.
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
    by move: hidc; rewrite /check_args_kinds /= andbF.
    rewrite /eval_op /exec_instr_op /= /eval_instr_op /=.
    rewrite /truncate_word /x86_VPXOR hidc /= /x86_u128_binop /check_size_128_256 wsize_ge_U256. 
    have -> /= : (U128 ≤ sz)%CMP by case: (sz) hsz64. 
    rewrite wxor_xx; set id := instr_desc_op (VPXOR sz) => hlo.
    apply: (@compile_lvals _ _ _ _ _ _ _ _ _ _ _
             rip ii m lvs m' s [:: a0; XReg r; XReg r]
             id.(id_out) id.(id_tout)
             (0%R: word sz)
             (reg_msb_flag sz) (refl_equal _) hw hlo hcd id.(id_check_dest)).
      + move=> ii0 m0 rf e c v hf hasm hes h; subst. apply: eval_assemble_cond.
        + by apply hf.
        + by apply hasm.
        by apply hes.
      by apply erefl.
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
    have H :=
      compile_lvals (asm_e:=x86_extra) _
       (id_out := [:: E 0]) (id_tout := [:: sword256]) _ MSB_CLEAR refl_equal hwr hlow hcd refl_equal.
    have hp : (∀ (ii : instr_info) (m : estate) (rf : rflagmap) 
         (e : pexpr) (c : cond_t) (v : value),
         eqflags m rf
         → assemble_cond ii e = ok c
           → sem_pexpr [::] m e = ok v
             → let get :=
                 λ x : cfinT_finType,
                   match rf x with
                   | Def b => ok b
                   | Undef => undef_error
                   end in
               ∃ v' : value,
                 value_of_bool (eval_cond get c) = ok v' ∧ value_uincl v v').
    + move=> ii0 m0 rf e c v hf hasm hes h'; subst. apply: eval_assemble_cond.
      + by apply hf.
      + by apply hasm.
      by apply hes.
    have hp' : (reg_size < xreg_size)%CMP by apply erefl.
    move: (H hp hp')=> [s' [hwm hlow']].
    exists s'; split => //.
    move: hca; rewrite /check_sopn_args /= => /and4P [] hE1 hE2 hE3 _.
Opaque eval_arg_in_v check_i_args_kinds.
    rewrite /eval_op /exec_instr_op /= /eval_instr_op /= hch.
    have [vh' [-> /= hvh']]:= check_sopn_arg_sem_eval eval_assemble_cond hlow hE2 hvh hwh.
    have [v1 [/= -> hv1 /=]] :=
       check_sopn_arg_sem_eval eval_assemble_cond hlow hE3 refl_equal (truncate_word_u _).
Transparent eval_arg_in_v check_i_args_kinds.
    move: hE1; rewrite /check_sopn_arg /=.
    case: oseq.onth => // a.
    case: x hvl haux => x [] // hvl haux.
    case heq: xreg_of_var => [ a' | //] /andP[] hc _.
    have := xreg_of_varI heq => {heq}.
    case: a' hc => //= [ r | mmx | xmm].
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
    + rewrite /compat_imm; case:a => //= r' /orP [/eqP [?]|//] hr; subst r'.
      have heq := of_varI hr.
      move: hvl.
      rewrite /get_gvar /= -heq => hvl.
      case: hlow => _ _ _ _ /(_ _ _ hvl) hu _ _.
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
  have [v' /= [-> /= ->] /=]:= check_sopn_arg_sem_eval eval_assemble_cond hlo hca1 hva htwa.
  move: hcd; rewrite /check_sopn_dests /= /check_sopn_dest /= => /andP -[].
  case ok_y: xreg_of_var => [y|//]; move /xreg_of_varI in ok_y.
  rewrite andbT => /eqP ? _; subst a0.
  case: y hidc hca1 ok_y => // r hidc hca1 /of_varI xr.
  rewrite /mem_write_vals.
  eexists; split; first reflexivity.
  case: hlo => h1 hrip hd h2 h3 h4 h5.
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
    rewrite Fv.setP_neq //. apply h3. admit.
  + move=> r' v''; rewrite /get_var /on_vu /=.
    rewrite Fv.setP_neq. apply h4. auto.
  move=> f v''; rewrite /get_var /on_vu /=.
  by rewrite Fv.setP_neq //; apply h5.
Admitted.

Lemma assemble_iP i j ls ls' lc xs :
  let: rip := mk_rip (lp_rip p) in
  omap lfd_body (get_fundef (lp_funcs p) (lfn ls)) = Some lc ->
  match_state rip ls lc xs →
  assemble_i rip i = ok j →
  linear_sem.eval_instr p x86_mov_eop i ls = ok ls' →
  exists2 xs': x86_state,
    arch_sem.eval_instr p' j xs = ok xs'  &
    exists2 lc',
        omap lfd_body (get_fundef (lp_funcs p) (lfn ls')) = Some lc' &
        match_state rip ls' lc' xs'.
Proof.
move => omap_lc.
rewrite /linear_sem.eval_instr /arch_sem.eval_instr; case => eqm eqfn eqc eqpc.
case: i => ii [] /=.
- move => lvs op pes; t_xrbindP => -[op' asm_args] hass <- m hsem ?; subst ls'.
  have [s [-> eqm' /=]]:=
    assemble_sopnP (asm_e := x86_extra) eval_assemble_cond erefl assemble_extra_op hsem hass eqm.
  eexists; first reflexivity.
  eexists; first exact: omap_lc.
  by constructor => //=; rewrite ?to_estate_of_estate ?eqpc.
- move => [<-] [?]; subst ls'.
  eexists; first reflexivity.
  eexists; first eassumption.
  by constructor => //; rewrite /setpc eqpc.
- move => lbl [<-] [?]; subst ls'.
  eexists; first reflexivity.
  eexists; first eassumption.
  constructor => //.
  by rewrite /setpc /= eqpc.
- case => fn lbl [<-] /=; t_xrbindP => body.
  case ok_fd: get_fundef => [ fd | // ] [ ] <-{body} pc ok_pc <-{ls'}.
  case/ok_get_fundef: (ok_fd) => fd' ->.
  case/assemble_fdI => rsp_not_in_args ok_callee_saved [] xc [] _ [] _ [] ok_xc _ _ ->{fd'} /=.
  rewrite -(assemble_c_find_label lbl ok_xc) ok_pc /=.
  rewrite ok_fd /=.
  do 2 (eexists; first reflexivity).
  by constructor.
- t_xrbindP => e _ /assertP ok_e d ok_d <- ptr v ok_v ok_ptr.
  have [v' ok_v' hvv'] := eval_assemble_word eqm ok_e ok_d ok_v.
  rewrite ok_v' /= (value_uincl_word hvv' ok_ptr) /=.
  case ptr_eq: decode_label => [ [] fn lbl | // ] /=.
  replace (@decode_label (@arch_pd _ _ _ _ _ x86_decl) _ ptr) with (Some (fn, lbl));
    last by rewrite -(assemble_prog_labels ok_p').
  rewrite /=.
  case get_fd: (get_fundef _) => [ fd | // ].
  have [fd' -> ] := ok_get_fundef get_fd.
  case/assemble_fdI => rsp_not_in_args ok_callee_saved [] xc [] _ [] _ [] ok_xc _ _ ->{fd'} /=.
  t_xrbindP => pc ok_pc <-{ls'}.
  rewrite -(assemble_c_find_label lbl ok_xc) ok_pc.
  rewrite get_fd /=.
  do 2 (eexists; first reflexivity).
  by constructor.
- case => // x lbl.
  case ok_r_x: (of_var x) => [r|//]; move /of_varI in ok_r_x.
  move=> /= [<-]{j}.
  rewrite eqfn.
  case ptr_eq: encode_label => [ ptr | ] //.
  replace (encode_label _ _) with (Some ptr);
    last by rewrite -(assemble_prog_labels ok_p').
  rewrite /=.
  rewrite /sem_sopn /=.
  t_xrbindP => s' q ok_s' ? ?; subst ls' q.
  eexists; first reflexivity.
  rewrite /= -eqfn.
  exists lc; first exact: omap_lc.
  constructor => //=; last by congr _.+1.
  move: ok_s' ok_r_x.
  rewrite to_estate_of_estate zero_extend_u wrepr_unsigned.
  exact: lom_eqv_write_var.
- t_xrbindP => cnd lbl cndt ok_c <- b v ok_v ok_b.
  case: eqm => eqm hrip hd eqr eqrx eqx eqf.
  have [v' [ok_v' hvv']] := eval_assemble_cond eqf ok_c ok_v.
  case: v ok_v ok_b hvv' => // [ b' | [] // ] ok_b [?]; subst b'.
  rewrite /eval_Jcc.
  case: b ok_b => ok_b; case: v' ok_v' => // b /= ok_v' ?; subst b;
    (case: (x86_eval_cond _ _) ok_v' => // [ b | [] // ] [->] {b}).
  + t_xrbindP => lc'' ok_lc'' pc ok_pc ?; subst ls' => /=.
    move: omap_lc ok_lc''; rewrite /omap /obind /oapp => /=.
    case: get_fundef => // lfu [->]  [?]; subst lc''; clear lfu.
    rewrite /eval_JMP -(assemble_c_find_label lbl eqc) ok_pc /=.
    do 2 (eexists; first reflexivity).
    by constructor.
  case => ?; subst ls' => /=.
  eexists; first reflexivity.
  exists lc; first exact: omap_lc.
  by constructor => //; rewrite /setpc /= eqpc.
Qed.

Lemma match_state_step ls ls' lc xs :
  let: rip := mk_rip (lp_rip p) in
  omap lfd_body (get_fundef (lp_funcs p) (lfn ls)) = Some lc ->
  match_state rip ls lc xs →
  step p x86_mov_eop ls = ok ls' →
  exists2 xs',
    fetch_and_eval p' xs = ok xs' &
    exists2 lc',
      omap lfd_body (get_fundef (lp_funcs p) (lfn ls')) = Some lc' &
      match_state rip ls' lc' xs'.
Proof.
move => omap_lc.
move => ms; rewrite /step /find_instr /fetch_and_eval; case: (ms)=> _ _ eqc ->.
case ok_fd: get_fundef omap_lc => [fd|] //= [?]; subst lc.
case ok_i : (oseq.onth (lfd_body _) _) => [ i | // ].
have [j [-> ok_j]] := mapM_onth eqc ok_i.
apply: assemble_iP => //; last eassumption.
by rewrite ok_fd.
Qed.

Lemma match_state_sem ls ls' lc xs :
  let: rip := mk_rip (lp_rip p) in
  omap lfd_body (get_fundef (lp_funcs p) (lfn ls)) = Some lc ->
  lsem p x86_mov_eop ls ls' →
  match_state rip ls lc xs →
  ∃ xs' lc',
    [/\ x86sem p' xs xs' ,
        omap lfd_body (get_fundef (lp_funcs p) (lfn ls')) = Some lc' &
        match_state rip ls' lc' xs'].
Proof.
move => omap_lc.
move => h; elim/lsem_ind: h xs lc omap_lc => {ls ls'}.
- move => ls xs lc omap_lc h; exists xs; exists lc; split => //; exact: rt_refl.
move => ls1 ls2 ls3 h1 h ih xs1 lc omap_lc m1.
have [ xs2 x [ lc' omap_lc' m2 ] ] := match_state_step omap_lc m1 h1.
have [xs3 [lc''] [y omap_lc'' m3]] := ih _ _ omap_lc' m2.
exists xs3; exists lc''; split => //.
apply: asmsem_trans; last by eauto.
exact: rt_step.
Qed.

Local Notation rip := (mk_rip p.(lp_rip)).

Lemma get_xreg_of_vars_uincl ii xs rs vm vs (rm: regmap) (rxm: regxmap) (xrm: xregmap) :
  (∀ r v, get_var vm (to_var r) = ok v → value_uincl v (Vword (rm r))) →
  (∀ r v, get_var vm (to_var r) = ok v → value_uincl v (Vword (rxm r))) →
  (∀ r v, get_var vm (to_var r) = ok v → value_uincl v (Vword (xrm r))) →
  mapM (xreg_of_var ii) xs = ok rs →
  mapM (λ x : var_i, get_var vm x) xs = ok vs →
  List.Forall2 value_uincl vs 
     (map (λ a, match a with Reg r => Vword (rm r) | Regx r => Vword (rxm r) | XReg r => Vword (xrm r) | _ => undef_w U64 end) rs).
Proof.
move => hr hrx; elim: xs rs vs.
+ by move => _ _ _ [<-] [<-]; constructor.
move => x xs ih rs' vs' /=; t_xrbindP=> hxr r /(xreg_of_varI (asm_e := x86_extra)) ok_r rs ok_rs <- {rs'} v ok_v vs ok_vs <- {vs'} /=.
constructor; last exact: ih.
case: r ok_r => // r' => /of_varI rx.
+ by apply: hr; rewrite rx.
+ by apply: hrx; rewrite rx.
by apply: hxr; rewrite rx.
Qed.

Lemma x86gen_exportcall fn m vm m' vm' :
  lsem_exportcall p x86_mov_eop (sv_of_list to_var x86_callee_saved) m fn vm m' vm' →
  vm_initialized_on vm (map to_var x86_callee_saved) →
  ∀ xm,
    lom_eqv rip {| emem := m ; evm := vm |} xm →
    exists2 xm',
      x86sem_exportcall p' fn xm xm'
    & lom_eqv rip {| emem := m' ; evm := vm' |} xm'.
Proof.
  case => fd ok_fd Export lexec saved_registers /allP ok_vm xm M.
  have [ fd' ok_fd' ] := ok_get_fundef ok_fd.
  case/assemble_fdI => ok_sp ok_callee_saved [] c [] ? [] ? [] ok_c ? ? ?; subst fd'.
  set s := {| asm_m := xm ; asm_f := fn ; asm_c := c ; asm_ip := 0 |}.
  have /= := match_state_sem _ lexec.
  rewrite ok_fd => /(_ _ s erefl) []; first by constructor.
  move => [] xm' fn' c' pc' [] _ [] xexec /Some_inj <- [] /= M'.
  rewrite ok_c => ? /ok_inj ??; subst fn' c' pc'.
  exists xm'; last exact: M'.
  eexists; first exact: ok_fd'.
  - exact: Export.
  - rewrite /= -(size_mapM ok_c); exact: xexec.
  move => r hr.
  have {} hr : to_var r \in map to_var x86_callee_saved.
  - by apply/in_map; exists r => //; apply/InP.
  have /saved_registers E : Sv.In (to_var r) (sv_of_list to_var x86_callee_saved).
  - by apply/sv_of_listP.
  move/ok_vm: hr.
  case: M => /= _ _ _ M _ _.
  case: M' => /= _ _ _ M' _ _.
  move: M => /(_ r); move: M' => /(_ r).
  rewrite /get_var E.
  case: _.[_]%vmap => [ | [] // ] /= [] sz w sz_le /(_ _ erefl) /= X' /(_ _ erefl) /= X.
  rewrite /truncate_word; case: ifP => // /(cmp_le_antisym sz_le) ? _; subst sz.
  rewrite /preserved_register.
  move/word_uincl_eq: X => <-.
  move/word_uincl_eq: X' => <-.
  by [].
Qed.

Section VMAP_SET_VARS.

  Context {t : stype} {T: eqType} `{ToString t T}.
  Context (from: T → exec (psem_t t)).

  Definition vmap_set_vars : vmap → seq T → vmap :=
    foldl (λ vm x, vm.[to_var x <- from x])%vmap.

  Lemma wf_vmap_set_vars vm xs :
    wf_vm vm →
    all (λ x, match from x with Ok _ => true | Error ErrAddrUndef => if vtype (to_var x) is sarr _ then false else true | Error _ => false end) xs →
    wf_vm (vmap_set_vars vm xs).
  Proof.
    elim: xs vm => // x xs ih vm h /= /andP[] ok_x ok_xs; apply: ih ok_xs.
    move => y; rewrite Fv.setP.
    case: eqP => ?; last exact: h.
    subst.
    case: (from x) ok_x => // - [] //.
    change (vtype (to_var x)) with rtype.
    by case: rtype.
  Qed.

  Lemma get_var_vmap_set_vars_other vm xs y :
    all (λ x, to_var x != y) xs →
    get_var (vmap_set_vars vm xs) y = get_var vm y.
  Proof.
    elim: xs vm => // x xs ih vm /= /andP[] x_neq_y /ih ->.
    apply: get_var_neq.
    exact/eqP.
  Qed.

  Lemma get_var_vmap_set_vars_other_type vm xs y :
    vtype y != t →
    get_var (vmap_set_vars vm xs) y = get_var vm y.
  Proof.
    move => /eqP neqt; apply: get_var_vmap_set_vars_other.
    by apply/allP => x _; apply/eqP => ?; subst y.
  Qed.

  Lemma get_var_vmap_set_vars_finite vm xs y :
    Finite.axiom xs →
    get_var (vmap_set_vars vm xs) (to_var y) = on_vu (@pto_val t) undef_error (from y).
  Proof.
    move => finT.
    move: vm.
    have {finT} : y \in xs.
    - by rewrite -has_pred1 has_count finT.
    elim: xs => // x xs; rewrite inE.
    case y_xs: (y \in xs).
    + move => /(_ erefl) ih _ vm; exact: ih.
    rewrite orbF => _ /eqP <-{x} vm /=.
    rewrite get_var_vmap_set_vars_other; first exact: get_var_eq.
    by apply/allP => x x_xs; apply/eqP => /inj_to_var ?; subst x; rewrite x_xs in y_xs.
  Qed.

End VMAP_SET_VARS.
Definition vmap_of_x86_mem (sp: word Uptr) (rip: Ident.ident) (s: x86_mem) : vmap :=
  let vm := vmap0.[to_var RSP <- ok (pword_of_word sp)].[ vid rip <- ok (pword_of_word (asm_rip s))]%vmap in
  let vm := vmap_set_vars (λ r : register, ok (pword_of_word (asm_reg s r))) vm registers in
  let vm := vmap_set_vars (λ r : register_ext, ok (pword_of_word (asm_regx s r))) vm regxs in
  let vm := vmap_set_vars (λ r : xmm_register, ok (pword_of_word (asm_xreg s r))) vm xmm_registers in
  let vm := vmap_set_vars (λ r : rflag, if asm_flag s r is Def b then ok b else pundef_addr sbool) vm rflags in
  vm.

Lemma wf_vmap_of_x86_mem sp rip s :
  wf_vm (vmap_of_x86_mem sp rip s).
Proof.
  repeat apply: wf_vmap_set_vars => //.
  - repeat apply: wf_vm_set.
    exact: wf_vmap0.
  elim: rflags => // r rflags ih.
  apply/andP; split; last exact: ih.
  by case: (asm_flag _ _).
Qed.

 Lemma get_var_vmap_of_x86_mem sp rip s r :
   get_var (vmap_of_x86_mem sp rip s) (var_of_asm_typed_reg r) = get_typed_reg_value s r.
Proof.
  rewrite /vmap_of_x86_mem.
  case: r => r.
  all: repeat (rewrite get_var_vmap_set_vars_other_type; last by []).
  - admit.
  all: rewrite get_var_vmap_set_vars_finite //=. 
  - exact: regxs_fin_axiom.
  - exact: xmm_registers_fin_axiom.
  - by case: (asm_flag s r).
  exact: rflags_fin_axiom.
  (*- exact: registers_fin_axiom. *)
Admitted.

Definition estate_of_x86_mem (sp: word Uptr) (rip: Ident.ident) (s: x86_mem) : estate :=
  {| emem := asm_mem s ; evm := vmap_of_x86_mem sp rip s |}.

Lemma lom_eqv_estate_of_x86_mem sp rip s :
  disj_rip (vid rip) →
  lom_eqv (vid rip) (estate_of_x86_mem sp rip s) s.
Proof using.
  case => rip_not_reg rip_not_regx rip_not_xreg rip_not_flag.
  split => //=.
  (* rip *)
  - rewrite /vmap_of_x86_mem.
    repeat (rewrite get_var_vmap_set_vars_other_type; last by []).
    rewrite get_var_vmap_set_vars_other; last first.
    + apply/allP => r _; apply/eqP; exact: rip_not_regx.
      admit. (*rewrite get_var_eq.*)
  (* reg *)
  - move => r v.
    by rewrite (get_var_vmap_of_x86_mem _ _ _ (ARReg r)) => /= /ok_inj <-.
  (* regx *)
  - move => r v.
    by rewrite (get_var_vmap_of_x86_mem _ _ _ (ARegX r)) => /= /ok_inj <-.
  (* xreg *)
  - move => r v.
    by rewrite (get_var_vmap_of_x86_mem _ _ _ (AXReg r)) => /= /ok_inj <-.
  move => r v.
  rewrite /= /vmap_of_x86_mem.
  set q := (X in vmap_set_vars _ X).
  generalize (get_var_vmap_set_vars_finite (λ r : rflag, match asm_flag s r with Def b => ok b | Undef => pundef_addr sbool end) q r rflags_fin_axiom).
  rewrite get_varE.
  case: _.[_]%vmap => /=; case: (asm_flag s r) => //=.
  - by move => ? ? /ok_inj -> /ok_inj ->.
  by move => _ [] -> /ok_inj ->.
Admitted.
Global Opaque vmap_of_x86_mem.

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
