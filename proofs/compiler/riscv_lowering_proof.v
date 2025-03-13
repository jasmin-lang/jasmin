From mathcomp Require Import ssreflect ssrfun ssrbool eqtype order ssralg.
Import
  Order.POrderTheory
  Order.TotalTheory.
From mathcomp Require Import word_ssrZ.

From Coq Require Import Lia.

Require Import
  compiler_util
  expr
  lowering
  lowering_lemmas
  psem
  utils.
Require Import
  arch_extra
  sem_params_of_arch_extra.
Require Import
  riscv_decl
  riscv_extra
  riscv_instr_decl
  riscv_lowering.

Section PROOF.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {atoI : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {pT : progT}
  {sCP : semCallParams}
  (p : prog)
  (ev : extra_val_t)
  (options : lowering_options)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars).
Notation lower_cmd :=
  (lower_cmd
     (fun _ _ _ => lower_i)
     options
     warning
     fv).
Notation lower_prog :=
  (lower_prog
     (fun _ _ _ => lower_i)
     options
     warning
     fv).

Notation p' := (lower_prog p).

(* -------------------------------------------------------------------- *)

#[ local ]
Definition Pi (s0 : estate) (i : instr) (s1 : estate) :=
  sem p' ev s0 (lower_i i) s1.

#[ local ]
Definition Pi_r (s0 : estate) (i : instr_r) (s1 : estate) :=
  forall ii, Pi s0 (MkI ii i) s1.

#[ local ]
Definition Pc (s0 : estate) (c : cmd) (s1 : estate) :=
  sem p' ev s0 (lower_cmd c) s1.

#[ local ]
Definition Pfor
  (i : var_i) (rng : seq Z) (s0 : estate) (c : cmd) (s1 : estate) :=
    sem_for p' ev i rng s0 (lower_cmd c) s1.

#[ local ]
Definition Pfun
  scs0 (m0 : mem) (fn : funname) (vargs : seq value) scs1 (m1 : mem) (vres : seq value) :=
  sem_call p' ev scs0 m0 fn vargs scs1 m1 vres.


#[ local ]
Lemma Hskip : sem_Ind_nil Pc.
Proof.
  exact: (Eskip p' ev).
Qed.

#[ local ]
Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ hpi _ hpc.
  exact: (sem_app hpi hpc).
Qed.

#[ local ]
Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Proof.
  move=> ii i s1 s2 _ hi. exact: hi.
Qed.

(* TODO: factorize with x86 *)
Lemma to_word_m sz sz' a w :
  to_word sz a = ok w ->
  (sz' ≤ sz)%CMP ->
  to_word sz' a = ok (zero_extend sz' w).
Proof.
  clear.
  case/to_wordI' => n [] m [] sz_le_n ->{a} ->{w} /= sz'_le_sz.
  by rewrite truncate_word_le ?zero_extend_idem // (cmp_le_trans sz'_le_sz sz_le_n).
Qed.

(* TODO: factorize with x86 *)
Lemma check_shift_amountP e sa s z w :
  check_shift_amount e = Some sa ->
  sem_pexpr true (p_globs p) s e = ok z ->
  to_word U8 z = ok w ->
  Sv.Subset (read_e sa) (read_e e) /\
  exists2 n, sem_pexpr true (p_globs p) s sa >>= to_word U8 = ok n & forall f (a: word U32), sem_shift f a w = sem_shift f a (wand n (wrepr U8 31)).
Proof.
  rewrite /check_shift_amount.
  case en: is_wconst => [ n | ].
  - case: eqP; last by [].
    move => n_in_range /Some_inj <-{sa} ok_z ok_w.
    have! := (is_wconstP true (p_globs p) s en).
    rewrite {en} ok_z /= ok_w => /ok_inj ?; subst w.
    split; first by [].
    exists n; first reflexivity.
    by rewrite -n_in_range.
  case: {en} e => // - [] // sz' a b.
  case en: is_wconst => [ n | ]; last by [].
  case: eqP; last by [].
  move => ? /Some_inj ? /=; subst a n.
  rewrite /sem_sop2 /=; t_xrbindP => a ok_a c ok_c wa ok_wa wb ok_wb <-{z} /truncate_wordP[] _ ->{w}.
  have! := (is_wconstP true (p_globs p) s en).
  rewrite {en} ok_a ok_c /= => hc.
  split.
  - clear; rewrite {2}/read_e /= !read_eE; SvD.fsetdec.
  eexists; first by rewrite (to_word_m ok_wa (wsize_le_U8 _)).
  move => f x; rewrite /sem_shift; do 2 f_equal.
  have := to_word_m ok_wb (wsize_le_U8 _).
  rewrite {ok_wb} hc => /ok_inj ->.
  by rewrite wand_zero_extend; last exact: wsize_le_U8.
Qed.

#[ local ]
Lemma Hassgn_op2_generic s e1 e2 v1 v2 op2 v ws v' lv s1 (op2' : sopn) :
  sem_pexpr true (p_globs p) s e1 = ok v1 ->
  sem_pexpr true (p_globs p) s e2 = ok v2 ->
  sem_sop2 op2 v1 v2 = ok v ->
  truncate_val (sword ws) v = ok v' ->
  write_lval true (p_globs p) lv v' s = ok s1 ->
  i_valid (sopn.get_instr_desc op2') ->
  forall ws1 ws2 ws3 ws1' ws2'
    (eq1 : type_of_op2 op2 = (sword ws1, sword ws2, sword ws3))
    (eq2 : tin (sopn.get_instr_desc op2') = [::sword ws1'; sword ws2'])
    (eq3 : tout (sopn.get_instr_desc op2') = [:: sword ws]),
  (ws <= ws3)%CMP
  /\ exists w1 w2, [/\
      to_word ws1 v1 = ok w1,
      to_word ws2 v2 = ok w2 &
      forall e1' e2' w1' w2'
        (hcmp1 : (ws1' <= ws1)%CMP)
        (hcmp2 : (ws2' <= ws2)%CMP),
        sem_pexpr true (p_globs p) s e1' >>= to_word ws1 = ok w1' ->
        sem_pexpr true (p_globs p) s e2' >>= to_word ws2 = ok w2' ->
        Let w := ecast t (let t := t in _) eq1 (sem_sop2_typed op2) w1 w2 in
        ok (zero_extend ws w)
        = ecast l (sem_prod l _) eq2
            (ecast l (sem_prod _ (exec (sem_tuple l))) eq3
              (semi (sopn.get_instr_desc op2')))
            (zero_extend ws1' w1') (zero_extend ws2' w2') ->
        sem_sopn (p_globs p) op2' s [::lv] [:: e1'; e2'] = ok s1].
Proof.
  move=> ok_v1 ok_v2 ok_v htrunc hwrite hvalid ws1 ws2 ws3 ws1' ws2' eq1 eq2 eq3.
  move: ok_v.
  rewrite /sem_sop2; move: (sem_sop2_typed op2).
  rewrite -> eq1 => /= sem_sop2_typed ok_v.
  rewrite /sem_sopn /= /exec_sopn /= /sopn_sem /sopn_sem_ hvalid /=.
  move: (semi (sopn.get_instr_desc op2')).
  rewrite -> eq2, -> eq3 => semi.
  move: ok_v.
  t_xrbindP=> w1 ok_w1 w2 ok_w2 w ok_w ?; subst.
  move: htrunc; rewrite /truncate_val /=.
  t_xrbindP=> _ /truncate_wordP [hcmp3 ->] ?; subst.
  split=> //.
  rewrite ok_w1 ok_w2 /= .
  exists w1, w2; split=> //.
  t_xrbindP=> e1' e2' w1' w2' hcmp1 hcmp2 v1' ok_v1' ok_w1' v2' ok_v2' ok_w2' eq_sem.
  rewrite ok_v1' ok_v2' /= (to_word_m ok_w1' hcmp1) (to_word_m ok_w2' hcmp2) /=.
  by rewrite -eq_sem ok_w /= hwrite.
Qed.

#[ local ]
Lemma Hassgn_op2 s e1 e2 v1 v2 op2 v v' lv s1 (op2' : sopn) :
  sem_pexpr true (p_globs p) s e1 = ok v1 ->
  sem_pexpr true (p_globs p) s e2 = ok v2 ->
  sem_sop2 op2 v1 v2 = ok v ->
  truncate_val (sword U32) v = ok v' ->
  write_lval true (p_globs p) lv v' s = ok s1 ->
  i_valid (sopn.get_instr_desc op2') ->
  forall ws
    (eq1 : type_of_op2 op2 = (sword ws, sword ws, sword ws))
    (eq2 : tin (sopn.get_instr_desc op2') = [::sword U32; sword U32])
    (eq3 : tout (sopn.get_instr_desc op2') = [:: sword U32]),
  (U32 <= ws)%CMP
  /\ exists w1 w2, [/\
      to_word ws v1 = ok w1,
      to_word ws v2 = ok w2 &
      Let w := ecast t (let t := t in _) eq1 (sem_sop2_typed op2) w1 w2 in
      ok (zero_extend U32 w)
      = ecast l (sem_prod l _) eq2
          (ecast l (sem_prod _ (exec (sem_tuple l))) eq3
            (semi (sopn.get_instr_desc op2')))
          (zero_extend U32 w1) (zero_extend U32 w2) ->
      sem_sopn (p_globs p) op2' s [::lv] [:: e1; e2] = ok s1].
Proof.
  move=> ok_v1 ok_v2 ok_v htrunc hwrite hvalid ws eq1 eq2 eq3.
  have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
    Hassgn_op2_generic ok_v1 ok_v2 ok_v htrunc hwrite hvalid eq1 eq2 eq3.
  split=> //.
  exists w1, w2; split=> //.
  apply sem_correct=> //.
  + by rewrite ok_v1.
  by rewrite ok_v2.
Qed.

#[ local ]
Lemma Hassgn_op2_shift s e1 e2 v1 v2 op2 v v' lv s1 (op2' : sopn) :
  sem_pexpr true (p_globs p) s e1 = ok v1 ->
  sem_pexpr true (p_globs p) s e2 = ok v2 ->
  sem_sop2 op2 v1 v2 = ok v ->
  truncate_val (sword U32) v = ok v' ->
  write_lval true (p_globs p) lv v' s = ok s1 ->
  i_valid (sopn.get_instr_desc op2') ->
  forall ws
    (eq1 : type_of_op2 op2 = (sword ws, sword U8, sword ws))
    (eq2 : tin (sopn.get_instr_desc op2') = [::sword U32; sword U8])
    (eq3 : tout (sopn.get_instr_desc op2') = [:: sword U32]),
  (U32 <= ws)%CMP
  /\ exists w1 w2, [/\
      to_word ws v1 = ok w1,
      to_word U8 v2 = ok w2 &
      forall e2' w2',
        sem_pexpr true (p_globs p) s e2' >>= to_word U8 = ok w2' ->
        Let w := ecast t (let t := t in _) eq1 (sem_sop2_typed op2) w1 w2 in
        ok (zero_extend U32 w)
        = ecast l (sem_prod l _) eq2
            (ecast l (sem_prod _ (exec (sem_tuple l))) eq3
              (semi (sopn.get_instr_desc op2')))
            (zero_extend U32 w1) w2' ->
        sem_sopn (p_globs p) op2' s [::lv] [:: e1; e2'] = ok s1].
Proof.
  move=> ok_v1 ok_v2 ok_v htrunc hwrite hvalid ws eq1 eq2 eq3.
  have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
    Hassgn_op2_generic ok_v1 ok_v2 ok_v htrunc hwrite hvalid eq1 eq2 eq3.
  split=> //.
  exists w1, w2; split=> //.
  move=> e2' w2' ok_w2'; rewrite -(zero_extend_u w2').
  apply sem_correct=> //.
  by rewrite ok_v1.
Qed.

Lemma decide_op_reg_immP s e1 e2 v1 v2 op_reg_reg op_reg_imm o es lv s1 :
  sem_pexpr true (p_globs p) s e1 = ok v1 ->
  sem_pexpr true (p_globs p) s e2 = ok v2 ->
  decide_op_reg_imm U32 e1 e2 (op_reg_reg) (op_reg_imm) = Some (o, es) ->
  sem_sopn (p_globs p) (Oasm op_reg_reg) = sem_sopn (p_globs p) (Oasm op_reg_imm) ->
  sem_sopn (p_globs p) (Oasm op_reg_reg) s [:: lv] [:: e1; e2] = ok s1 ->
  sem_sopn (p_globs p) (Oasm o) s [:: lv] es = ok s1.
Proof.
  move => ok_v1 ok_v2 + eq_sem.
  rewrite /riscv_lowering.decide_op_reg_imm.
  case en : is_wconst => [ t | ].
  - case : ifP => // _ [<- <-].
    by rewrite eq_sem.
  by move=> [<- <-].
Qed.

Lemma minus_insertP e1 e2 s0 ws w :
insert_minus e1 = Some e2 ->
Let x := sem_pexpr true (p_globs p) s0 e1 in to_word ws x = ok (w)%R ->
Let x := sem_pexpr true (p_globs p) s0 e2 in to_word ws x = ok (- w)%R.
Proof.
  case : e1 => // -[] // sz [] // n /= [<-] /=.
  move => /truncate_wordP [hcmp ->].
  rewrite truncate_word_le //.
  rewrite wrepr_opp.
  by rewrite wopp_zero_extend.
Qed.

#[ local ]
Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s0 s1 lv tag ty e v v' hseme htrunc hwrite.
  move=> ii.
  rewrite /Pi /=.
  set none_s :=  match ty with sword _ => _ | _ => _ end.
  case h : none_s => [ l | ]; last first.
  + apply: sem_seq_ir.
    by apply: Eassgn; eassumption.
  case : ty htrunc @none_s h => // ws htrunc.
  case h :  lower_cassgn => [[[lvs op] es] | ] //= [] <- /=.
  apply: sem_seq_ir.
  apply: Eopn.
  move : h.
  rewrite /lower_cassgn.
  case : is_lval_in_memory.
  + case : ifP => //.
    move => h_cmp [] <- <- <- /=.
    rewrite /sem_sopn /=.
    rewrite hseme /=.
    rewrite /exec_sopn /=.
    move: htrunc.
    move => /truncate_val_typeE [w [ws' [w']]] [] h_trunc  ??; subst => /=.
    rewrite h_trunc /= /sopn_sem /= h_cmp /=.
    rewrite zero_extend_u.
    by rewrite hwrite.
  case: e hseme => //=.
  + move => g hseme.
    rewrite /lower_Pvar.
    case: eqP => //.
    move => ?; subst => /= -[] <- <- <-.
    case: is_var_in_memory.
    + rewrite /sem_sopn /= hseme /= /exec_sopn /=.
      move: htrunc.
      move => /truncate_val_typeE [w [ws' [w']]] [] h_trunc  ??; subst => /=.
      rewrite h_trunc /=.
      rewrite sign_extend_u.
      by rewrite hwrite.
    rewrite /sem_sopn /= hseme /= /exec_sopn /=.
    move: htrunc.
    move => /truncate_val_typeE [w [ws' [w']]] [] h_trunc  ??; subst => /=.
    rewrite h_trunc /=.
    by rewrite hwrite.
  + move => a a0 w g p0.
    apply: on_arr_gvarP => n t gty h_getgvar.
    t_xrbindP.
    move=> z z0 hseme z1 z2 h_okz2 ?; subst.
    rewrite /lower_load /chk_ws_reg.
    case: eqP => //=.
    move => ?; subst.
    move=> [] <- <- <-.
    + rewrite /sem_sopn /= hseme /= h_getgvar /= z1 /= h_okz2 /= /exec_sopn /=.
      move: htrunc.
      rewrite /truncate_val /=.
      t_xrbindP.
      move=> z3 -> ?; subst => /=.
      rewrite sign_extend_u.
      by rewrite hwrite.
  + move => a w v0 p0.
    t_xrbindP.
    move=> z z0 hgetvar htoword z1 z2 hseme ok_z1 z3 hread ?; subst.
    rewrite /lower_load /chk_ws_reg.
    case: eqP => //=.
    move => ?; subst.
    move=> [] <- <- <-.
    + rewrite /sem_sopn /= hseme /= hgetvar /= ok_z1 /= htoword /= hread /= /exec_sopn /=.
      move: htrunc.
      rewrite /truncate_val /=.
      t_xrbindP.
      move=> z4 -> ?; subst => /=.
      rewrite sign_extend_u.
      by rewrite hwrite.
  + move => s p0 hseme.
    rewrite /lower_Papp1 /chk_ws_reg.
    case: eqP => //= ?; subst.
    case: s hseme => //.
    + move => w /= hseme.
      case: is_constP hseme => a //= hseme.
      move=> [] <- <- <-.
      rewrite /sem_sopn /= /exec_sopn /= truncate_word_u /=.
      move: hseme htrunc.
      rewrite /sem_sop1 /= => -[] <-.
      rewrite /truncate_val /=.
      t_xrbindP.
      move => z /truncate_wordP [] hcmp ->.
      rewrite zero_extend_wrepr // => ->.
      by rewrite hwrite.
    + move => w w0 hseme /=.
      case: w hseme => // hseme.
      case hle: (w0 ≤ U32)%CMP => //=.
      case: is_load => //=.
      move => [] <- <- <-.
      rewrite /sem_sopn /=.
      move: hseme.
      t_xrbindP.
      move => z -> /=.
      rewrite /sem_sop1 /=.
      t_xrbindP.
      move => z0 /to_wordI' [] ws [] x [] hcmp -> -> ?; subst.
      rewrite /exec_sopn /=.
      move: htrunc.
      rewrite /truncate_val /= truncate_word_u /= => -[] ?; subst.
      rewrite truncate_word_le //= /sopn_sem /= hle /=.
      by rewrite hwrite.
    + move => w w0 hseme /=.
      case: w hseme => // hseme.
      case hle: (w0 ≤ U16)%CMP => //=.
      case: is_load => //=.
      move => [] <- <- <-.
      rewrite /sem_sopn /=.
      move: hseme.
      t_xrbindP.
      move => z -> /=.
      rewrite /sem_sop1 /=.
      t_xrbindP.
      move => z0 /to_wordI' [] ws [] x [] hcmp -> -> ?; subst.
      rewrite /exec_sopn /=.
      move: htrunc.
      rewrite /truncate_val /= truncate_word_u /= => -[] ?; subst.
      rewrite truncate_word_le //= /sopn_sem /= hle /=.
      by rewrite hwrite.
    + move => ws hseme.
      case: ws hseme => //= hseme.
      move=> [] <- <- <-.
      rewrite /sem_sopn.
      move: hseme.
      t_xrbindP.
      move => z /= ->.
      rewrite /sem_sop1 /=.
      t_xrbindP.
      move => z0 /to_wordI' [] ws [] x [] hcmp -> -> ?; subst.
      rewrite /exec_sopn /=.
      move: htrunc.
      rewrite /truncate_val /= truncate_word_u /= => -[] ?; subst.
      rewrite truncate_word_le //=.
      by rewrite hwrite.
    move => o hseme.
    case: o hseme => //= -[] // hseme.
    move=> [] <- <- <-.
    rewrite /sem_sopn.
    move: hseme.
    t_xrbindP.
    move => z /= ->.
    rewrite /sem_sop1 /=.
    t_xrbindP.
    move => z0 /to_wordI' [] ws [] x [] hcmp -> -> ?; subst.
    rewrite /exec_sopn /=.
    move: htrunc.
    rewrite /truncate_val /= truncate_word_u /= => -[] ?; subst.
    rewrite truncate_word_le //=.
    by rewrite hwrite.

  t_xrbindP=> s e1 e2 v1 ok_v1 v2 ok_v2 ok_v.
  rewrite /lower_Papp2 /chk_ws_reg.
  case: eqP => //= ?; subst.
  case: s ok_v => //= o ok_v.
  + case: o ok_v => //= ws ok_v.
    rewrite /riscv_lowering.decide_op_reg_imm.
    - case en : is_wconst => [ n | ].
      - case : ifP => //.
      rewrite /riscv_params_core.is_arith_small.
      move => hcmp1 /=.
      set op2' := Oasm _.
      have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
      Hassgn_op2 ok_v1 ok_v2 ok_v htrunc hwrite (op2' := op2') erefl erefl erefl.
      move=> [<- <- <-].
      by apply sem_correct; rewrite /= wadd_zero_extend.
    - set op2' := Oasm _.
      have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
      Hassgn_op2 ok_v1 ok_v2 ok_v htrunc hwrite (op2' := op2') erefl erefl erefl.
      move=> [<- <- <-].
      by apply sem_correct; rewrite /= wadd_zero_extend.
  + case: o ok_v => //= ws ok_v.
    move=> [<- <- <-].
    set op2' := Oasm _.
    have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
      Hassgn_op2 ok_v1 ok_v2 ok_v htrunc hwrite (op2' := op2') erefl erefl erefl.
    by apply sem_correct; rewrite /= wmul_zero_extend.
  + case: o ok_v => //= ws ok_v.
    rewrite /riscv_lowering.decide_op_reg_imm_neg.
    case en : is_wconst => [ n | ].
    - case : ifP => //.
      rewrite /riscv_params_core.is_arith_small_neg.
      move => hcmp1 /=.
      case h_insert: insert_minus => [e1' | //].
      set op2' := Oasm _.
      have [hcmp [w1 [w2] [ok_w1 ok_w2 sem_correct]]] := Hassgn_op2_generic ok_v1 ok_v2 ok_v htrunc hwrite (op2' := op2') erefl erefl erefl.
      move=> [<- <- <-].
      apply :(sem_correct _ _ w1 (- w2)%R) => //.
      + by rewrite ok_v1.
      + apply (minus_insertP h_insert).
        by rewrite ok_v2.
      by rewrite /= wadd_zero_extend.
    move=> [<- <- <-].
    set op2' := Oasm _.
    have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
      Hassgn_op2 ok_v1 ok_v2 ok_v htrunc hwrite (op2' := op2') erefl erefl erefl.
    by apply sem_correct; rewrite /= wsub_zero_extend.
  + case: o ok_v => // -[] [] //=.
    + rewrite /sem_sop2 /=.
      t_xrbindP=> w1 ok_w1 w2 ok_w2.
      rewrite /mk_sem_divmod /=.
      case w2_nzero: eq_op => //=.
      case: andb => //.
      move=> _ [<-] ?; subst v.
      move=> [<- <- <-].
      rewrite /sem_sopn /= ok_v1 ok_v2 /=.
      rewrite /exec_sopn /= ok_w1 ok_w2 /=.
      rewrite /riscv_div_semi w2_nzero.
      rewrite (truncate_val_subtype_eq htrunc) //.
      by rewrite hwrite.
    rewrite /sem_sop2 /=.
    t_xrbindP=> w1 ok_w1 w2 ok_w2.
    rewrite /mk_sem_divmod orbF /=.
    case w2_nzero: eq_op => //=.
    move=> _ /ok_inj <- ?; subst v.
    move=> [<- <- <-].
    rewrite /sem_sopn /= ok_v1 ok_v2 /=.
    rewrite /exec_sopn /= ok_w1 ok_w2 /=.
    rewrite /riscv_divu_semi w2_nzero.
    rewrite (truncate_val_subtype_eq htrunc) //.
    by rewrite hwrite.
  + case: o ok_v => // -[] [] //=.
    + rewrite /sem_sop2 /=.
      t_xrbindP=> w1 ok_w1 w2 ok_w2.
      rewrite /mk_sem_divmod /=.
      case: eq_op => //=.
      case: andb => //.
      move=> _ [<-] ?; subst v.
      move=> [<- <- <-].
      rewrite /sem_sopn /= ok_v1 ok_v2 /=.
      rewrite /exec_sopn /= ok_w1 ok_w2 /=.
      rewrite /riscv_rem_semi.
      rewrite (truncate_val_subtype_eq htrunc) //.
      by rewrite hwrite.
    rewrite /sem_sop2 /=.
    t_xrbindP=> w1 ok_w1 w2 ok_w2.
    rewrite /mk_sem_divmod orbF.
    case: eq_op => //=.
    move=> _ /ok_inj <- ?; subst v.
    move=> [<- <- <-].
    rewrite /sem_sopn /= ok_v1 ok_v2 /=.
    rewrite /exec_sopn /= ok_w1 ok_w2 /=.
    rewrite /riscv_div_semi.
    rewrite (truncate_val_subtype_eq htrunc) //.
    by rewrite hwrite.
  + case h: decide_op_reg_imm => [[ol esi] | ] //= [<- <- <-].
    apply: (decide_op_reg_immP ok_v1 ok_v2 h erefl).
    set op2' := Oasm _.
    have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
    Hassgn_op2 ok_v1 ok_v2 ok_v htrunc hwrite (op2' := op2') erefl erefl erefl.
    by apply sem_correct; rewrite /= -wand_zero_extend.
  + case h: decide_op_reg_imm => [[ol esi] | ] //= [<- <- <-].
    apply: (decide_op_reg_immP ok_v1 ok_v2 h erefl).
    set op2' := Oasm _.
    have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
      Hassgn_op2 ok_v1 ok_v2 ok_v htrunc hwrite (op2' := op2') erefl erefl erefl.
    by apply sem_correct; rewrite /= -wor_zero_extend.
  + case h: decide_op_reg_imm => [[ol esi] | ] //= [<- <- <-].
    apply: (decide_op_reg_immP ok_v1 ok_v2 h erefl).
    set op2' := Oasm _.
    have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
      Hassgn_op2 ok_v1 ok_v2 ok_v htrunc hwrite (op2' := op2') erefl erefl erefl.
    by apply sem_correct; rewrite /= -wxor_zero_extend.
  + case: o ok_v => // ok_v.
    case good_shift: check_shift_amount => [ sa | ] //.
    move=> [<- <- <-].
    rewrite !fun_if if_same.
    set op2' := Oasm _.
    have [_ [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
      Hassgn_op2_shift ok_v1 ok_v2 ok_v htrunc hwrite (op2' := op2') erefl erefl erefl.
    have [_ [wa ok_wa eq_shift]] := check_shift_amountP good_shift ok_v2 ok_w2.
    apply (sem_correct _ _ ok_wa).
    by rewrite /= !zero_extend_u /sem_shr eq_shift.
  + case: o ok_v => // ws ok_v.
    case good_shift: check_shift_amount => [ sa | ] //.
    move=> [<- <- <-].
    rewrite !fun_if if_same.
    set op2' := Oasm _.
    have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
      Hassgn_op2_shift ok_v1 ok_v2 ok_v htrunc hwrite (op2' := op2') erefl erefl erefl.
    have [_ [wa ok_wa eq_shift]] := check_shift_amountP good_shift ok_v2 ok_w2.
    apply (sem_correct _ _ ok_wa).
    rewrite /= zero_extend_wshl //; last by have [? _] := wunsigned_range w2.
    by rewrite -/(sem_shift _ _ _) eq_shift.
  case: o ok_v => // -[] // ok_v.
  case good_shift: check_shift_amount => [ sa | ] //.
  move=> [<- <- <-].
  rewrite !fun_if if_same.
  set op2' := Oasm _.
  have [hcmp [w1 [w2 [ok_w1 ok_w2 sem_correct]]]] :=
    Hassgn_op2_shift ok_v1 ok_v2 ok_v htrunc hwrite (op2' := op2') erefl erefl erefl.
  have [_ [wa ok_wa eq_shift]] := check_shift_amountP good_shift ok_v2 ok_w2.
  apply (sem_correct _ _ ok_wa).
  by rewrite /= !zero_extend_u /sem_sar eq_shift.
Qed.

#[ local ]
Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move=> s0 s1 tag op lvs es hsem01.
  move=> ii.

  rewrite /Pi /=.

  case h : lower_copn => [l | ];
  last by apply: sem_seq_ir; apply: Eopn.
  move: h.

  case: op hsem01 => // -[] //=.
  + move => [] // hsem01.
    rewrite /lower_mulu.
    case: lvs hsem01 => // -[] // r1 [] // [] // r2 [] // hsem01.
    case: es hsem01 => // -[] // x [] // [] // y [] // hsem01.
    case: ifP => // /Bool.orb_false_elim [] /negbT h_neqx /negbT h_neqy.
    move => [] <-.
    move: hsem01.
    rewrite /sem_sopn /=.
    t_xrbindP.
    move => vs _ v1 ok_v1 _ v2 ok_v2 <- <-.
    rewrite /exec_sopn /= /sopn_sem /= /sopn_sem_ /=.
    t_xrbindP => _ w0 ok_w0 w1 ok_w1 <- <- /=.
    t_xrbindP => s2 ok_s2 {}s1 ok_s1 <-.
    apply: (Eseq (s2:=s2)).
    + apply: EmkI.
      apply: Eopn.
      by rewrite /sem_sopn /= ok_v1 /= ok_v2 /= /exec_sopn /= ok_w0 /= ok_w1 /= ok_s2.
    apply: sem_seq_ir.
    apply: Eopn.
    rewrite /sem_sopn /=.
    do 2 rewrite (write_get_gvarP_neq _ _ ok_s2) //.
    rewrite ok_v1 ok_v2 /=.
    rewrite /exec_sopn /=.
    rewrite ok_w0 ok_w1 /sopn_sem /=.
    move: ok_s1.
    by rewrite wrepr_mul !wrepr_unsigned => ->.

  move=> ty hsem01.
  case: ty hsem01 => [|| len | ws ] // hsem01.
  + rewrite /lower_swap.
    move => [] <- /=.
    apply: sem_seq_ir.
    by apply: Eopn.
  rewrite /lower_swap.
  case: ifP => // hcmp.
  move => [] <- /=.
  apply: sem_seq_ir.
  by apply: Eopn.
Qed.

#[ local ]
Lemma Hsyscall : sem_Ind_syscall p Pi_r.
Proof.
  move=> s1 scs m s2 o xs es ves vs hes ho hw ii.
  apply: sem_seq_ir.
  by apply: Esyscall; eassumption.
Qed.

#[ local ]
Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  move=> s0 s1 e c0 c1 hseme _ hc ii.
  apply: sem_seq_ir.
  by apply: Eif_true; eassumption.
Qed.

#[ local ]
Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  move=> s0 s1 e c0 c1 hseme _ hc ii.
  apply: sem_seq_ir.
  by apply: Eif_false; eassumption.
Qed.

#[ local ]
Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  move=> s0 s1 s2 s3 al c0 e info c1 _ hc0 hseme _ hc1 _ hwhile ii.
  rewrite /Pi /=.
  apply: sem_seq_ir.
  apply: (Ewhile_true hc0 hseme hc1).
  move: (hwhile ii).
  rewrite /Pi_r /Pi.
  by rewrite /lower_i -/lower_i => /sem_seq1_iff /sem_IE.
Qed.

#[ local ]
Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> s0 s1 al c0 e info c1 _ hc0 hseme ii.
  rewrite /Pi /=.
  apply: sem_seq_ir.
  by apply: Ewhile_false; eassumption.
Qed.

#[ local ]
Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Proof.
  move=> s0 s1 i d lo hi c vlo vhi hlo hhi _ hfor ii.
  rewrite /Pi /=.
  apply: sem_seq_ir.
  by apply: Efor; eassumption.
Qed.

#[ local ]
Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof.
  move=> s0 i c.
  rewrite /Pfor.
  by apply: EForDone; eassumption.
Qed.

#[ local ]
Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  move=> s0 s1 s2 s3 i v vs c hwrite hsem hc hsemf hfor.
  rewrite /Pfor.
  by apply: EForOne; eassumption.
Qed.

#[ local ]
Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
Proof.
  move=> s0 scs0 m0 s1 lvs fn args vargs vs hsemargs _ hfun hwrite ii.
  rewrite /Pi /=.
  apply: sem_seq_ir.
  by apply: Ecall; eassumption.
Qed.

#[ local ]
Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
Proof.
  move=> scs0 m0 scs1 m1 fn fd vargs vargs' s0 s1 s2 vres vres'.
  move=> hget htruncargs hinit hwrite _ hc hres htruncres hscs hfin.
  rewrite /Pfun.
  by apply: EcallRun; first (by rewrite get_map_prog hget /=; reflexivity); eassumption.
Qed.

Lemma lower_callP
  (f : funname) scs mem scs' mem' (va vr : seq value) :
  (* Calling f in a given context implies calling f in the same context except p -> p compiled. *)
  sem_call p ev scs mem f va scs' mem' vr
  -> sem_call (lower_prog p) ev scs mem f va scs' mem' vr.
Proof.
  (* <=> by apply: *)
  exact:
    (sem_call_Ind
       Hskip
       Hcons
       HmkI
       Hassgn
       Hopn
       Hsyscall
       Hif_true
       Hif_false
       Hwhile_true
       Hwhile_false
       Hfor
       Hfor_nil
       Hfor_cons
       Hcall
       Hproc).
Qed.

End PROOF.

