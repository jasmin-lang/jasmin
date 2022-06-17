(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem compiler_util.
Require Export lea.
Import Utf8.
Import ssrring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap_scope.
Local Open Scope seq_scope.

Section PROOF.
  Context {pd:PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.
  Context (gd: glob_decls).

  (* ---------------------------------------------------------- *)

  Definition sem_lea sz vm l : exec (word sz) :=
    Let base :=
      oapp (fun (x:var_i) => get_var vm x >>= to_word sz) (ok 0%R) l.(lea_base) in
    Let offset :=
      oapp (fun (x:var_i) => get_var vm x >>= to_word sz) (ok 0%R) l.(lea_offset) in
    ok (zero_extend sz l.(lea_disp) + (base + (zero_extend sz l.(lea_scale) * offset)))%R.

  Lemma lea_constP sz w vm : sem_lea sz vm (lea_const w) = ok (zero_extend sz w).
  Proof. by rewrite /sem_lea /lea_const /=; f_equal; ssring. Qed.

  Lemma lea_varP x sz vm : sem_lea sz vm (lea_var x) = get_var vm x >>= to_word sz.
  Proof.
    rewrite /sem_lea /lea_var /=.
    case: (Let _ := get_var _ _ in _) => //= w.
    rewrite zero_extend0 zero_extend1; f_equal; ssring.
  Qed.

  Lemma mkLeaP sz d b sc o vm w :
    sem_lea sz vm (MkLea d b sc o) = ok w ->
    sem_lea sz vm (mkLea d b sc o) = ok w.
  Proof.
  rewrite /mkLea; case: eqP => // ->; rewrite /sem_lea /=; t_xrbindP => w1 -> /= w2 _ <-.
  f_equal; rewrite zero_extend0 zero_extend1; ssring.
  Qed.

  Lemma lea_mulP sz l1 l2 w1 w2 l vm :
    (sz <= Uptr)%CMP ->
    sem_lea sz vm l1 = ok w1 -> sem_lea sz vm l2 = ok w2 ->
    lea_mul l1 l2 = Some l ->
    sem_lea sz vm l = ok (w1 * w2)%R.
  Proof.
    move=> hsz.
    case: l1 l2 => d1 [b1|] sc1 [o1|] [d2 [b2|] sc2 [o2|]] //=; rewrite {1 2}/sem_lea /=.
    + apply: rbindP => wb1 Hb1 [<-] [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Hb1 /=.
      by f_equal; rewrite wmul_zero_extend //; ssring.
    + apply: rbindP => wo1 Ho1 [<-] [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Ho1 /=.
      by f_equal; rewrite !wmul_zero_extend //; ssring.
    + move=> [<-];apply: rbindP => wb2 Hb2 [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Hb2 /=.
      by f_equal; rewrite wmul_zero_extend //; ssring.
    + move=> [<-];apply: rbindP => wo2 Ho2 [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Ho2 /=.
      by f_equal; rewrite !wmul_zero_extend //; ssring.
    move=> [<-] [<-] [<-].
    by rewrite lea_constP; f_equal; rewrite wmul_zero_extend //; ssring.
  Qed.

  Lemma lea_addP sz l1 l2 w1 w2 l vm :
    (sz <= Uptr)%CMP ->
    sem_lea sz vm l1 = ok w1 -> sem_lea sz vm l2 = ok w2 ->
    lea_add l1 l2 = Some l ->
    sem_lea sz vm l = ok (w1 + w2)%R.
  Proof.
    move=> hsz.
    case: l1 l2 => d1 [b1|] sc1 [o1|] [d2 [b2|] sc2 [o2|]] //=; rewrite {1 2}/sem_lea /=.
    + by apply: rbindP => wb1 Hb1; apply: rbindP => wo1 Ho1 [<-] [<-] [<-];
       apply mkLeaP;rewrite /sem_lea /= Hb1 /= Ho1 /=; f_equal; rewrite !wadd_zero_extend //; ssring.
    + by apply: rbindP => wb1 Hb1 [<-]; apply: rbindP => wb2 Hb2 [<-] [<-];
        apply mkLeaP;rewrite /sem_lea /= Hb1 /= Hb2 /=; f_equal; rewrite !wadd_zero_extend // zero_extend1; ssring.
    + by apply: rbindP => wb1 Hb1 [<-]; apply: rbindP => wo2 Ho2 [<-] [<-];
        apply mkLeaP;rewrite /sem_lea /= Hb1 /= Ho2 /=; f_equal; rewrite !wadd_zero_extend //; ssring.
    + by apply: rbindP => zb Hb [<-] [<-] [<-];apply mkLeaP;
       rewrite /sem_lea /= Hb /=; f_equal; rewrite !wadd_zero_extend //; ssring.
    + apply: rbindP => zoff1 Hoff1 [<-]; apply: rbindP => zb2 Hb2 [<-] [<-];apply mkLeaP.
      by rewrite /sem_lea /= Hoff1 /= Hb2 /=; f_equal; rewrite !wadd_zero_extend //; ssring.
    + apply: rbindP => zo1 Ho1 [<-];apply: rbindP => zo2 Ho2 [<-].
      case:eqP => [-> | _].
      + by move=> [<-];apply mkLeaP;rewrite /sem_lea /= Ho1 /= Ho2 /=; f_equal; rewrite !wadd_zero_extend // zero_extend1; ssring.
      case:eqP => //= -> [<-];apply mkLeaP;rewrite /sem_lea /= Ho1 /= Ho2 /=.
      by f_equal; rewrite !wadd_zero_extend // zero_extend1; ssring.
    + apply: rbindP => zo1 Ho1 [<-] [<-] [<-];apply mkLeaP;rewrite /sem_lea /= Ho1 /=.
      by f_equal; rewrite !wadd_zero_extend //; ssring.
    + move=> [<-];apply: rbindP => zb2 Hb2;apply: rbindP => zo2 Ho2 [<-] [<-].
      by apply mkLeaP; rewrite /sem_lea /= Hb2 /= Ho2 /=; f_equal; rewrite !wadd_zero_extend //; ssring.
    + move=> [<-];apply: rbindP => zb2 Hb2 [<-] [<-];apply mkLeaP.
      by rewrite /sem_lea /= Hb2 /=; f_equal; rewrite !wadd_zero_extend //; ssring.
    + move=> [<-];apply:rbindP=> zo2 Ho2 [<-] [<-];apply mkLeaP.
      by rewrite /sem_lea /= Ho2 /=; f_equal; rewrite !wadd_zero_extend //; ssring.
    by move=> [<-] [<-] [<-];apply mkLeaP;rewrite /sem_lea /=; f_equal; rewrite !wadd_zero_extend //; ssring.
  Qed.

  Lemma lea_subP sz l1 l2 w1 w2 l vm :
    (sz <= Uptr)%CMP ->
    sem_lea sz vm l1 = ok w1 -> sem_lea sz vm l2 = ok w2 ->
    lea_sub l1 l2 = Some l ->
    sem_lea sz vm l = ok (w1 - w2)%R.
  Proof.
    move=> hsz.
    case: l1 l2 => d1 b1 sc1 o1 [d2 [b2|] sc2 [o2|]] //=; rewrite {1 2}/sem_lea /=.
    t_xrbindP => vb1 hb1 vo1 ho1 <- <- [<-] /=;apply mkLeaP.
    by rewrite /sem_lea /= hb1 ho1 /=; f_equal; rewrite wsub_zero_extend //; ssring.
  Qed.

  Lemma mk_lea_recP s e l sz sz' (w: word sz') :
    (sz <= Uptr)%CMP -> 
    (sz ≤ sz')%CMP →
    mk_lea_rec sz e = Some l ->
    sem_pexpr gd s e = ok (Vword w) ->
    sem_lea sz (evm s) l = ok (zero_extend sz w).
  Proof.
    move=> hsz.
    elim: e l sz' w => //=.
    + move=> x l sz' w hsz'; rewrite /get_gvar; case: ifP => // hlv [<-].
      by rewrite lea_varP => -> /=; f_equal; rewrite /truncate_word hsz'.
    + move=> [] //= sz1 [] //= e1 he1 l sz' w hsz' [<-]; rewrite /sem_sop1 /= => h.
      have /Vword_inj[? ? /=] := ok_inj h; subst; rewrite lea_constP /=.
      by rewrite zero_extend_sign_extend // sign_extend_truncate.
    move=> [] //= [] //= sz1 e1 He1 e2 He2 l sz' w hsz'.
    + case Heq1: mk_lea_rec => [l1|]//; case Heq2: mk_lea_rec => [l2|]// Hadd.
      rewrite /sem_sop2 /=; t_xrbindP=> > + ? + ?
        /to_wordI' [? [? [hsz1 ? ->]]] ?
        /to_wordI' [? [? [hsz2 ? ->]]] ?.
      subst=> h1 h2 [<-]; rewrite wadd_zero_extend // !zero_extend_idem //.
      exact (lea_addP hsz (He1 _ _ _ (cmp_le_trans hsz' hsz1) Heq1 h1)
                           (He2 _ _ _ (cmp_le_trans hsz' hsz2) Heq2 h2) Hadd).
    + case Heq1: mk_lea_rec => [l1|]//;case Heq2: mk_lea_rec => [l2|]// Hmul.
      rewrite /sem_sop2 /=; t_xrbindP=> > + ? + ?
        /to_wordI' [? [? [hsz1 ? ->]]] ?
        /to_wordI' [? [? [hsz2 ? ->]]] ?.
      subst=> h1 h2 [<-]; rewrite wmul_zero_extend // !zero_extend_idem //.
      exact (lea_mulP hsz (He1 _ _ _ (cmp_le_trans hsz' hsz1) Heq1 h1)
                           (He2 _ _ _ (cmp_le_trans hsz' hsz2) Heq2 h2) Hmul).
    case Heq1: mk_lea_rec => [l1|]//;case Heq2: mk_lea_rec => [l2|]// Hsub.
    rewrite /sem_sop2 /=; t_xrbindP=> > + ? + ?
        /to_wordI' [? [? [hsz1 ? ->]]] ?
        /to_wordI' [? [? [hsz2 ? ->]]] ?.
      subst=> h1 h2 [<-]; rewrite wsub_zero_extend // !zero_extend_idem //.
    exact (lea_subP hsz (He1 _ _ _ (cmp_le_trans hsz' hsz1) Heq1 h1)
                           (He2 _ _ _ (cmp_le_trans hsz' hsz2) Heq2 h2) Hsub).
  Qed.

  Lemma push_cast_szP sz e s v :  
    sem_pexpr gd s (Papp1 (Oword_of_int sz) e) = ok v ->
    exists v', sem_pexpr gd s (push_cast_sz sz e) = ok v' /\ value_uincl v v'.
  Proof.
    elim: e v; eauto.
    + move=> o e1 he1 v.
      case: o; eauto.
      move=> sz' /=.
      case: (@idP (sz <= sz')%CMP); last eauto; rewrite /sem_sop1 /=.
      t_xrbindP=> hsz > -> ? /to_wordI' [? [? [? -> ->]]] <- ? [<-] <-.
      eexists; split=> //=.
      have -> : forall w, wrepr sz (wunsigned w) = zero_extend sz w by done.
      rewrite zero_extend_idem //.
      by apply: word_uincl_zero_ext (cmp_le_trans hsz _).
    rewrite /= /sem_sop1 => o e1 he1 e2 he2 v.
    case: o; eauto; case; eauto; rewrite /= /sem_sop2 /=;
      t_xrbindP=> _ ? heq1 ? heq2 i1 /to_intI ? i2 /to_intI ? <- _ [<-] <-; subst;
      move: (he1 (Vword (wrepr sz i1))) (he2 (Vword (wrepr sz i2))) => {he1 he2};
      rewrite {}heq1 {}heq2 => [[//| ? [-> /value_uinclE [? [? [-> +]]]]]]
        [//| ? [-> /value_uinclE [? [? [-> +]]]]] /=;
      rewrite /word_uincl /truncate_word => /andP[-> /eqP <-] /andP[-> /eqP <-] /=;
      eexists; split=> //=; apply/andP; split=> //.
    + by rewrite -wrepr_add zero_extend_wrepr.
    + by rewrite -wrepr_mul zero_extend_wrepr.
    by rewrite -wrepr_sub zero_extend_wrepr.
  Qed.

  Lemma push_castP e s v :
    sem_pexpr gd s e = ok v ->
    exists v', sem_pexpr gd s (push_cast e) = ok v' /\ value_uincl v v'.
  Proof.
    elim: e v; eauto.
    + move=> o e1 he1 v /=.
      t_xrbindP => v1 /he1{he1} [v1' [he1 hu]].
      move=> /(vuincl_sem_sop1 hu).
      case o => [sz | ? | ?? | ?? | | ? | ?] he1'; try by exists v; rewrite /= he1 /= he1'.
      by apply push_cast_szP; rewrite /= he1 /= he1'.
    move=> o e1 he1 e2 he2 /=.
    t_xrbindP => ? v1 /he1 [v1' [-> hu1]] v2 /he2 [v2' [-> hu2]]. 
    by move=> /(vuincl_sem_sop2 hu1 hu2) /= ->; eauto.
  Qed.

  Lemma mk_leaP s e l sz sz' (w: word sz') :
    (sz <= Uptr)%CMP -> 
    (sz ≤ sz')%CMP →
    mk_lea sz e = Some l ->
    sem_pexpr gd s e = ok (Vword w) ->
    sem_lea sz (evm s) l = ok (zero_extend sz w).
  Proof.
    rewrite /mk_lea => h1 h2 hrec.
    move=> /push_castP [v' [he hu]].
    have [sz1 [w1 [? /andP [] hle /eqP ->]]]:= value_uinclE hu; subst v'.
    rewrite zero_extend_idem //.
    apply: mk_lea_recP hrec he => //.
    by apply: cmp_le_trans h2 hle.
  Qed.

  Definition read_ovar (o: option var_i) : Sv.t :=
    if o is Some v then read_e (mk_lvar v) else Sv.empty.

  Definition read_lea (m: lea) : Sv.t :=
    Sv.union (read_ovar m.(lea_base)) (read_ovar m.(lea_offset)).

  Lemma read_lea_mkLea d b sc o :
    Sv.Subset (read_lea (mkLea d b sc o)) (Sv.union (read_ovar b) (read_ovar o)).
  Proof. rewrite /mkLea; case: ifP => _; rewrite /read_lea /=; SvD.fsetdec. Qed.

  Ltac read_lea_mkLea :=
    match goal with
    | |- context[ read_lea (mkLea ?d ?b ?sc ?o) ] => have := @read_lea_mkLea d b sc o
    end.

  Lemma lea_add_read m1 m2 m :
    lea_add m1 m2 = Some m →
    Sv.Subset (read_lea m) (Sv.union (read_lea m1) (read_lea m2)).
  Proof.
  Local Ltac lar :=
    rewrite {-1}/read_lea /=; read_lea_mkLea; SvD.fsetdec.
  case: m1 m2 => [d1 b1 sc1 o1] [d2 b2 sc2 o2].
  case: b1 o1 => [ b1 | ] [ o1 | ] /=; last first.
  - case => <-; rewrite SvP.MP.empty_union_1; last exact: Sv.empty_spec.
    lar.
  - case: b2 => [ b2 | ].
    + case: o2 => // - [<-]; lar.
    case: o2 => [ o2 | ].
    + case: ifP => _.
      * case => <-; lar.
      case: ifP => // _ [<-]; lar.
    case => <-; lar.
  - case: b2 => [ b2 | ].
    + case: o2 => // - [<-]; lar.
    case: o2 => [ o2 | ] [<-]; lar.
  case: b2 => //; case: o2 => // - [<-]; lar.
  Qed.

  Lemma lea_mul_read m1 m2 m :
    lea_mul m1 m2 = Some m →
    Sv.Subset (read_lea m) (Sv.union (read_lea m1) (read_lea m2)).
  Proof.
  case: m1 m2 => [d1 b1 sc1 o1] [d2 b2 sc2 o2].
  case: b1 o1 b2 o2 => [ b1 | ] [ o1 | ] // [ b2 | ] // [ o2 | ] // [<-];
  last exact: SvP.MP.subset_empty;
  lar.
  Qed.

  Lemma lea_sub_read m1 m2 m :
    lea_sub m1 m2 = Some m →
    Sv.Subset (read_lea m) (Sv.union (read_lea m1) (read_lea m2)).
  Proof.
  case: m1 m2 => [d1 b1 sc1 o1] [d2 b2 sc2 o2].
  case: b2 o2 => // - [] // [<-]; lar.
  Qed.

  Lemma mk_lea_rec_read sz e m :
    mk_lea_rec sz e = Some m →
    Sv.Subset (read_lea m) (read_e e).
  Proof.
  elim: e m => //=.
  + by move => [x []] //= _ [<-]; rewrite read_e_var; apply: SvD.F.Subset_refl.
  + by case => // sz' [] // z _ _ [<-].
  case => //.
  + case => // sz' e1.
    case: (mk_lea_rec sz e1) => // m1 /(_ _ erefl) ih1 e2.
    case: (mk_lea_rec sz e2) => // m2 /(_ _ erefl) ih2 m /lea_add_read.
    rewrite /read_e /= !read_eE.
    by SvD.fsetdec.
  + case => // sz' e1.
    case: (mk_lea_rec sz e1) => // m1 /(_ _ erefl) ih1 e2.
    case: (mk_lea_rec sz e2) => // m2 /(_ _ erefl) ih2 m /lea_mul_read.
    rewrite /read_e /= !read_eE.
    by SvD.fsetdec.
  case => // sz' e1.
  case: (mk_lea_rec sz e1) => // m1 /(_ _ erefl) ih1 e2.
  case: (mk_lea_rec sz e2) => // m2 /(_ _ erefl) ih2 m /lea_sub_read.
  rewrite /read_e /= !read_eE.
  by SvD.fsetdec.
  Qed.

  Lemma push_cast_sz_read sz e :
    Sv.Equal (read_e (push_cast_sz sz e)) (read_e e).
  Proof.
  elim: e => //=.
  + by move=> o e1 he1; case: o => //= sz'; case: ifP.
  by move=> o e1 he1 e2 he2; case: o => //= -[] //=; 
   rewrite /read_e /= !read_eE; SvD.fsetdec.
  Qed.

  Lemma push_cast_read e :
    Sv.Equal (read_e (push_cast e)) (read_e e).
  Proof.
  elim: e => //=.
  + move=> o e1 he1; case: o => //= sz'.
    by rewrite push_cast_sz_read he1.
  by move=> o e1 he1 e2 he2; rewrite /read_e /= !read_eE; SvD.fsetdec.
  Qed.

  Lemma mk_lea_read sz e m :
    mk_lea sz e = Some m →
    Sv.Subset (read_lea m) (read_e e).
  Proof. by move=> /mk_lea_rec_read; rewrite push_cast_read. Qed.

End PROOF.
