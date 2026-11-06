From ITree Require Import ITree ITreeFacts.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import compiler_util psem psem_facts.
Require Import normalize_calls.

Section SYNTAX.

Context (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).

Lemma fresh_auxP ii X acc ty acc' x :
  fresh_aux fresh_var_ident ii X acc ty = ok (acc', x) ->
  [/\ vtype x = ty, ~ Sv.In x X, ~ Sv.In x acc & acc' = Sv.add x acc].
Proof.
  rewrite /fresh_aux; set y := {| vtype := _; vname := _ |}.
  t_xrbindP => /Sv_memP hx <- <-.
  rewrite /=; split => //; clearbody y; SvD.fsetdec.
Qed.

Lemma flag_destP lv ty x :
  flag_dest lv ty = Some x -> [/\ lv = Lvar x, vtype x = abool & ty = abool].
Proof.
  case: lv => //= y; case: andP => // -[/eqP h1 /eqP h2] [<-]; done.
Qed.

Lemma writes_flagP x lvs touts :
  writes_flag x lvs touts -> Sv.In x (vrvs lvs) /\ vtype x = abool.
Proof.
  elim: lvs touts => [|lv lvs ih] [|ty touts] //=.
  rewrite vrvs_cons => /orP [| /ih [] ?? ]; last by split => //; SvD.fsetdec.
  case h: flag_dest => [y|//] /eqP ?; subst x.
  case: (flag_destP h) => -> ?? /=; split => //; SvD.fsetdec.
Qed.

Lemma flag_varsP x lvs touts :
  Sv.In x (flag_vars lvs touts) <-> writes_flag x lvs touts.
Proof.
  elim: lvs touts => [|lv lvs ih] [|ty touts] /=; try by split => //; SvD.fsetdec.
  case: flag_dest => [y|] /=; last by rewrite ih.
  rewrite SvP.MP.Dec.F.add_iff ih; split.
  + by move=> [/eqP -> | ->]; rewrite ?orbT.
  by move=> /orP [/eqP -> | ->]; auto.
Qed.

Lemma snapshot_varsP x lvs touts :
  x \in snapshot_vars lvs touts <->
  writes_flag x lvs touts /\ read_before_write x lvs touts.
Proof.
  rewrite /snapshot_vars mem_filter -flag_varsP; split.
  + by move=> /andP [-> /Sv_elemsP].
  by move=> [/Sv_elemsP -> ->].
Qed.

Context {asm_op : Type} {asmop : asmOp asm_op}.

(* The new destinations write flags of the original ones, or variables that
   are fresh. *)
Lemma nc_dests_vrvs ii X tg r acc lvs touts acc' xs c :
  nc_dests fresh_var_ident ii X tg r acc lvs touts = ok (acc', xs, c) ->
  Sv.Subset acc acc' /\
  forall y, Sv.In y (vrvs xs) ->
    writes_flag y lvs touts \/ (~ Sv.In y X /\ ~ Sv.In y acc).
Proof.
  elim: lvs touts r acc acc' xs c => [|lv lvs ih] [|ty touts] r acc acc' xs c /=.
  1-3: by move=> [<- <- _]; split => // y; rewrite /vrvs /=; SvD.fsetdec.
  case h: flag_dest => [x|].
  + case: ifP => hw.
    + t_xrbindP => -[acc1 a] /fresh_auxP [_ ha1 ha2 ->] -[[acc2 xs2] c2] /ih [hs hy] /=.
      move=> <- <- _; split.
      1: by move: hs hy => /= hs hy; SvD.fsetdec.
      move: hy => /= hy y; rewrite vrvs_cons vrv_var => hin.
      case: (SvP.MP.Dec.F.union_1 hin) => [/SvD.F.singleton_1 <- | /hy]; first by right.
      case=> [-> | ?]; [left; apply orbT | right; SvD.fsetdec].
    t_xrbindP => -[[acc2 xs2] c2] /ih /= [hs hy] <- <- _.
    split => // y; rewrite vrvs_cons; case: (flag_destP h) => -> _ _.
    rewrite vrv_var => hin.
    case: (SvP.MP.Dec.F.union_1 hin) => [/SvD.F.singleton_1 -> | /hy].
    + by rewrite eqxx; left.
    by case=> [-> | ?]; [left; apply orbT | right].
  t_xrbindP => -[acc1 a] /fresh_auxP [_ ha1 ha2 ->] -[[acc2 xs2] c2] /ih /= [hs hy] /=.
  move=> <- <- _; split; first SvD.fsetdec.
  move=> y; rewrite vrvs_cons vrv_var => hin.
  case: (SvP.MP.Dec.F.union_1 hin) => [/SvD.F.singleton_1 <- | /hy]; first by right.
  case=> [-> | ?]; [left; done | right; SvD.fsetdec].
Qed.

Lemma nc_dests_lvars ii X tg r acc lvs touts acc' xs c :
  nc_dests fresh_var_ident ii X tg r acc lvs touts = ok (acc', xs, c) ->
  exists ys, mapM get_lvar xs = ok ys.
Proof.
  elim: lvs touts r acc acc' xs c => [|lv lvs ih] [|ty touts] r acc acc' xs c /=.
  1-3: by move=> [_ <- _]; exists [::].
  case h: flag_dest => [x|].
  + case: (flag_destP h) => ? _ _; subst lv; case: ifP => _.
    + t_xrbindP => -[acc1 a] _ -[[acc2 xs2] c2] /ih [ys hys] /= _ <- _.
      by exists (v_var a :: ys); rewrite /= hys.
    t_xrbindP => -[[acc2 xs2] c2] /ih [ys hys] /= _ <- _.
    by exists (v_var x :: ys); rewrite /= hys.
  t_xrbindP => -[acc1 a] _ -[[acc2 xs2] c2] /ih [ys hys] /= _ <- _.
  by exists (v_var a :: ys); rewrite /= hys.
Qed.

End SYNTAX.

Section PROOF.

#[local] Existing Instance progUnit.

Context
  {asm_op syscall_state : Type}
  {wa : WithAssert}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

(* A renamed expression evaluates in [t] as the original one in [s] when each
   variable it reads is read in [t] through the renaming. *)
Section RENAME.

Context {sm : SemMode}.
Context (r : Mvar.t var) (wdb : bool) (gd : glob_decls) (t s : estate) (R : Sv.t).
Hypothesis hmem : emem t = emem s.
Hypothesis hR : forall z, Sv.In z R -> (evm t).[odflt z (Mvar.get r z)] = (evm s).[z].

Let P e :=
  Sv.Subset (read_e e) R -> sem_pexpr wdb gd t (rename_e r e) = sem_pexpr wdb gd s e.

Let Q es :=
  Sv.Subset (read_es es) R ->
  sem_pexprs wdb gd t (map (rename_e r) es) = sem_pexprs wdb gd s es.

Lemma rename_gvarP x :
  Sv.Subset (read_gvar x) R ->
  get_gvar wdb gd (evm t) (rename_gvar r x) = get_gvar wdb gd (evm s) x.
Proof using hR sip wa.
  rewrite /rename_gvar /get_gvar /read_gvar; case: ifP => hl /= hsub.
  2: by rewrite hl.
  have hx : Sv.In (gv x) R by SvD.fsetdec.
  have := hR hx; rewrite /rename_var /get_var.
  by case: (Mvar.get r (gv x)) => [y|] /= ->.
Qed.

Lemma rename_e_esP : (forall e, P e) * (forall es, Q es).
Proof using hR hmem sip wa.
  apply: pexprs_ind_pair; split; subst P Q => //=.
  - move=> e he es hes; rewrite read_es_cons => hsub.
    rewrite he ?hes //; SvD.fsetdec.
  - move=> x hsub; apply rename_gvarP; rewrite /read_e /= in hsub; SvD.fsetdec.
  - move=> al aa sz x e he hsub; rewrite /read_e /= read_eE in hsub.
    rewrite rename_gvarP ?he //; rewrite /read_e; SvD.fsetdec.
  - move=> aa sz len x e he hsub; rewrite /read_e /= read_eE in hsub.
    rewrite rename_gvarP ?he //; rewrite /read_e; SvD.fsetdec.
  - by move=> al sz e he hsub; rewrite he // hmem.
  - by move=> op e he hz; rewrite he.
  - move=> op e1 he1 e2 he2 hsub; rewrite /read_e /= read_eE in hsub.
    rewrite he1 ?he2 //; rewrite /read_e; SvD.fsetdec.
  - by move=> op es hes hz; rewrite -!/(sem_pexprs _ _ _ _) hes.
  move=> ty e he e1 he1 e2 he2 hsub; rewrite /read_e /= !read_eE in hsub.
  rewrite he ?he1 ?he2 //; rewrite /read_e; SvD.fsetdec.
Qed.

End RENAME.

(* How the target reads the value that the source reads in [z]: through the
   renaming, [z] itself when it is not renamed. *)
Definition read_rel (r : Mvar.t var) (vt vs : Vm.t) (z : var) :=
  match Mvar.get r z with
  | None => vt.[z] = vs.[z]
  | Some y => vt.[y] = vs.[z] /\ vtype z = abool
  end.

Lemma read_rel_get r vt vs z :
  read_rel r vt vs z -> vt.[odflt z (Mvar.get r z)] = vs.[z].
Proof.
  by rewrite /read_rel; case: Mvar.get => [y [] |] //=.
Qed.

Lemma read_rel_eq r vt vs vt' vs' z :
  read_rel r vt vs z ->
  vt'.[odflt z (Mvar.get r z)] = vt.[odflt z (Mvar.get r z)] ->
  vs'.[z] = vs.[z] ->
  read_rel r vt' vs' z.
Proof.
  rewrite /read_rel; case: Mvar.get => [y|] /=.
  + by move=> [h hb] h1 h2; rewrite h1 h2.
  by move=> h h1 h2; rewrite h1 h2.
Qed.

Lemma write_var_rel (x y : var_i) v (t s t' : estate) :
  vtype x = vtype y ->
  write_var true x v t = ok t' ->
  exists2 s', write_var true y v s = ok s' &
    [/\ escs t' = escs t /\ emem t' = emem t, escs s' = escs s /\ emem s' = emem s,
        (evm t').[x] = (evm s').[y],
        evm s' = (evm s).[y <- v]
      & type_of_val v <> cbool -> vtype x <> abool].
Proof.
  move=> hty; rewrite /write_var /set_var; t_xrbindP.
  move=> _ hdb htr <- <-; rewrite hdb -hty htr /=; eexists; first reflexivity.
  split => //=.
  + by rewrite !Vm.setP_eq hty.
  by move=> hv hx; apply hv; move: htr; rewrite hx => /truncatable_bool.
Qed.

Lemma vrv_rename_lval r lv : vrv (rename_lval r lv) = vrv lv.
Proof.
  by case: lv.
Qed.

(* A destination copied after the instruction (not a flag, so it receives a
   value that is not a boolean) is written as the original one. *)

Lemma defer_writeP gd r lv v (t s t' : estate) :
  escs t = escs s -> emem t = emem s ->
  type_of_val v <> cbool ->
  (forall z, Sv.In z (read_rv lv) -> read_rel r (evm t) (evm s) z) ->
  write_lval true gd (rename_lval r lv) v t = ok t' ->
  exists2 s', write_lval true gd lv v s = ok s' &
    [/\ escs t' = escs s', emem t' = emem s'
      & forall y, Sv.In y (vrv lv) ->
          vtype y <> abool /\ (evm t').[y] = (evm s').[y]].
Proof using sip wa.
  move=> hscs hmem hv hr.
  have hre : forall e, Sv.Subset (read_e e) (read_rv lv) -> sem_pexpr true gd t (rename_e r e) = sem_pexpr true gd s e.
  + move=> e hsub.
    exact: ((rename_e_esP true gd hmem (fun z hz => read_rel_get (hr z hz))).1 e hsub).
  case: lv hr hre => /=.
  + move=> ?? _ _; rewrite /write_none; t_xrbindP => h1 h2 <-.
    rewrite h1 h2; eexists; first reflexivity.
    split => // y; SvD.fsetdec.
  + move=> x _ _ /(write_var_rel s erefl) [s'] -> [[h1 h2] [h3 h4] hx _ hb]; eexists; first reflexivity.
    split; [by rewrite h1 h3 | by rewrite h2 h4 | ].
    move=> y /SvD.F.add_iff [<- | ]; last SvD.fsetdec.
    by split => //; apply hb.
  + move=> al ws vi e _ hre; t_xrbindP => pe ve hve hpe w hw m hm <-.
    rewrite hre // in hve; rewrite hve /= hpe /= hw /= -hmem hm /=.
    eexists; first reflexivity.
    by split => // y; rewrite /vrv /=; SvD.fsetdec.
  (* An array cell and a sub-array are written alike. *)
  all: move=> ??? x e hr hre; apply: on_arr_varP => n a htyx hget.
  all: have hx : Sv.In x (read_e_rec (Sv.add x Sv.empty) e) by rewrite read_eE; SvD.fsetdec.
  all: have := hr x hx; rewrite /read_rel.
  all: case: Mvar.get => [y [_ hxb] | heq]; first by rewrite hxb in htyx.
  all: have hget' : get_var true (evm s) x = ok (Varr a)
         by move: hget; rewrite /get_var heq.
  all: have he : Sv.Subset (read_e e) (read_e_rec (Sv.add x Sv.empty) e)
         by rewrite read_eE; SvD.fsetdec.
  all: rewrite hget' /=; t_xrbindP => i vi hvi hi w hw a' ha' hwr.
  all: rewrite (hre _ he) in hvi; rewrite hvi /= hi /= hw /= ha' /=.
  all: case: (write_var_rel s erefl hwr) => s' -> [[h1 h2] [h3 h4] hx' _ hb].
  all: eexists; first reflexivity.
  all: split; [by rewrite h1 h3 | by rewrite h2 h4 | ].
  all: move=> y /SvD.F.add_iff [<- | ]; last SvD.fsetdec.
  all: by split => //; apply hb.
Qed.

Context (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).
Context (p' : prog) (ev : extra_val_t).

(* The invariant of the copies: [U] is the target state before the copy of
   the first destination of [lvs], [S] the source state before writing it,
   [TF] the target state after the instruction. *)
Definition nc_inv (X : Sv.t) (r : Mvar.t var) (lvs : lvals) (touts : seq atype)
  (TF U S : estate) :=
  [/\ escs U = escs S /\ emem U = emem S,
      (forall z, Sv.In z X ->
         read_before_write z lvs touts || ~~ writes_flag z lvs touts ->
         read_rel r (evm U) (evm S) z),
      (forall z y, Mvar.get r z = Some y -> writes_flag z lvs touts /\ ~ Sv.In y X),
      (forall a, ~ Sv.In a X ->
         (evm U).[a] = (evm TF).[a])
    & (forall z, writes_flag z lvs touts ->
         (evm U).[z] = (evm TF).[z])].

Lemma nc_destsP ii X tg (TF : estate) lvs touts r acc acc' xs c vs (W U S U' : estate) :
  nc_dests fresh_var_ident ii X tg r acc lvs touts = ok (acc', xs, c) ->
  Sv.Subset (vars_lvals lvs) X ->
  List.map type_of_val vs = map eval_atype touts ->
  dests_match lvs touts ->
  write_lvals true (p_globs p') W xs vs = ok TF ->
  esem p' ev c U = ok U' ->
  nc_inv X r lvs touts TF U S ->
  exists2 S', write_lvals true (p_globs p') S lvs vs = ok S' & st_eq_on X U' S'.
Proof.
  elim: lvs touts r acc acc' xs c vs W U S =>
    [|lv lvs ih] [|ty touts] r acc acc' xs c vs W U S /=.
  2,3: by move=> _ _ _ hf; exfalso; apply: notF hf.
  + move=> [_ <- <-] _; case: vs => [|//] _ _ _ [<-] [[h1 h2] h3 h4 _ _]; exists S => //.
    split => // z hz; have := h3 z hz isT; rewrite /read_rel; case h: Mvar.get => [y|] //.
    by case: (h4 _ _ h).
  move=> hnc hsub; case: vs => [|v vs] //= [htv htys] /andP [hm hms] hW hc [[h1 h2] h3 h4 h5 h6].
  have [hlv hsub'] : Sv.Subset (Sv.union (read_rv lv) (vrv lv)) X /\ Sv.Subset (vars_lvals lvs) X.
  + by move: hsub; rewrite /vars_lvals read_rvs_cons vrvs_cons; split; SvD.fsetdec.
  have hvrsX : forall y, writes_flag y lvs touts -> Sv.In y X.
  + by move=> y /writes_flagP [hy _]; move: hsub'; rewrite /vars_lvals; SvD.fsetdec.
  move: hnc; case hf: flag_dest => [x|].
  + case: (flag_destP hf) => ? hxb ?; subst lv ty.
    have hxX : Sv.In x X by move: hlv; rewrite vrv_var; SvD.fsetdec.
    case: ifP => hw.
    + t_xrbindP => -[acc1 a] /fresh_auxP [hta haX haacc ->] -[[acc2 xs2] c2] hnc /= _ ? ?; subst xs c.
      move: hW => /=; t_xrbindP => W1 hW1 hW'.
      have [|S1 hS1 [_ [hS1a hS1b] hraw hvmS1 _]] := write_var_rel (y := x) S _ hW1.
      + by rewrite hta hxb.
      rewrite hS1 /=.
      have [_ hvrs] := nc_dests_vrvs hnc.
      have haTF : (evm W1).[a] = (evm TF).[a].
      + apply: (vrvsP hW') => /hvrs [/hvrsX // | [_ /=]]; SvD.fsetdec.
      apply: (ih touts _ _ _ _ _ vs W1 U S1 hnc hsub' htys hms hW' hc).
      split.
      + by rewrite hS1a hS1b.
      + move=> z hz hpre /=; case: (v_var x =P z) => [<- | hne].
        + rewrite /read_rel Mvar.setP_eq; split => //.
          by rewrite (h5 _ haX) -haTF.
        have hne' : (v_var x == z) = false by apply/eqP.
        have hrz : read_rel r (evm U) (evm S) z.
        + by apply: h3 hz _; rewrite /= hxb /= hne'.
        have hS : (evm S1).[z] = (evm S).[z].
        + by rewrite hvmS1 Vm.setP_neq // hne'.
        have := read_rel_eq (vt' := evm U) hrz erefl hS.
        by rewrite /read_rel Mvar.setP_neq // hne'.
      + move=> z y /=; rewrite Mvar.setP; case: eqP => [<- [<-] | hne /h4] //.
        by rewrite /= hxb /= (introF eqP hne).
      + by move=> b hb; rewrite h5.
      by move=> z hz; apply h6; rewrite /= hxb /= hz orbT.
    t_xrbindP => -[[acc2 xs2] c2] hnc /= _ ? ?; subst xs c.
    move: hW => /=; t_xrbindP => W1 hW1 hW'.
    have [S1 hS1 [_ [hS1a hS1b] hraw hvmS1 _]] := write_var_rel (y := x) S erefl hW1.
    rewrite hS1 /=.
    have [_ hvrs] := nc_dests_vrvs hnc.
    have hxTF : (evm W1).[x] = (evm TF).[x].
    + by apply: (vrvsP hW') => /hvrs [ | []]; rewrite ?hw.
    apply: (ih touts _ _ _ _ _ vs W1 U S1 hnc hsub' htys hms hW' hc).
    split.
    + by rewrite hS1a hS1b.
    + move=> z hz hpre /=; case: (v_var x =P z) => [<- | hne].
      + rewrite /read_rel Mvar.removeP eqxx.
        by rewrite (h6 x) /= ?hxb /= ?eqxx // -hxTF hraw.
      have hne' : (v_var x == z) = false by apply/eqP.
      have hrz : read_rel r (evm U) (evm S) z.
      + by apply: h3 hz _; rewrite /= hxb /= hne'.
      have hS : (evm S1).[z] = (evm S).[z].
      + by rewrite hvmS1 Vm.setP_neq // hne'.
      have := read_rel_eq (vt' := evm U) hrz erefl hS.
      by rewrite /read_rel Mvar.removeP hne'.
    + move=> z y; rewrite Mvar.removeP; case: eqP => [// | hne /h4].
      by rewrite /= hxb /= (introF eqP hne).
    + by move=> b hb; rewrite h5.
    by move=> z hz; apply h6; rewrite /= hxb /= hz orbT.
  t_xrbindP => -[acc1 a] /fresh_auxP [hta haX haacc ->] -[[acc2 xs2] c2] hnc /= _ ? ?; subst xs c.
  move: hW => /=; t_xrbindP => W1 hW1 hW'.
  have [_ hvrs] := nc_dests_vrvs hnc.
  have haTF : (evm W1).[a] = (evm TF).[a].
  + apply: (vrvsP hW') => /hvrs [/hvrsX // | [_ /=]]; SvD.fsetdec.
  have hinv : forall U1 S1, escs U1 = escs S1 /\ emem U1 = emem S1 ->
    (forall z, Sv.In z X -> read_rel r (evm U) (evm S) z -> read_rel r (evm U1) (evm S1) z) ->
    (forall b, ~ Sv.In b X -> (evm U1).[b] = (evm U).[b]) ->
    (forall z, writes_flag z lvs touts -> (evm U1).[z] = (evm U).[z]) ->
    nc_inv X r lvs touts TF U1 S1.
  + move=> U1 S1 hU1 hrel hU1X hU1w; split => //.
    + move=> z hz hpre; apply: hrel hz (h3 z hz _).
      by move: hpre; rewrite /= hf; case: Sv.mem.
    + by move=> z y /h4; rewrite /= hf.
    + by move=> b hb; rewrite hU1X // h5.
    by move=> z hz; rewrite hU1w // h6 //= hf.
  have [[vi [ty' ?]] | [hnn {}hc]] : (exists vi ty', lv = Lnone vi ty') \/
    ((forall vi ty', lv <> Lnone vi ty') /\
     esem p' ev (MkI ii (Cassgn (rename_lval r lv) tg ty (Plvar a)) :: c2) U = ok U').
  + by case: (lv) hc; eauto; right.
  + subst lv; move: hm => /eqP ?; subst ty'.
    move: hW1 => /=; rewrite /write_var /set_var; t_xrbindP => vm1 hdb htr _ _.
    rewrite /= /write_none -hta htr hdb /=.
    by apply: (ih touts _ _ _ _ _ vs W1 U S hnc hsub' htys hms hW' hc); apply hinv.
  move: hc => /=; t_xrbindP => U1 hU1 hc.
  move: hU1; rewrite /sem_assgn; t_xrbindP => w0 hw0 w htr hwr.
  move: hW1 => /=; rewrite /write_var /set_var; t_xrbindP => vm1 hdb htr1 ? ?; subst vm1 W1.
  have hUa : (evm U).[a] = vm_truncate_val (eval_atype ty) v.
  + by rewrite (h5 _ haX) -haTF /= Vm.setP_eq hta.
  case: (ty =P abool) => hty.
  + move: htr; rewrite hty => /truncate_val_typeE [b _ ?]; subst w.
    case: (write_lval_bool hwr) => [[vi [ty' ]] | [y]]; case: (lv) hnn hf => //=.
    + by move=> ?? h; case: (h _ _ erefl).
    by move=> z _ + [<-] hz; rewrite hz hty.
  have hvb : type_of_val v <> cbool by rewrite htv; case: (ty) hty.
  have hdef : is_defined v by move: hdb; rewrite /DB /= (introF eqP hvb) orbF.
  have ? : w0 = v.
  + move: hw0 => /=; rewrite /get_gvar /= /get_var; t_xrbindP => _ <-.
    by rewrite hUa vm_truncate_val_eq ?hta.
  subst w0; have ? : v = w by apply: (truncate_val_subctype_eq htr); rewrite htv.
  subst w.
  have hrd : forall z, Sv.In z (read_rv lv) -> read_rel r (evm U) (evm S) z.
  + move=> z hz; apply: (h3 z); first by SvD.fsetdec.
    by rewrite /= hf (SvD.F.mem_1 hz).
  have [S1 hS1 [hsc hme hy]] := defer_writeP h1 h2 hvb hrd hwr.
  rewrite hS1 /=.
  apply: (ih touts _ _ _ _ _ vs _ U1 S1 hnc hsub' htys hms hW' hc).
  have hU1 := vrvP hwr; rewrite vrv_rename_lval in hU1.
  have hS1' := vrvP hS1.
  have hwf : forall z, writes_flag z (lv :: lvs) (ty :: touts) -> ~ Sv.In z (vrv lv).
  + by move=> z /writes_flagP [_ hb] /hy [].
  apply hinv => //.
  + move=> z hz hrz; case: (Sv_memP z (vrv lv)) => hzl.
    + have [hzb heq] := hy _ hzl.
      move: hrz; rewrite /read_rel; case h: Mvar.get => [y|] //.
      by case: (hwf z (h4 _ _ h).1).
    apply: (read_rel_eq hrz); last by rewrite hS1'.
    rewrite hU1 //; case h: Mvar.get => [y|] //=.
    by case: (h4 _ _ h) => _ hyX hyl; apply hyX; SvD.fsetdec.
  + by move=> b hb; rewrite hU1 //; SvD.fsetdec.
  by move=> z hz; rewrite hU1 //; apply hwf; rewrite /= hf.
Qed.

(* The snapshots save, in fresh variables, the flags read by a copy before
   the instruction writes them. *)
Lemma nc_snapshotsP ii X acc xs acc' m pre (t t' : estate) :
  nc_snapshots fresh_var_ident ii X acc xs = ok (acc', m, pre) ->
  (forall x, x \in xs -> Sv.In x X) ->
  esem p' ev pre t = ok t' ->
  [/\ escs t' = escs t /\ emem t' = emem t,
      Sv.Subset acc acc',
      (forall y, Sv.In y X \/ Sv.In y acc ->
         (evm t').[y] = (evm t).[y]),
      (forall x y, Mvar.get m x = Some y ->
         [/\ x \in xs, ~ Sv.In y X, Sv.In y acc' & (evm t').[y] = (evm t).[x]])
    & (forall x, x \in xs -> Mvar.get m x <> None)].
Proof.
  elim: xs acc acc' m pre t => [|x xs ih] acc acc' m pre t /=.
  + by move=> [<- <- <-] _ [<-]; split => // x y; rewrite Mvar.get0.
  t_xrbindP => -[acc1 a] /fresh_auxP [hta haX haacc ->] -[[acc2 m2] pre2] hsn /= ? ? ?; subst acc' m pre.
  move=> hxs; rewrite /= /sem_assgn; t_xrbindP => t1 w0 hw0 w htr hw1 hpre.
  have hxX : Sv.In x X by apply hxs; rewrite inE eqxx.
  have [[hsc hme] hsub hraw hm hdom] :=
    ih _ _ _ _ _ hsn (fun z hz => hxs z (introT orP (or_intror hz))) hpre.
  move: hw0 => /=; rewrite /get_gvar /=; move=> hw0.
  have ? := truncate_val_subctype_eq htr (type_of_get_var hw0); subst w.
  move: hw0; rewrite /get_var; t_xrbindP => hdef ?; subst w0.
  move: hw1 => /=; rewrite /write_var /set_var; t_xrbindP => vm1 _ _ ? ?; subst vm1 t1.
  have hax : v_var a <> x by move=> h; apply haX; rewrite h.
  move: hsub hraw hm => /= hsub hraw hm.
  split.
  + by rewrite hsc hme.
  + by move: hsub; clear; SvD.fsetdec.
  + move=> y hy.
    have hy' : Sv.In y X \/ Sv.In y (Sv.add a acc) by case: hy => ?; [left | right; SvD.fsetdec].
    rewrite (hraw _ hy') /= Vm.setP_neq //; apply/eqP => h; subst y.
    by case: hy.
  + move=> x0 y; rewrite Mvar.setP; case: eqP => [<- [<-] | hne /hm [h1 h2 h3 h4]].
    + split => //; first by rewrite inE eqxx.
      + by move: hsub; clear; SvD.fsetdec.
      have ha : Sv.In a X \/ Sv.In a (Sv.add a acc) by right; SvD.fsetdec.
      rewrite (hraw _ ha) /= Vm.setP_eq compat_val_vm_truncate_val //.
      by rewrite hta; apply Vm.getP.
    split => //; first by rewrite inE h1 orbT.
    rewrite h4 /= Vm.setP_neq //.
    by apply/eqP => ?; subst x0; apply haX; apply hxs; rewrite inE h1 orbT.
  move=> x0; rewrite inE Mvar.setP eq_sym; case: eqP => // _ /= h; exact: hdom h.
Qed.

Lemma nc_inv_init ii X tg lvs touts r acc acc' xs c vs (W S TF : estate) :
  nc_dests fresh_var_ident ii X tg r acc lvs touts = ok (acc', xs, c) ->
  Sv.Subset (vars_lvals lvs) X ->
  escs W = escs S /\ emem W = emem S ->
  (forall z, Sv.In z X ->
     (evm W).[z] = (evm S).[z]) ->
  (forall z y, Mvar.get r z = Some y ->
     [/\ writes_flag z lvs touts, ~ Sv.In y X, Sv.In y acc & (evm W).[y] = (evm S).[z]]) ->
  (forall z, writes_flag z lvs touts -> read_before_write z lvs touts ->
     Mvar.get r z <> None) ->
  write_lvals true (p_globs p') W xs vs = ok TF ->
  nc_inv X r lvs touts TF TF S.
Proof using wa.
  move=> hnc hsub [hsc hme] hX hr hdom hW.
  have [_ hvrs] := nc_dests_vrvs hnc.
  have [ys hys] := nc_dests_lvars hnc.
  have hsc' := write_lvals_escs hW; have hme' := write_lvals_emem hys hW.
  have hTF := vrvsP hW.
  have hwX : forall z, writes_flag z lvs touts -> Sv.In z X.
  + by move=> z /writes_flagP [hz _]; move: hsub; rewrite /vars_lvals; SvD.fsetdec.
  split => //.
  + by rewrite hsc' hme'.
  + move=> z hz hpre; rewrite /read_rel; case h: Mvar.get => [y|].
    + have [hw hyX hyacc hy] := hr _ _ h.
      split; last by case: (writes_flagP hw).
      rewrite -hy hTF //.
      by move=> /hvrs [/hwX | []].
    have hz' : ~ Sv.In z (vrvs xs).
    + move=> /hvrs [hw | [hzX _]]; last by apply hzX.
      have hrbw : read_before_write z lvs touts by move: hpre; rewrite hw orbF.
      by case: (hdom _ hw hrbw h).
    by rewrite -(hTF _ hz'); apply hX.
  by move=> z y /hr [].
Qed.

Context (p : prog).
Hypothesis Hp : normalize_calls_prog fresh_var_ident p = ok p'.

Lemma normalize_calls_fd_inv f f' :
  normalize_calls_fd fresh_var_ident p f = ok f' ->
  [/\ f_info f = f_info f', f_contract f = f_contract f', f_tyin f = f_tyin f',
      f_params f = f_params f', f_tyout f = f_tyout f', f_res f = f_res f'
    & f_extra f = f_extra f'].
Proof. by rewrite /normalize_calls_fd; t_xrbindP => ?? <-. Qed.

Lemma normalize_calls_prog_inv :
  [/\ map_cfprog (normalize_calls_fd fresh_var_ident p) (p_funcs p) = ok (p_funcs p'),
      p_globs p' = p_globs p
    & p_extra p' = p_extra p].
Proof using Hp. by apply: rbindP Hp => ?? [<-]. Qed.

Lemma eq_globs : p_globs p' = p_globs p.
Proof using Hp. by case: normalize_calls_prog_inv. Qed.

Lemma normalize_calls_get_fundef fn :
  if get_fundef (p_funcs p) fn is Some fd then
    exists2 fd', normalize_calls_fd fresh_var_ident p fd = ok fd'
               & get_fundef (p_funcs p') fn = Some fd'
  else get_fundef (p_funcs p') fn = None.
Proof using Hp.
  apply: get_map_cfprog_name_gen_aux.
  by case: normalize_calls_prog_inv => H _ _; exact H.
Qed.

Lemma normalize_calls_sem_pre fn fs :
  sem_pre p' fn fs = ok tt -> sem_pre p fn fs = ok tt.
Proof using Hp.
  rewrite /sem_pre eq_globs.
  move: (normalize_calls_get_fundef fn).
  case: get_fundef => [fd [fd' H1 ->]| -> //].
  by case: (normalize_calls_fd_inv H1) => _ -> ->.
Qed.

Lemma normalize_calls_sem_post fn vs fr :
  sem_post p' fn vs fr = ok tt -> sem_post p fn vs fr = ok tt.
Proof using Hp.
  rewrite /sem_post eq_globs.
  move: (normalize_calls_get_fundef fn).
  case: get_fundef => [fd [fd' H1 ->]| -> //].
  by case: (normalize_calls_fd_inv H1) => _ -> ->.
Qed.

(* The results of a call have the types of the outputs of the callee. *)
Definition results_typed (fn : funname) (fr : fstate) :=
  forall fd, get_fundef (p_funcs p) fn = Some fd ->
    List.map type_of_val (fvals fr) = map eval_atype (f_tyout fd).

Definition nc_spec : EquivSpec :=
  {| rpreF_ := fun fn1 fn2 fs1 fs2 => fn1 = fn2 /\ fs1 = fs2
   ; rpostF_ := fun fn1 fn2 fs1 fs2 fr1 fr2 => fr1 = fr2 /\ results_typed fn2 fr2 |}.

#[local] Lemma checker_st_eq_onP' : Checker_eq p' p checker_st_eq_on.
Proof using Hp. by apply checker_st_eq_onP; rewrite eq_globs. Qed.
#[local] Lemma checker_a_st_eq_onP' : Checker_a_eq p' p checker_a_st_eq_on.
Proof using Hp. by apply checker_a_st_eq_onP; rewrite eq_globs. Qed.

#[local] Hint Resolve checker_st_eq_onP' checker_a_st_eq_onP' : core.

(* The rewriting of the destinations of an instruction: [t0] and [s] are the
   states before the instruction, [W] and [S] the states in which its outputs
   are written. *)
Lemma normalize_destsP ii X acc tg multi lvs touts acc' pre xs post vs
  (t0 s t W S TF U' : estate) :
  normalize_dests fresh_var_ident ii X acc tg multi lvs touts = ok (acc', pre, xs, post) ->
  Sv.Subset (vars_lvals lvs) X ->
  List.map type_of_val vs = map eval_atype touts ->
  st_eq_on X t0 s ->
  esem p' ev pre t0 = ok t ->
  escs W = escs S /\ emem W = emem S -> evm W = evm t -> evm S = evm s ->
  write_lvals true (p_globs p) W xs vs = ok TF ->
  esem p' ev post TF = ok U' ->
  exists2 S', write_lvals true (p_globs p) S lvs vs = ok S' & st_eq_on X U' S'.
Proof using Hp.
  move=> hnd hsub htys [h1 h2 h3] hpre [hW1 hW2] hWt hSs hW hpost.
  move: hnd; rewrite /normalize_dests; case: ifP => hneed.
  + t_xrbindP => -[[acc1 r] pre1] hsn -[[acc2 xs2] post2] hnc /= ????; subst acc' pre xs post.
    have hxs : forall x, x \in snapshot_vars lvs touts -> Sv.In x X.
    + move=> x /snapshot_varsP [/writes_flagP [hx _] _].
      by move: hsub; rewrite /vars_lvals; SvD.fsetdec.
    have [_ _ hraw hr hdom] := nc_snapshotsP hsn hxs hpre.
    rewrite -eq_globs in hW *.
    apply: (nc_destsP hnc hsub htys _ hW hpost).
    + by case/andP: hneed.
    apply: (nc_inv_init hnc hsub (conj hW1 hW2) _ _ _ hW).
    + by move=> z hz; rewrite hWt hSs hraw; [apply h3 | left].
    + move=> z y /= /hr [hz hyX hyacc hy].
      have [hw _] := (snapshot_varsP z lvs touts).1 hz.
      split => //; rewrite hWt hSs hy.
      by apply: h3; apply: hxs.
    by move=> /= z hw hrbw; apply hdom; apply/snapshot_varsP.
  move=> [????]; subst acc' pre xs post.
  move: hpre hpost => [?] [?]; subst t U'.
  have hWS : evm W =[X] evm S by rewrite hWt hSs.
  have [|vm2 hS' heq] := write_lvals_eq_on _ hW hWS.
  + by move: hsub; rewrite /vars_lvals; SvD.fsetdec.
  have hWS' : with_vm W (evm S) = S.
  + by move: hW1 hW2; clear; case: W S => ??? [???] /= <- <-.
  rewrite hWS' in hS'.
  exists (with_vm TF vm2) => //; split => //=.
  by apply: eq_onI heq; SvD.fsetdec.
Qed.

Lemma nc_snapshots_basic ii X acc xs acc' m pre :
  nc_snapshots fresh_var_ident ii X acc xs = ok (acc', m, pre) -> all basic_i pre.
Proof.
  elim: xs acc acc' m pre => [|x xs ih] acc acc' m pre /=; first by move=> [_ _ <-].
  by t_xrbindP => -[acc1 a] _ -[[acc2 m2] pre2] /ih hb _ _ <-.
Qed.

Lemma nc_dests_basic ii X tg r acc lvs touts acc' xs c :
  nc_dests fresh_var_ident ii X tg r acc lvs touts = ok (acc', xs, c) -> all basic_i c.
Proof.
  elim: lvs touts r acc acc' xs c => [|lv lvs ih] [|ty touts] r acc acc' xs c /=.
  1-3: by move=> [_ _ <-].
  case: flag_dest => [x|].
  + case: ifP => _.
    + by t_xrbindP => -[acc1 a] _ -[[acc2 xs2] c2] /ih hb _ _ <-.
    by t_xrbindP => -[[acc2 xs2] c2] /ih hb _ _ <-.
  t_xrbindP => -[acc1 a] _ -[[acc2 xs2] c2] /ih hb _ _ <-.
  by case: (lv).
Qed.

Lemma normalize_dests_basic ii X acc tg multi lvs touts acc' pre xs post :
  normalize_dests fresh_var_ident ii X acc tg multi lvs touts = ok (acc', pre, xs, post) ->
  all basic_i pre /\ all basic_i post.
Proof.
  rewrite /normalize_dests; case: ifP => _; last by move=> [_ <- _ <-].
  t_xrbindP => -[[acc1 r] pre1] /nc_snapshots_basic hb1 -[[acc2 xs2] post2].
  by move=> /nc_dests_basic hb2 _ <- _ <-.
Qed.

Lemma normalize_dests_pre ii X acc tg multi lvs touts acc' pre xs post (t0 s t : estate) :
  normalize_dests fresh_var_ident ii X acc tg multi lvs touts = ok (acc', pre, xs, post) ->
  Sv.Subset (vars_lvals lvs) X ->
  st_eq_on X t0 s -> esem p' ev pre t0 = ok t -> st_eq_on X t s.
Proof.
  rewrite /normalize_dests; case: ifP => _; last by move=> [_ <- _ _] _ ? [<-].
  t_xrbindP => -[[acc1 r] pre1] hsn -[[acc2 xs2] post2] _ _ <- _ _ hsub [h1 h2 h3] hpre.
  have hxs : forall x, x \in snapshot_vars lvs touts -> Sv.In x X.
  + move=> x /snapshot_varsP [/writes_flagP [hx _] _].
    by move: hsub; rewrite /vars_lvals; SvD.fsetdec.
  have [[hsc hme] _ hraw _ _] := nc_snapshotsP hsn hxs hpre.
  split; [by rewrite hsc | by rewrite hme | ].
  by move=> z hz; rewrite hraw; [apply h3 | left].
Qed.

Context {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Lemma nc_call X ii xs1 xs2 f es c1 (R Q : rel_c) :
  all basic_i c1 ->
  Sv.Subset (read_es es) X ->
  (forall t s, R t s -> st_eq_on X t s) ->
  (forall fr t s t', R t s -> results_typed f fr ->
     (Let t1 := upd_estate true (p_globs p') xs1 fr t in esem p' ev c1 t1) = ok t' ->
     exists2 s', upd_estate true (p_globs p) xs2 fr s = ok s' & Q t' s') ->
  wequiv_rec p' p ev ev nc_spec R
    (MkI ii (Ccall xs1 f es) :: c1) [:: MkI ii (Ccall xs2 f es)] Q.
Proof using Hp.
  move=> hb hes hR hpost' t s hRts.
  have [h1 h2 h3] := hR _ _ hRts.
  rewrite /isem_cmd_ /= bind_ret_r.
  rewrite bind_bind /isem_pexprs eq_globs.
  have hes' : evm t =[read_es es] evm s by apply: eq_onI h3.
  rewrite (eq_on_sem_pexprs (s := t) (s' := s) _ _ h2 hes').
  case: sem_pexprs => [vs | e].
  2: rewrite /iresult bind_throw; apply xrutt.xrutt_CutL => //.
  2: by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  rewrite !bind_ret_l bind_bind /isem_pre.
  have hfs : mk_fstate vs t = mk_fstate vs s by rewrite /mk_fstate h1 h2.
  rewrite hfs.
  case hpre: (sem_pre p' f (mk_fstate vs s)) => [[] | e].
  2: rewrite /iresult bind_throw; apply xrutt.xrutt_CutL => //.
  2: by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  rewrite (normalize_calls_sem_pre hpre) !bind_ret_l bind_bind.
  apply xrutt_facts.xrutt_bind with (rpostF (eS := nc_spec) f f (mk_fstate vs s) (mk_fstate vs s)).
  + by apply (wequiv_fun_rec (p1 := p') (p2 := p) (ev1 := ev) (ev2 := ev)).
  move=> fr _ [<- htyped] /=; rewrite /isem_post.
  case hpost: (sem_post p' f vs fr) => [[] | e].
  2: rewrite bind_bind /iresult bind_throw; apply xrutt.xrutt_CutL => //.
  2: by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  rewrite (normalize_calls_sem_post hpost) !bind_ret_l.
  have hpo := hpost' fr t s; rewrite eq_globs in hpo.
  case hup: upd_estate => [t1 | e].
  2: rewrite /iresult bind_throw; apply xrutt.xrutt_CutL => //.
  2: by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
  rewrite bind_ret_l -/(isem_cmd_ p' ev c1 t1).
  rewrite hup /= in hpo.
  destruct (esem p' ev c1 t1) as [t' | e] eqn:hc1.
  + have [s' -> hQ] := hpo t' hRts htyped erefl.
    by rewrite (esem_i_bodyP (sem_F := sem_fun_rec _) hc1); apply xrutt.xrutt_Ret.
  rewrite (esem_basic_errorP hb hc1) /iresult; apply xrutt.xrutt_CutL => //.
  by rewrite /core_logics.errcutoff /is_error /Subevent.subevent /CategoryOps.resum /fromErr mid12.
Qed.

Let Pi (i : instr) :=
  forall X acc acc' c', Sv.Subset (vars_I i) X ->
  normalize_calls_i fresh_var_ident p X acc i = ok (acc', c') ->
  wequiv_rec p' p ev ev nc_spec (st_eq_on X) c' [:: i] (st_eq_on X).

Let Pi_r (ir : instr_r) := forall ii, Pi (MkI ii ir).

Let Pc (c : cmd) :=
  forall X acc acc' c', Sv.Subset (vars_c c) X ->
  normalize_calls_c (normalize_calls_i fresh_var_ident p X) acc c = ok (acc', c') ->
  wequiv_rec p' p ev ev nc_spec (st_eq_on X) c' c (st_eq_on X).

(* The snapshots on the target side only. *)
Lemma nc_pre X pre :
  all basic_i pre ->
  wequiv_rec p' p ev ev nc_spec (st_eq_on X) pre [::]
    (fun t s => exists2 t0, st_eq_on X t0 s & esem p' ev pre t0 = ok t).
Proof.
  move=> hb; apply wequiv_basic_esem => // t0 s t h hpre.
  by exists s => //; exists t0.
Qed.

Lemma normalize_calls_body : forall c, Pc c.
Proof using Hp.
  apply (cmd_rect (Pr := Pi_r) (Pi := Pi)).
  + done.
  + by move=> X acc acc' c' _ [_ <-]; apply wequiv_nil.
  + move=> i c Hi Hc X acc acc' c' hsub /=.
    t_xrbindP => -[acc1 ci] hci -[acc2 cc] hcc _ <-.
    rewrite vars_c_cons in hsub.
    rewrite -cat1s; apply wequiv_cat with (st_eq_on X).
    + by apply: (Hi _ _ _ _ _ hci); SvD.fsetdec.
    by apply: (Hc _ _ _ _ _ hcc); SvD.fsetdec.
  { move=> x tg ty e ii X acc acc' c' hsub [_ <-].
    rewrite vars_I_assgn /vars_lval in hsub.
    apply wequiv_assgn_rel_eq with checker_st_eq_on X => //.
    all: by split; try done; rewrite /read_es /read_rvs /=; SvD.fsetdec. }
  { move=> xs tg o es ii X acc acc' c' hsub /=.
    rewrite /normalize_dests_i; t_xrbindP => -[[[acc1 pre] xs'] post] hnd _ <-.
    rewrite vars_I_opn in hsub.
    have hsubl : Sv.Subset (vars_lvals xs) X by SvD.fsetdec.
    have hses : Sv.Subset (read_es es) X by SvD.fsetdec.
    have [hb1 hb2] := normalize_dests_basic hnd.
    rewrite -[[:: MkI ii (Copn xs tg o es)]]cat0s.
    apply wequiv_cat with (fun t s => exists2 t0, st_eq_on X t0 s & esem p' ev pre t0 = ok t).
    + by apply nc_pre.
    apply wequiv_basic_esem; first by rewrite /= hb2.
    move=> t s U' [t0 hts0 hpre].
    have [h1 h2 h3] := normalize_dests_pre hnd hsubl hts0 hpre.
    rewrite esem_cons /= /sem_sopn; t_xrbindP => TF vs ves hves hvs hW hpost.
    have hves' : sem_pexprs true (p_globs p) s es = ok ves.
    + rewrite -eq_globs -hves; symmetry; apply: eq_on_sem_pexprs => //.
      by apply: eq_onI h3.
    rewrite eq_globs in hW.
    have [S' hS' heq] :=
      normalize_destsP hnd hsubl (sopn_toutP hvs) hts0 hpre (conj h1 h2) erefl erefl hW hpost.
    by exists S' => //; rewrite hves' /= hvs /= hS'. }
  { move=> xs o es ii X acc acc' c' hsub /=.
    rewrite /normalize_dests_i; t_xrbindP => -[[[acc1 pre] xs'] post] hnd _ <-.
    rewrite vars_I_syscall in hsub.
    have hsubl : Sv.Subset (vars_lvals xs) X by SvD.fsetdec.
    have [hb1 hb2] := normalize_dests_basic hnd.
    rewrite -[[:: MkI ii (Csyscall xs o es)]]cat0s.
    apply wequiv_cat with (fun t s => exists2 t0, st_eq_on X t0 s & esem p' ev pre t0 = ok t).
    + by apply nc_pre.
    apply wequiv_basic_esem; first by rewrite /= hb2.
    move=> t s U' [t0 hts0 hpre].
    have [h1 h2 h3] := normalize_dests_pre hnd hsubl hts0 hpre.
    rewrite esem_cons /= /sem_syscall; t_xrbindP => TF ves hves fs hfs hW hpost.
    have hves' : sem_pexprs true (p_globs p) s es = ok ves.
    + rewrite -eq_globs -hves; symmetry; apply: eq_on_sem_pexprs => //.
      by apply: eq_onI h3; SvD.fsetdec.
    have hfs' : mk_fstate ves t = mk_fstate ves s by rewrite /mk_fstate h1 h2.
    have [_ htys] := syscall_u_toutP hfs.
    move: hW; rewrite /upd_estate eq_globs => hW.
    have [S' hS' heq] := normalize_destsP hnd hsubl htys hts0 hpre
      (W := with_scs (with_mem t (fmem fs)) (fscs fs))
      (S := with_scs (with_mem s (fmem fs)) (fscs fs)) (conj erefl erefl) erefl erefl hW hpost.
    by exists S' => //; rewrite hves' /= -hfs' hfs /= /upd_estate hS'. }
  { move=> a ii X acc acc' c' hsub [_ <-].
    rewrite vars_I_assert in hsub.
    eapply wequiv_assert_rel_eq with checker_a_st_eq_on => //.
    by split; try done; SvD.fsetdec. }
  { move=> e c1 c2 Hc1 Hc2 ii X acc acc' c' hsub /=.
    t_xrbindP => -[acc1 c1'] hc1 -[acc2 c2'] hc2 _ <-.
    rewrite vars_I_if in hsub.
    apply wequiv_if_rel_eq with checker_st_eq_on X X X => //.
    + by split; try done; SvD.fsetdec.
    + by apply: (Hc1 _ _ _ _ _ hc1); SvD.fsetdec.
    by apply: (Hc2 _ _ _ _ _ hc2); SvD.fsetdec. }
  { move=> v dir lo hi c Hc ii X acc acc' c' hsub /=.
    t_xrbindP => -[acc1 c1'] hc _ <-.
    rewrite vars_I_for in hsub.
    apply wequiv_for_rel_eq with checker_st_eq_on X X => //.
    + by split => //; rewrite /read_es /= read_eE; SvD.fsetdec.
    + by split; try done; SvD.fsetdec.
    by apply: (Hc _ _ _ _ _ hc); SvD.fsetdec. }
  { move=> a c e info c' Hc Hc' ii X acc acc' c'' hsub /=.
    t_xrbindP => -[acc1 c1'] hc -[acc2 c2'] hc' _ <-.
    rewrite vars_I_while in hsub.
    apply wequiv_while_rel_eq with checker_st_eq_on X => //.
    + by split; try done; SvD.fsetdec.
    + by apply: (Hc _ _ _ _ _ hc); SvD.fsetdec.
    by apply: (Hc' _ _ _ _ _ hc'); SvD.fsetdec. }
  move=> xs f es ii X acc acc' c' hsub /=.
  rewrite /normalize_dests_i; t_xrbindP => fd /o2rP hfd -[[[acc1 pre] xs'] post] hnd _ <-.
  rewrite vars_I_call in hsub.
  have hsubl : Sv.Subset (vars_lvals xs) X by SvD.fsetdec.
  have [hb1 hb2] := normalize_dests_basic hnd.
  rewrite -[[:: MkI ii (Ccall xs f es)]]cat0s.
  apply wequiv_cat with (fun t s => exists2 t0, st_eq_on X t0 s & esem p' ev pre t0 = ok t).
  + by apply nc_pre.
  apply (nc_call (X := X)) => //.
  + by SvD.fsetdec.
  + by move=> t s [t0 hts0 hpre]; apply: normalize_dests_pre hnd hsubl hts0 hpre.
  move=> fr t s U' [t0 hts0 hpre] htyped; t_xrbindP => TF hW hpost.
  move: hW; rewrite /upd_estate eq_globs => hW.
  have [S' hS' heq] := normalize_destsP hnd hsubl (htyped _ hfd) hts0 hpre
    (W := with_scs (with_mem t (fmem fr)) (fscs fr))
    (S := with_scs (with_mem s (fmem fr)) (fscs fr)) (conj erefl erefl) erefl erefl hW hpost.
  by exists S'.
Qed.

Lemma normalize_calls_finalize fn fd fd' fs :
  get_fundef (p_funcs p) fn = Some fd ->
  normalize_calls_fd fresh_var_ident p fd = ok fd' ->
  wrequiv (st_eq_on (vars_fd fd)) (finalize_funcall fd') (finalize_funcall fd)
    (rpostF (eS := nc_spec) fn fn fs fs).
Proof using spp.
  move=> hget hfd; rewrite /finalize_funcall.
  case: (normalize_calls_fd_inv hfd) => _ _ _ _ <- <- <- t s fr [h1 h2 h3].
  t_xrbindP => vs hvs vs' htr <-.
  move: hvs; rewrite -(sem_pexprs_get_var _ [::]) => hvs.
  rewrite (eq_on_sem_pexprs (~~ direct_call) [::] h2 (eq_onI _ h3)) in hvs.
  2: by rewrite vars_l_read_es /vars_fd; SvD.fsetdec.
  rewrite sem_pexprs_get_var in hvs.
  rewrite hvs /= htr /= h1 h2; eexists; first reflexivity.
  split => // fd0; rewrite hget => -[<-].
  exact: mapM2_truncate_val_has_type htr.
Qed.

Lemma normalize_calls_nc fn :
  wiequiv_f p' p ev ev (rpreF (eS := nc_spec)) fn fn (rpostF (eS := nc_spec)).
Proof using Hp.
  apply wequiv_fun_ind_wa => {}fn fn' fsi fs [<- <-] fd' H.
  move: (normalize_calls_get_fundef fn); case hget: get_fundef => [fd|]; last by rewrite H.
  move=> [fd'_ Hfd Hfn]; move: Hfn; rewrite H => -[?]; subst fd'_.
  exists fd; first done.
  move=> Hsem; split; first by apply: normalize_calls_sem_pre.
  move=> si hinit; exists si.
  + move: hinit; rewrite /initialize_funcall.
    case: (normalize_calls_fd_inv Hfd) => _ _ <- <- _ _ <-.
    by case: normalize_calls_prog_inv => _ _ ->.
  exists (st_eq_on (vars_fd fd)), (st_eq_on (vars_fd fd)); split.
  + done.
  + move: Hfd; rewrite /normalize_calls_fd; t_xrbindP => -[acc c] hc <-.
    by apply: normalize_calls_body hc; rewrite /vars_fd; SvD.fsetdec.
  + exact: normalize_calls_finalize hget Hfd.
  by move=> fr1 fr2 [-> _]; apply normalize_calls_sem_post.
Qed.

Lemma normalize_calls_l fn :
  wiequiv_f p' p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using Hp.
  move=> fs1 fs2 hpre; have := normalize_calls_nc hpre.
  apply xrutt_facts.xrutt_weaken => //.
  by move=> > [].
Qed.

End PROOF.
