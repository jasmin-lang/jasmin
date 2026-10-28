(* * Correctness of the pass assert_facts.

   The pass removes from the assertions the conjuncts that an assertion
   evaluated earlier on every path establishes, nothing it reads having
   changed since; the rest of the code is unchanged. A removed conjunct holds
   where it is, on the same state.

   The relation [wiequiv_f] only constrains the runs of its first program that
   do not fail: the statement is that of the direction needed, from the
   transformed program to the source. The two runs go through the same
   states; the invariant is that the facts computed by the pass hold in the
   current state and that the bytes of the memory readable at the start of
   the function are still readable, which keeps the [Pis_mem_init] facts
   across writes to the memory and calls. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype word_ssrZ.
Require Import seq_extra compiler_util psem psem_facts.
Require Import assert_facts.
Import Lia.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

(* ------------------------------------------------------------------------- *)
(* The facts computed by the pass                                             *)

Section SYNTAX.

Context {asm_op : Type} {asmop : asmOp asm_op}.

Definition fstep (acc : seq eassert * seq eassert) c :=
  let: (fs, keep) := acc in
  if has (implies^~ c) fs then acc else (c :: fs, rcons keep c).

Lemma fassertE fs a : fassert fs a = foldl fstep (fs, [::]) (conjuncts a).
Proof. by []. Qed.

Lemma fstep_keep cs acc c : List.In c acc.2 -> List.In c (foldl fstep acc cs).2.
Proof.
  elim: cs acc => //= c' cs hrec [fs kp] hc; apply hrec.
  rewrite /fstep; case: ifP => _ //=.
  by rewrite -cats1; apply List.in_or_app; left.
Qed.

Lemma fstep_sub cs acc c : List.In c (foldl fstep acc cs).2 -> List.In c acc.2 \/ List.In c cs.
Proof.
  elim: cs acc => /= [ | c' cs hrec] [fs kp] /=; first by left.
  move=> /hrec [ | ]; last by auto.
  rewrite /fstep; case: ifP => _ /=; first by auto.
  by rewrite -cats1 => /List.in_app_iff [ | [ | []]]; auto.
Qed.

Lemma fstep_mono cs acc f : List.In f acc.1 -> List.In f (foldl fstep acc cs).1.
Proof.
  elim: cs acc => //= c cs hrec [fs kp] hf; apply hrec.
  by rewrite /fstep; case: ifP => _ //=; right.
Qed.

Lemma fassert_sub fs a c : List.In c (fassert fs a).2 -> List.In c (conjuncts a).
Proof. by rewrite fassertE => /fstep_sub [[] | ]. Qed.

(* The facts that [fkill] keeps. *)
Definition alive (xs : Sv.t) (mem : bool) (f : eassert) :=
  Sv.is_empty (Sv.inter (read_eassert f) xs) && ~~ (mem && load_mem f).

Lemma In_fkill fs xs mem f : List.In f (fkill fs xs mem) <-> List.In f fs /\ alive xs mem f.
Proof. exact: In_filter. Qed.

Lemma fkill_incl fs xs (mem : bool) : forall f, List.In f (fkill fs xs mem) -> List.In f fs.
Proof. by move=> f /In_fkill []. Qed.

Lemma aliveP xs mem f :
  alive xs mem f <-> Sv.Empty (Sv.inter (read_eassert f) xs) /\ (mem -> ~~ load_mem f).
Proof.
  rewrite /alive; split.
  + by move=> /andP [/Sv.is_empty_spec h]; case: mem.
  by move=> [/Sv.is_empty_spec -> h]; case: mem h => // ->.
Qed.

Lemma alive_sub xs (mem : bool) xs' (mem' : bool) f :
  alive xs mem f -> Sv.Subset xs' xs -> (mem' -> mem) -> alive xs' mem' f.
Proof.
  move=> /aliveP [h1 h2] hsub hm; apply/aliveP; split; last by move=> /hm /h2.
  by clear -h1 hsub; SvD.fsetdec.
Qed.

(* A fact that nothing in [c] can change is still a fact after [c]. *)
Lemma facts_c_mono c fs f :
  List.In f fs -> alive (write_c c) (has write_mem_i c) f ->
  List.In f (facts_c facts_i fs c).1.
Proof.
  set Pi := fun i => forall fs f, List.In f fs -> alive (write_I i) (write_mem_i i) f -> List.In f (facts_i fs i).1.
  set Pr := fun i => forall ii, Pi (MkI ii i).
  set Pc := fun c => forall fs f, List.In f fs -> alive (write_c c) (has write_mem_i c) f -> List.In f (facts_c facts_i fs c).1.
  move: fs f; apply (cmd_rect (Pr := Pr) (Pi := Pi) (Pc := Pc)) => //.
  + move=> i c0 hi hc fs f hf /= ha.
    have h1 : List.In f (facts_i fs i).1.
    + apply: hi hf (alive_sub ha _ _); last by move=> ->.
      by rewrite write_c_cons; SvD.fsetdec.
    case: facts_i h1 => fs1 ci /= h1.
    have /(_ (alive_sub ha _ _)) := hc fs1 f h1.
    case: facts_c => fs2 c2 /= h2; apply h2; last by move=> ->; rewrite orbT.
    by rewrite write_c_cons; SvD.fsetdec.
  + by move=> x tg ty e ii fs f hf /= ha; apply/In_fkill; split.
  + by move=> xs t o es ii fs f hf /= ha; apply/In_fkill; split.
  + by move=> xs o es ii fs f hf /= ha; apply/In_fkill; split.
  + move=> [lbl a] ii fs f hf /= ha.
    have := @fstep_mono (conjuncts a) (fs, [::]) f hf; rewrite -fassertE.
    by case: fassert.
  + move=> e c1 c2 hc1 hc2 ii fs f hf /= ha.
    have h1 : List.In f (facts_c facts_i fs c1).1.
    + apply: hc1 hf (alive_sub ha _ _); last by move=> ->.
      by rewrite write_Ii write_i_if; SvD.fsetdec.
    have h2 : List.In f (facts_c facts_i fs c2).1.
    + apply: hc2 hf (alive_sub ha _ _); last by move=> ->; rewrite orbT.
      by rewrite write_Ii write_i_if; SvD.fsetdec.
    case: facts_c h1 => fs1 c1' /= h1; case: facts_c h2 => fs2 c2' /= h2.
    by apply/In_filter; split => //; apply: In_has h2 (eq_eassert_refl f).
  + move=> x dir lo hi c0 hc ii fs f hf /= ha.
    case: facts_c => _ c' /=; apply/In_fkill; split => //; apply: alive_sub ha _ _ => //.
    by rewrite write_Ii write_i_for; SvD.fsetdec.
  + move=> al c1 e info c2 hc1 hc2 ii fs f hf /= ha.
    have hw : Sv.Subset (Sv.union (write_c c1) (write_c c2)) (write_I (MkI ii (Cwhile al c1 e info c2))).
    + by rewrite write_Ii write_i_while; SvD.fsetdec.
    have h0 := proj2 (In_fkill _ _ _ _) (conj hf (alive_sub ha hw (fun h => h))).
    have h1 : List.In f (facts_c facts_i (fkill fs (Sv.union (write_c c1) (write_c c2)) (has write_mem_i c1 || has write_mem_i c2)) c1).1.
    + apply: hc1 h0 (alive_sub ha _ _); last by move=> ->.
      by rewrite write_Ii write_i_while; SvD.fsetdec.
    by case: facts_c h1 => fs1 c1' /= h1; case: facts_c.
  by move=> xs fn es ii fs f hf /= ha; apply/In_fkill; split.
Qed.

End SYNTAX.

(* ------------------------------------------------------------------------- *)
(* The facts hold                                                             *)

Section HOLDS.

Context
  {wsw : WithSubWord} {syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} (gd : glob_decls).

Definition holds (s : estate) (a : eassert) := sem_eassert gd s a = ok true.

Lemma holds1 s a : holds s a <-> forall c, List.In c [:: a] -> holds s c.
Proof. by split => [h c [<- | []] | h]; [ | apply h; left]. Qed.

Lemma holds_and s a1 a2 : holds s (Pand a1 a2) <-> holds s a1 /\ holds s a2.
Proof.
  rewrite /holds /=; split; last by move=> [-> ->].
  by t_xrbindP => b1 -> b2 -> /= /andP [-> ->].
Qed.

Lemma holds_app s l1 l2 :
  (forall c, List.In c (l1 ++ l2) -> holds s c) <->
  (forall c, List.In c l1 -> holds s c) /\ (forall c, List.In c l2 -> holds s c).
Proof.
  by split => [h | [h1 h2] c /List.in_app_iff []]; [split => c hc; apply h; apply/List.in_app_iff; auto | apply h1 | apply h2].
Qed.

(* An assertion holds when all its conjuncts do. *)
Lemma conj_pexprP s e :
  holds s (Pexpr e) <-> forall c, List.In c (conj_pexpr e) -> holds s c.
Proof.
  elim/pexpr_ind: e; try by intros; apply holds1.
  move=> op e1 h1 e2 h2; case: op; try by intros; apply holds1.
  rewrite /= -/(conj_pexpr e1) -/(conj_pexpr e2) holds_app -h1 -h2 /holds /=.
  split.
  + t_xrbindP => v v1 -> v2 -> /=; rewrite /sem_sop2 /=.
    t_xrbindP => b1 /to_boolI -> b2 /to_boolI -> <- /=.
    by case: b1; case: b2.
  move=> [].
  by t_xrbindP => v1 -> /to_boolI -> v2 -> /to_boolI -> /=.
Qed.

Lemma conjunctsP s a :
  holds s a <-> forall c, List.In c (conjuncts a) -> holds s c.
Proof.
  elim: a => /=; try by intros; apply holds1.
  + by move=> e; apply conj_pexprP.
  by move=> a1 h1 a2 h2; rewrite holds_and h1 h2 holds_app.
Qed.

Lemma mk_andP s k ks :
  holds s (mk_and k ks) <-> forall c, List.In c (k :: ks) -> holds s c.
Proof.
  elim: ks k => [ | k' ks hrec] k /=; first by apply holds1.
  rewrite holds_and hrec /=.
  by split => [[hk h] c [<- // | hc] | h]; [apply h | split => [ | c hc]; apply h; auto].
Qed.

Lemma impliesP s f c : implies f c -> holds s f -> holds s c.
Proof.
  rewrite /implies /holds => /orP [/(eq_eassertP gd s) <- // | ].
  case: f => // -[] // len [] // m [] // [] // lo [] // [] // n [] //.
  case: c => // -[] // len' [] // m' [] // [] // lo' [] // [] // n' [] //=.
  move=> /and3P [/eqP <- /(eq_exprP (sm := total) true gd s) <- hr].
  rewrite /sem_opN_safety /=; t_xrbindP => _ v -> <- /=; t_xrbindP => t -> /= hall.
  congr ok; apply/allP => i; rewrite in_ziota => hi; apply (allP hall); rewrite in_ziota.
  by move: hr hi; rewrite !zify; lia.
Qed.

(* The readable bytes of [m] are readable in [m']. *)
Definition readable_incl (m m' : mem) := forall al p ws, validr m al p ws -> validr m' al p ws.

(* An assertion that does not load from the memory still holds when the
   variables it reads are unchanged and the readable bytes remain readable. *)
Lemma holds_readable s s' a :
  evm s =[read_eassert a] evm s' -> readable_incl (emem s) (emem s') -> ~~ load_mem a ->
  holds s a -> holds s' a.
Proof.
  move=> heq hr; rewrite /holds (eq_on_sem_eassert (s' := with_vm s (evm s')) gd _ heq) //.
  have : evm (with_vm s (evm s')) = evm s' by [].
  change (readable_incl (emem (with_vm s (evm s'))) (emem s')) in hr.
  move: (with_vm s (evm s')) hr => {heq} s1 hr hvm.
  have he e : ~~ use_mem e ->
    sem_pexpr (sm := total) true gd s1 e = sem_pexpr (sm := total) true gd s' e.
  + exact: use_memP.
  have hes es : ~~ has use_mem es ->
    mapM (sem_pexpr (sm := total) true gd s1) es = mapM (sem_pexpr (sm := total) true gd s') es.
  + by elim: es => //= e es ih; rewrite negb_or => /andP [] /he -> /ih ->.
  elim: a => /=.
  + by move=> e /he ->.
  + by move=> op es /hes ->.
  + by move=> x _; rewrite hvm.
  + move=> e1 e2; rewrite negb_or => /andP [] /he -> /he ->; t_xrbindP.
    move=> lo ? -> /= -> sz ? -> /= -> /= /allP h.
    by congr ok; apply/allP => i /h /hr.
  move=> a1 h1 a2 h2; rewrite negb_or => /andP [] /h1 {}h1 /h2 {}h2; t_xrbindP => b1 hb1 b2 hb2.
  by case: b1 hb1 => // /h1 -> /=; case: b2 hb2 => // /h2 ->.
Qed.

Definition fholds s (fs : seq eassert) := forall f, List.In f fs -> holds s f.

Lemma fstep_sound s cs acc :
  fholds s acc.1 -> fholds s (foldl fstep acc cs).2 ->
  fholds s (foldl fstep acc cs).1 /\ fholds s cs.
Proof.
  elim: cs acc => /= [ | c cs hrec] [fs kp] /= hfs hkp; first by split => // ? [].
  case: ifP hkp => [/(all_has (all_predT _)) [f hf himp] | _] hkp.
  + have [h1 h2] := hrec (fs, kp) hfs hkp.
    split => // c' [<- | /h2 //].
    exact: (impliesP himp (hfs _ hf)).
  have hc : holds s c.
  + apply hkp; apply fstep_keep => /=.
    by rewrite -cats1; apply List.in_or_app; right; left.
  have [ | h1 h2] := hrec (c :: fs, rcons kp c) _ hkp.
  + by move=> f /= [<- // | /hfs].
  by split => // c' /= [<- // | /h2].
Qed.

End HOLDS.

Section KILL.

Context
  {wsw : WithSubWord} {syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} (gd : glob_decls).

Lemma fholds_incl s fs fs' : (forall f, List.In f fs' -> List.In f fs) -> fholds gd s fs -> fholds gd s fs'.
Proof. by move=> hin h f /hin /h. Qed.

Lemma fassert_sound s fs a :
  fholds gd s fs -> fholds gd s (fassert fs a).2 -> fholds gd s (fassert fs a).1 /\ holds gd s a.
Proof.
  rewrite fassertE => hfs hkp.
  have [h1 h2] := @fstep_sound _ _ _ _ gd s (conjuncts a) (fs, [::]) hfs hkp.
  by split => //; apply/conjunctsP.
Qed.

Lemma fholds_kill s s' fs xs (mem : bool) :
  fholds gd s fs -> evm s =[\ xs] evm s' -> (~~ mem -> emem s = emem s') ->
  readable_incl (emem s) (emem s') -> fholds gd s' (fkill fs xs mem).
Proof.
  move=> hfs heq hm hr f /In_fkill [/hfs hf /aliveP [hdisj hmem]].
  have hon : evm s =[read_eassert f] evm s'.
  + move=> x hx; apply heq.
    by move=> hxs; apply: (hdisj x); SvD.fsetdec.
  case hu: (load_mem f); last by apply: holds_readable hon hr _ hf; rewrite hu.
  rewrite /holds -(eq_on_sem_eassert gd _ hon) //; apply hm.
  by apply/negP => /hmem; rewrite hu.
Qed.

Lemma fholds_join_l s fs1 fs2 : fholds gd s fs1 -> fholds gd s (fjoin fs1 fs2).
Proof. by move=> h f /In_filter [/h]. Qed.

Lemma fholds_join_r s fs1 fs2 : fholds gd s fs2 -> fholds gd s (fjoin fs1 fs2).
Proof.
  move=> h f /In_filter [_ /(all_has (all_predT _)) [g /h hg heq]].
  by rewrite /holds (eq_eassertP gd s heq).
Qed.

End KILL.

(* ------------------------------------------------------------------------- *)
(* The two programs                                                           *)

Section PROOF.

Context
  {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state} {sm : SemMode}
  {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

#[local] Existing Instance withassert_nocontract.

Context (p : uprog) (ev : extra_val_t).

Notation p' := (assert_facts_prog p).

(* The calls run on the same arguments and return the same results; the
   bytes readable before a call are readable after it. *)
Definition rd_spec : EquivSpec := {|
  rpreF_ := fun (fn1 fn2 : funname) (fs1 fs2 : fstate) => fn1 = fn2 /\ fs1 = fs2;
  rpostF_ := fun (fn1 fn2 : funname) (fs1 fs2 fr1 fr2 : fstate) =>
    fr1 = fr2 /\ readable_incl (fmem fs1) (fmem fr1) |}.

(* Both programs are in the same state, where the facts hold and the bytes
   readable in [m], the memory at the start of the function, are readable. *)
Definition Rf (m : mem) (fs : seq eassert) (s t : estate) :=
  [/\ s = t, fholds (p_globs p) s fs & readable_incl m (emem s)].

Lemma facts_assgn m fs x tg ty e ii :
  wequiv_rec p' p ev ev rd_spec (Rf m fs) [:: MkI ii (Cassgn x tg ty e)] [:: MkI ii (Cassgn x tg ty e)]
    (Rf m (fkill fs (vrv x) (lv_write_mem x))).
Proof.
  apply wequiv_assgn_eq.
  + by move=> s _ v [<- _ _] ->; exists v.
  move=> v s _ s' [<- hfs hm] hw; exists s' => //; split => //.
  + apply: (fholds_kill hfs (vrvP hw)); first by move=> h; apply: lv_write_memP h hw.
    by move=> al q ws; apply: write_lval_validr hw.
  by move=> al q ws /hm; apply: write_lval_validr hw.
Qed.

Lemma facts_opn m fs xs tg o es ii :
  wequiv_rec p' p ev ev rd_spec (Rf m fs) [:: MkI ii (Copn xs tg o es)] [:: MkI ii (Copn xs tg o es)]
    (Rf m (fkill fs (vrvs xs) (has lv_write_mem xs))).
Proof.
  apply wequiv_opn_eq.
  + exact: same_mode_refl.
  + by move=> s _ v [<- _ _] ->; exists v.
  move=> vs s _ s' [<- hfs hm] hw; exists s' => //; split => //.
  + apply: (fholds_kill hfs (vrvsP hw)); first by move=> h; apply: write_lvals_memP h hw.
    by move=> al q ws; apply: write_lvals_validr hw.
  by move=> al q ws /hm; apply: write_lvals_validr hw.
Qed.

(* After a call or a system call whose final memory keeps the readable bytes
   readable. *)
Lemma Rf_upd_estate m fs wdb gd xs fr s s' :
  Rf m fs s s -> readable_incl (emem s) (fmem fr) -> upd_estate wdb gd xs fr s = ok s' ->
  Rf m (fkill fs (vrvs xs) true) s' s'.
Proof.
  move=> [_ hfs hm] hr hw.
  have hr' : readable_incl (emem s) (emem s') by move=> al q ws /hr; apply: write_lvals_validr hw.
  split => //; last by move=> al q ws /hm /hr'.
  exact: (fholds_kill hfs (vrvsP hw)).
Qed.

Lemma facts_syscall m fs xs o es ii :
  wequiv_rec p' p ev ev rd_spec (Rf m fs) [:: MkI ii (Csyscall xs o es)] [:: MkI ii (Csyscall xs o es)]
    (Rf m (fkill fs (vrvs xs) true)).
Proof.
  apply wequiv_syscall_esem => s _ s1 [<- hfs hm].
  rewrite esem1 /= /sem_syscall; t_xrbindP => vs hvs fr hfr hw.
  exists s1; first by rewrite hvs /= hfr /= hw.
  apply: Rf_upd_estate hw; first by split.
  by have [<- _] := syscall_u_toutP hfr.
Qed.

Lemma facts_call m fs xs fn es ii :
  wequiv_rec p' p ev ev rd_spec (Rf m fs) [:: MkI ii (Ccall xs fn es)] [:: MkI ii (Ccall xs fn es)]
    (Rf m (fkill fs (vrvs xs) true)).
Proof.
  apply wequiv_call_core_wa with (Pf := rpreF (eS := rd_spec)) (Qf := rpostF (eS := rd_spec)) (Rv := eq).
  + by move=> s _ v [<- _ _] ->; exists v.
  + by [].
  + by move=> s _ vs _ [<- _ _] <-.
  + exact: (@wequiv_fun_rec _ _ _ _ _ _ _ _ _ _ p' p ev ev rd_spec ii ii fn fn).
  + by move=> fs1 fs2 fr1 fr2 _ _; rewrite /sem_post.
  move=> fs1 _ fr _ [_ <-] [<- hr] s _ s' [[<- hfs hm] _ _ hmem _ _] hw; exists s' => //.
  by apply: Rf_upd_estate hw; [split | rewrite hmem].
Qed.

Lemma facts_assert m fs a ii :
  let: (fs', c') := facts_i fs (MkI ii (Cassert a)) in
  wequiv_rec p' p ev ev rd_spec (Rf m fs) c' [:: MkI ii (Cassert a)] (Rf m fs').
Proof.
  case: a => lbl a /=.
  have hsub := @fassert_sub fs a.
  have hsound : forall s, fholds (p_globs p) s fs -> fholds (p_globs p) s (fassert fs a).2 ->
    fholds (p_globs p) s (fassert fs a).1 /\ holds (p_globs p) s a.
  + by move=> s; apply fassert_sound.
  case: fassert hsub hsound => fs' [ | k ks] /= hsub hsound.
  + apply wequiv_assert_right => s _ [<- hfs hm].
    have [hfs' ha] := hsound s hfs (fun _ (h : List.In _ [::]) => match h with end).
    by rewrite /sem_assert /= ha.
  case: ifP => _; apply wequiv_assert => _; split => // s _ [<- hfs hm] /= ha.
  + have hk : fholds (p_globs p) s (k :: ks) by move=> c /hsub; apply (proj1 (conjunctsP _ _ _) ha).
    by have [? _] := hsound s hfs hk.
  have hk : fholds (p_globs p) s (k :: ks) by apply/mk_andP.
  by have [? ?] := hsound s hfs hk.
Qed.

Let Pi (i : instr) := forall m fs,
  wequiv_rec p' p ev ev rd_spec (Rf m fs) (facts_i fs i).2 [:: i] (Rf m (facts_i fs i).1).

Let Pi_r (i : instr_r) := forall ii, Pi (MkI ii i).

Let Pc (c : cmd) := forall m fs,
  wequiv_rec p' p ev ev rd_spec (Rf m fs) (facts_c facts_i fs c).2 c (Rf m (facts_c facts_i fs c).1).

Lemma facts_cP c : Pc c.
Proof.
  apply (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => //.
  + by move=> m fs; apply wequiv_nil.
  + move=> i c0 hi hc m fs /=.
    have := hi m fs; case: facts_i => fs1 ci /= hi'.
    have := hc m fs1; case: facts_c => fs2 c2 /= hc'.
    rewrite -(cat1s i c0).
    exact: (wequiv_cat hi' hc').
  + by move=> x tg ty e ii m fs; apply facts_assgn.
  + by move=> xs tg o es ii m fs; apply facts_opn.
  + by move=> xs o es ii m fs; apply facts_syscall.
  + by move=> a ii m fs; have := facts_assert m fs a ii; case: facts_i.
  + move=> e c1 c2 hc1 hc2 ii m fs /=.
    have := hc1 m fs; case: facts_c => fs1 c1' /= hc1'.
    have := hc2 m fs; case: facts_c => fs2 c2' /= hc2'.
    apply wequiv_if_eq; first by move=> s _ v [<- _ _] ->; exists v.
    case.
    + eapply wequiv_weaken; last exact hc1'.
      + by [].
      by move=> s t [-> h hm]; split => //; apply fholds_join_l.
    eapply wequiv_weaken; last exact hc2'.
    + by [].
    by move=> s t [-> h hm]; split => //; apply fholds_join_r.
  + move=> x dir lo hi c0 hc ii m fs /=.
    set fs0 := fkill _ _ _.
    have hin : forall f, List.In f fs0 -> List.In f (facts_c facts_i fs0 c0).1.
    + move=> f hf; have /In_fkill [_ ha] := hf; apply: facts_c_mono hf (alive_sub ha _ _) => //.
      by SvD.fsetdec.
    have := hc m fs0; case: facts_c hin => fs1 c0' /= hin hc'.
    apply wequiv_for_eq with (Rf m fs0).
    + by move=> s t [-> h hm]; split => //; apply: fholds_incl h; apply fkill_incl.
    + by move=> s _ v [<- _ _] ->; exists v.
    + move=> i s _ s' [<- hfs hm] hw; exists s' => //.
      have hmem := write_var_memP hw.
      have hr : readable_incl (emem s) (emem s') by rewrite -hmem.
      split => //; last by rewrite -hmem.
      have := fholds_kill (mem := false) hfs (vrvP_var hw) (fun _ => hmem) hr.
      apply fholds_incl => f hf; apply/In_fkill; split => //.
      have /In_fkill [_ ha] := hf; apply: alive_sub ha _ _ => //; SvD.fsetdec.
    eapply wequiv_weaken; last exact hc'.
    + by [].
    by move=> s t [-> h hm]; split => //; apply: fholds_incl h.
  + move=> al c1 e info c2 hc1 hc2 ii m fs /=.
    set fs0 := fkill _ _ _.
    have hin1 : forall f, List.In f fs0 -> List.In f (facts_c facts_i fs0 c1).1.
    + move=> f hf; have /In_fkill [_ ha] := hf; apply: facts_c_mono hf (alive_sub ha _ _); last by move=> ->.
      by SvD.fsetdec.
    have := hc1 m fs0; case: facts_c hin1 => fs1 c1' /= hin1 hc1'.
    have hin2 : forall f, List.In f fs0 -> List.In f (facts_c facts_i fs1 c2).1.
    + move=> f hf; have /In_fkill [_ ha] := hf; apply: facts_c_mono (hin1 _ hf) (alive_sub ha _ _); last by move=> ->; rewrite orbT.
      by SvD.fsetdec.
    have := hc2 m fs1; case: facts_c hin2 => fs2 c2' /= hin2 hc2'.
    eapply wequiv_weaken with (P2 := Rf m fs0) (Q2 := Rf m fs1); last apply wequiv_while_eq.
    + by move=> s t [-> h hm]; split => //; apply: fholds_incl h; apply fkill_incl.
    + by [].
    + by move=> s _ v [<- _ _] ->; exists v.
    + exact hc1'.
    eapply wequiv_weaken; last exact hc2'.
    + by [].
    by move=> s t [-> h hm]; split => //; apply: fholds_incl h.
  by move=> xs fn es ii m fs; apply facts_call.
Qed.

Lemma assert_facts_tgt_src_aux fn :
  wiequiv_f p' p ev ev (rpreF (eS := rd_spec)) fn fn (rpostF (eS := rd_spec)).
Proof.
  apply wequiv_fun_ind_wa => {}fn _ fs _ [<- <-] fd.
  rewrite get_map_prog; case: get_fundef => // fd0 [<-]; exists fd0 => //.
  move=> _; split => // s hinit; exists s => //.
  exists (Rf (fmem fs) [::]), (Rf (fmem fs) (facts_c facts_i [::] (f_body fd0)).1); split => //.
  + move: hinit; rewrite /initialize_funcall; t_xrbindP => ? _ s0 [<-] /write_vars_memP /= hm.
    by split => //; rewrite hm.
  + exact: facts_cP.
  move=> s1 _ fr [<- _ hm] h; exists fr => //; split => //.
  by move: h; rewrite /finalize_funcall; t_xrbindP => ???? <-.
Qed.

End PROOF.

(* When the transformed program runs without failure, in the mode
   [total_init] (the pass runs after [explicit_init]) with its assertions
   evaluated, the source runs with the same results. *)
Lemma assert_facts_tgt_src :
  forall {asm_op syscall_state : Type} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (p : prog) (ev : extra_val_t),
  forall fn,
  wiequiv_f (sm1 := total_init) (sm2 := total_init)
    (wa1 := withassert_nocontract) (wa2 := withassert_nocontract)
    (assert_facts_prog p) p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof.
  move=> asm_op syscall_state ep spp sip E E0 wE rE p ev fn.
  eapply wkequiv_io_weaken; last exact: (assert_facts_tgt_src_aux (sm := total_init) p ev (fn := fn)).
  1-3: by [].
  by move=> > _ [].
Qed.
