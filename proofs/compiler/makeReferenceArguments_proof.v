(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
Require Import Uint63.
Require Import psem compiler_util.
Require Export makeReferenceArguments.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Section SemInversion.

Context
  {wsw : WithSubWord}
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  (pT : progT)
  (cs : semCallParams)
  (p : prog)
  (ev : extra_val_t).

Lemma sem_nilI s1 s2 (P : estate -> estate -> Prop) :
  P s2 s2 -> sem p ev s1 [::] s2 -> P s1 s2.
Proof. by move=> ? /semE <-. Qed.

Lemma sem_consI s1 i c s2 (P : estate -> instr -> cmd -> estate -> Prop) :
  (forall s3, sem_I p ev s1 i s3 -> sem p ev s3 c s2 -> P s1 i c s2) ->
  sem p ev s1 (i::c) s2 -> P s1 i c s2.
Proof. by move=> h /semE [s3 [] /h]. Qed.

Section SemInversionSeq1.
  Context (s1 : estate) (i : instr) (s2 : estate).
  Context
    (P : estate -> instr -> estate -> Prop).

  Hypothesis Hi :
    (sem_I p ev s1 i s2 -> P s1 i s2).

  Lemma sem_seq1I : sem p ev s1 [:: i] s2 → P s1 i s2.
  Proof.
    elim/sem_consI=> s hs h_nil.
    by elim/sem_nilI: h_nil hs => /Hi.
  Qed.
End SemInversionSeq1.
End SemInversion.

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {eparams : EstateParams syscall_state}
  {spparams : SemPexprParams}
  {siparams : SemInstrParams asm_op syscall_state}
  (fresh_id : instr_info → int → string → stype → Ident.ident).

#[local] Existing Instance indirect_c.

  Lemma make_referenceprog_globs (p p' : uprog) :
    makereference_prog fresh_id p = ok p' ->
      p.(p_globs) = p'.(p_globs).
  Proof.
    case: p p' => [???] [???]; t_xrbindP.
    by rewrite /makereference_prog; t_xrbindP.
  Qed.

  Section MakeEpilogueInd.
  Variable P : int → seq (bool * string * stype) -> lvals -> seq pseudo_instr -> Prop.
  Variable (ii : instr_info) (X:Sv.t).

  Hypothesis P0 : ∀ ctr, P ctr [::] [::] [::].

  Hypothesis PSNone :
    forall (ctr:int) b x ty xftys lv lvs args,
         is_reg_ptr_lval fresh_id b ii ctr x ty lv = None
      -> make_pseudo_epilogue fresh_id ii X ctr xftys lvs = ok args
      -> P ctr xftys lvs args
      -> P ctr ((b,x,ty) :: xftys) (lv :: lvs) (PI_lv lv :: args).

  Hypothesis PSSome :
    forall ctr b x ty xftys lv lvs (y : var_i) args,
       ~~Sv.mem y X
    -> is_reg_ptr_lval fresh_id b ii ctr x ty lv = Some y
    -> make_pseudo_epilogue fresh_id ii X (Uint63.succ ctr) xftys lvs = ok args
    -> P (Uint63.succ ctr) xftys lvs args
    -> P ctr ((b, x, ty) :: xftys) (lv :: lvs) (PI_lv (Lvar y) :: (PI_i lv ty y) :: args).

  Lemma make_pseudo_epilogueW ctr xftys lvs args :
       make_pseudo_epilogue fresh_id ii X ctr xftys lvs = ok args
    -> P ctr xftys lvs args.
  Proof.
  elim: xftys lvs args ctr.
  + by move=> [] //= ?? [<-]; apply P0.
  move=> [[b x] ty] xfty ih [] //= lv lvs args ctr.
  case E: is_reg_ptr_lval; last first.
  + by t_xrbindP => ?? <-; apply/PSNone/ih.
  by t_xrbindP => ??? <-; apply/PSSome/ih.
  Qed.

  End MakeEpilogueInd.

  Context (p p' : uprog).
  Let ev : unit := tt.

  Hypothesis Hp : makereference_prog fresh_id p = ok p'.

  Inductive sem_pis ii : estate -> seq pseudo_instr -> values -> estate -> Prop :=
   | SPI_nil : forall s, sem_pis ii s [::] [::] s
   | SPI_lv  : forall s1 s2 s3 lv pis v vs,
     write_lval true (p_globs p') lv v s1 = ok s2 ->
     sem_pis ii s2 pis vs s3 ->
     sem_pis ii s1 (PI_lv lv :: pis) (v::vs) s3
   | SPI_i : forall s1 s2 s3 lv ty y pis vs,
     sem_I p' ev s1 (mk_ep_i ii lv ty y) s2 ->
     sem_pis ii s2 pis vs s3 ->
     sem_pis ii s1 (PI_i lv ty y :: pis) vs s3.

  Lemma sem_pisE ii s1 pis vs s3 :
    sem_pis ii s1 pis vs s3 →
    match pis with
    | [::] => vs = [::] ∧ s3 = s1
    | PI_lv lv :: pis' =>
        ∃ v vs' s2,
        [/\ vs = v ::vs', write_lval true (p_globs p') lv v s1 = ok s2 & sem_pis ii s2 pis' vs' s3 ]
    | PI_i lv ty y :: pis' =>
        exists2 s2, sem_I p' ev s1 (mk_ep_i ii lv ty y) s2 & sem_pis ii s2 pis' vs s3
    end.
  Proof.
    case => {s1 pis vs s3}.
    - by [].
    - by move => s1 s2 s3 lv pis v vs ok_s2 rec; exists v, vs, s2.
    by move => s1 s2 s3 lv ty y pis vs h h'; exists s2.
  Qed.

  Lemma eq_globs : p_globs p = p_globs p'.
  Proof.
   case : p Hp => /= p_funcs p_globs extra.
   rewrite /makereference_prog.
   t_xrbindP => /=.
   by move => y _ <-.
  Qed.

  Lemma is_reg_ptr_lval_ty b ii ctr x ty lv y:
     is_reg_ptr_lval fresh_id b ii ctr x ty lv = Some y -> vtype y = ty.
  Proof. by case: lv => //= [? | _ _ _ ? _]; case: ifP => // _ [<-]. Qed.

  Lemma make_pseudo_codeP ii X ctr xtys lvs pis s1 s2 vm1 vs vst:
    make_pseudo_epilogue fresh_id ii X ctr xtys lvs = ok pis ->
    mapM2 ErrType dc_truncate_val (map snd xtys) vs = ok vst ->
    Sv.Subset (Sv.union (read_rvs lvs) (vrvs lvs)) X ->
    write_lvals true (p_globs p) s1 lvs vst = ok s2 ->
    evm s1 =[X] vm1 ->
    exists2 vm2,sem_pis ii (with_vm s1 vm1) pis vst (with_vm s2 vm2) & evm s2 =[X] vm2.
  Proof.
    move=> h; elim /make_pseudo_epilogueW : h s1 vm1 vs vst => {ctr xtys lvs pis}.
    + by move=> _ s1 vm1 [] // _ [] <- _ [<-] ?; exists vm1 => //; constructor.
    + move=> ctr b x ty xtys lv lvs pis hnone _ ih s1 vm1 [ //| v vs] vst' /=.
      t_xrbindP => vt ht vst hts <- {vst'}.
      rewrite read_rvs_cons vrvs_cons => leX /=.
      t_xrbindP => s1' hw hws eqvm.
      have [|vm1' hw' eqvm']:= write_lval_eq_on _ hw eqvm; first by SvD.fsetdec.
      case: (ih _ vm1' _ _ hts _ hws _).
      - by SvD.fsetdec.
      - by apply: eq_onI eqvm'; SvD.fsetdec.
      move=> vm2' ih1 ih2; exists vm2' => //.
      econstructor; eauto.
      by rewrite -eq_globs.
    move=> ctr b x ty xtys lv lvs y pis /Sv_memP hyX hsome _ ih s1 vm1 [ //| v vs] vst' /=.
    t_xrbindP => vt ht vst hts <- {vst'}.
    rewrite read_rvs_cons vrvs_cons => leX /=.
    t_xrbindP => s1' hw hws eqvm.
    have ? := is_reg_ptr_lval_ty hsome; subst ty.
    have [vmy [hw' eqvmy semy]]: exists vmy,
      [/\ write_lval true (p_globs p') y vt (with_vm s1 vm1) = ok (with_vm s1 vmy),
          evm s1 =[X] vmy &
          sem_pexpr true (p_globs p') (with_vm s1 vmy) (Plvar y) = ok vt].
    + have heqt := truncate_val_has_type ht.
      rewrite /= (write_var_eq_type heqt (truncate_val_DB true ht)).
      eexists; split; first reflexivity.
      move=> z hz; rewrite Vm.setP_neq; first by apply eqvm.
      + by apply/eqP => ?;subst z;SvD.fsetdec.
      assert (htr := truncatable_type_of true vt).
      move: htr; rewrite heqt => htr.
      by rewrite /get_gvar /= get_var_eq //= (truncate_val_defined ht) (vm_truncate_val_eq heqt).
    set I := mk_ep_i ii lv (vtype y) y.
    have [vm1' semI eqvm1']:
     exists2 vm1', sem_I p' ev (with_vm s1 vmy) I (with_vm s1' vm1') & evm s1' =[X]  vm1'.
    + have [ | vm1' hwvm1 eqvm1' ]:= write_lval_eq_on (X:=X) _ hw eqvmy;first by SvD.fsetdec.
      exists vm1'; last by apply: eq_onI eqvm1'; SvD.fsetdec.
      constructor; apply Eassgn with vt vt => //.
      - by apply: truncate_val_idem ht.
      by rewrite -eq_globs.
    have [|vm2 sem2 eqvm2]:= ih s1' vm1' vs vst hts _ hws eqvm1'; first by SvD.fsetdec.
    exists vm2 => //; econstructor; eauto; econstructor; eauto.
  Qed.

  Lemma swapableP ii pis lvs vs c s1 s2:
    swapable ii pis = ok (lvs, c) ->
    sem_pis ii s1 pis vs s2 ->
    exists s1' vm2,
      [/\ write_lvals true (p_globs p') s1 lvs vs = ok s1',
          sem p' ev s1' c (with_vm s2 vm2) & (evm s2 =1 vm2)%vm].
  Proof.
    elim: pis lvs c vs s1 => /= [ | pi pis ih] lvs' c' vs s1.
    + case/ok_inj => <- <-{lvs' c'} /sem_pisE[] -> <- {vs s1}.
      exists s2, (evm s2); split => //.
      by rewrite with_vm_same; constructor.
    case: pi => [lv | lv ty y] /=; t_xrbindP => -[] lvs c /ih{ih}ih.
    + move=> [??] h; subst lvs' c'.
      case/sem_pisE: h => v [] vs' [] s2' [] ? H H0; subst.
      have [s1' [vm2 [hws hsem]]] := ih _ _ H0.
      by exists s1', vm2 ; split => //=; rewrite H.
    t_xrbindP => /Sv.is_empty_spec.
    rewrite /mk_ep_i /= /write_I /read_I /= -/vrv -/read_rv -Sv.is_empty_spec.
    move=> hrw hwr wflv ?? h; subst c' lvs'.
    case/sem_pisE: h => s3 /sem_IE/sem_iE[] v [] v' [] H ok_v' H3 H0.
    have [s1' [vm2 [hws hsem heqvm]]]:= ih _ _ H0.
    have heqr := eq_onS (disjoint_eq_on hrw H3).
    have nwm_pi : ~~ lv_write_mem lv by case: (lv) wflv.
    have heqm  := lv_write_memP nwm_pi H3.
    have heqs  := lv_write_scsP H3.
    have [{nwm_pi} vm3 hw3 hvm3] := write_lvals_eq_on (@SvP.MP.subset_refl _) hws heqr.
    have hy : sem_pexpr true (p_globs p') (with_vm s1' vm3) (Plvar y) = ok v.
    + rewrite -H; rewrite /=; apply: (get_gvar_eq_on _ _ (@SvP.MP.subset_refl _)).
      rewrite /read_gvar /= => y' /SvD.F.singleton_iff ?; subst y'.
      have := (disjoint_eq_ons (s:= Sv.singleton y) _ hw3).
      rewrite !evm_with_vm => <- //; last by SvD.fsetdec.
      apply/Sv.is_empty_spec; move/Sv.is_empty_spec: hwr.
      by rewrite /read_I_rec /write_I_rec /= read_rvE /read_gvar /=; SvD.fsetdec.
    have heqnw: evm s1' =[\ Sv.union (vrv lv) (vrvs lvs)] vm3.
    + move=> x hx; have /= <- := vrvsP hw3; last by SvD.fsetdec.
      rewrite -(vrvsP hws); last by SvD.fsetdec.
      by rewrite -(vrvP H3) //; SvD.fsetdec.
    have [vmi [hsemi heqv]]: exists vmi, write_lval true (p_globs p') lv v' (with_vm s1' vm3) = ok (with_vm s1' vmi) /\ (evm s1' =1 vmi)%vm.
    + move: H3; rewrite /write_lval.
      move /Sv.is_empty_spec: hwr; move /Sv.is_empty_spec: hrw.
      rewrite /read_I_rec /write_I_rec [X in (Sv.inter (vrvs _) X)]/= /read_gvar
        [X in (Sv.inter (vrvs _) X)]/= read_rvE.
      case: lv wflv heqnw => //=.
      + move=> x _ heqnw hrw hwr /write_var_spec -/(_ (with_vm s1' vm3)) [vmi] [-> hvmx hx].
        exists vmi; rewrite with_vm_idem; split => //.
        move=> z; case: ((v_var x) =P z) => hxz.
        + by subst z;rewrite hx; have -> //:= vrvsP hws; SvD.fsetdec.
        rewrite -hvmx; last by SvD.fsetdec.
        rewrite evm_with_vm.
        by case (Sv_memP z (vrvs lvs)) => hz; [apply hvm3 | apply heqnw]; SvD.fsetdec.
      move=> aa ws sc x e hnoload heqnw hrw hwr.
      apply: on_arr_varP => sz t htyx hget.
      rewrite /write_var.
      t_xrbindP=>  zi vi he hvi t1 -> t1' hsub vms3 hset ?; subst s3; rewrite /on_arr_var.
      rewrite (@get_var_eq_on _ _ (Sv.singleton x) (evm s1)); first last.
      + by move=> z hz; have := vrvsP hw3; rewrite !evm_with_vm => -> //; SvD.fsetdec.
      + by SvD.fsetdec.
      rewrite hget /=.
      rewrite -(use_memP_eq_on _ _ (s1:= s1) hnoload) ?he; last first.
      + rewrite evm_with_vm; rewrite /with_vm /= in hw3 => z hz.
        by have /= -> // := vrvsP hw3; move: hwr; rewrite read_eE; SvD.fsetdec.
      rewrite /= hvi /= hsub /=.
      have [vmi [-> hvmi hx]]:= set_var_spec vm3 hset; exists vmi; split => //.
      move=> z; case: ((v_var x) =P z) => hxz.
      + by subst z; rewrite hx; have /= -> // := vrvsP hws; SvD.fsetdec.
      rewrite -hvmi; last by SvD.fsetdec.
      by case (Sv_memP z (vrvs lvs)) => hz; [apply hvm3 | apply heqnw]; SvD.fsetdec.
    set I := (MkI _ _).
    have hsemI : sem_I p' ev (with_vm s1' vm3) I (with_vm s1' vmi) by constructor; econstructor; eauto.
    have [vm4 ]:= sem_vm_eq hsem heqv.
    rewrite with_vm_idem => {hsem}hsem heqvm4.
    exists (with_vm s1' vm3), vm4; split.
    + by have -> // : s1 = (with_vm s3 (evm s1)); rewrite /with_vm -heqm -heqs; case: (s1).
    + by econstructor;eauto.
    by move=> x; rewrite (heqvm x) // (heqvm4 x).
  Qed.

  Let Pi s1 (i:instr) s2:=
    forall (X:Sv.t) c', update_i fresh_id p X i = ok c' ->
     Sv.Subset (Sv.union (read_I i) (write_I i)) X ->
     forall vm1, evm s1 =[X] vm1 ->
     exists2 vm2, evm s2 =[X] vm2 & sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2).

  Let Pi_r s1 (i:instr_r) s2 :=
    forall ii, Pi s1 (MkI ii i) s2.

  Let Pc s1 (c:cmd) s2:=
    forall (X:Sv.t) c', update_c (update_i fresh_id p X) c = ok c' ->
     Sv.Subset (Sv.union (read_c c) (write_c c)) X ->
     forall vm1, evm s1 =[X] vm1 ->
     exists2 vm2, evm s2 =[X] vm2 & sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2).

  Let Pfor (i:var_i) vs s1 c s2 :=
    forall X c',
    update_c (update_i fresh_id p X) c = ok c' ->
    Sv.Subset (Sv.add i (Sv.union (read_c c) (write_c c))) X ->
    forall vm1, evm s1 =[X] vm1 ->
    exists2 vm2, evm s2 =[X] vm2 & sem_for p' ev i vs (with_vm s1 vm1) c' (with_vm s2 vm2).

  Let Pfun scs m fn vargs scs' m' vres :=
    forall fnd vargs', get_fundef (p_funcs p) fn = Some fnd ->
    mapM2 ErrType truncate_val (f_tyin fnd) vargs = mapM2 ErrType truncate_val (f_tyin fnd) vargs' ->
    sem_call p' ev scs m fn vargs' scs' m' vres.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof.
    by move=> s X _ [<-] hs vm1 hvm1; exists vm1 => //; constructor.
  Qed.

  Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ hi _ hc X c'; rewrite /update_c /=.
    t_xrbindP => lc ci {}/hi hi cc hcc <- <-.
    rewrite read_c_cons write_c_cons => hsub vm1 hvm1.
    have [|vm2 hvm2 hs2]:= hi _ vm1 hvm1; first by SvD.fsetdec.
    have /hc : update_c (update_i fresh_id p X) c = ok (flatten cc).
    + by rewrite /update_c hcc.
    move=> /(_ _ vm2 hvm2) [|vm3 hvm3 hs3]; first by SvD.fsetdec.
    by exists vm3 => //=; apply: sem_app hs2 hs3.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by move=> ii i s1 s2 _ Hi X c' /Hi. Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x t ty e v v' he htr hw ii X c' [<-].
    rewrite read_Ii /write_I /write_I_rec vrv_recE read_i_assgn => hsub vm1 hvm1.
    move: he; rewrite (read_e_eq_on_empty _ _ (vm := vm1)); last first.
    + by apply: eq_onI hvm1; rewrite read_eE; SvD.fsetdec.
    rewrite eq_globs => he; have [|vm2 ? eq_s2_vm2]:= write_lval_eq_on _ hw hvm1.
    + by SvD.fsetdec.
    exists vm2.
    + by apply: (eq_onI _ eq_s2_vm2); SvD.fsetdec.
    by apply/sem_seq1/EmkI/(Eassgn _ _ he htr); rewrite -eq_globs.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es He ii X c' [<-].
    rewrite read_Ii read_i_opn /write_I /write_I_rec vrvs_recE => hsub vm1 hvm1.
    move: He; rewrite eq_globs /sem_sopn Let_Let.
    t_xrbindP => vs Hsem_pexprs res Hexec_sopn hw.
    case: (write_lvals_eq_on _ hw hvm1); first by SvD.fsetdec.
    move=> vm2  ? eq_s2_vm2; exists vm2.
    + by apply: (eq_onI _ eq_s2_vm2); SvD.fsetdec.
    apply/sem_seq1/EmkI; constructor.
    rewrite /sem_sopn Let_Let -(read_es_eq_on _ _ (s := X)); last first.
    + by rewrite read_esE; apply: (eq_onI _ hvm1); SvD.fsetdec.
    by rewrite Hsem_pexprs /= Hexec_sopn.
  Qed.

  Lemma write_Ii ii i : write_I (MkI ii i) = write_i i.
  Proof. by []. Qed.

  Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 He Hs Hc ii X c' /=.
    t_xrbindP => i_then i_thenE i_else i_elseE {c'}<-.
    rewrite !(read_Ii, write_Ii) !(read_i_if, write_i_if) => le_X.
    move=> vm1 eq_s1_vm1; case: (Hc X _ i_thenE _ vm1 eq_s1_vm1).
    + by SvD.fsetdec.
    move=> vm2 eq_s2_vm2 sem_i_then; exists vm2 => //.
    apply/sem_seq1/EmkI; apply: Eif_true => //.
    rewrite - eq_globs -He.
    rewrite -read_e_eq_on_empty // -/(read_e _).
    by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 He Hs Hc ii X c' /=.
    t_xrbindP => i_then i_thenE i_else i_elseE {c'}<-.
    rewrite !(read_Ii, write_Ii) !(read_i_if, write_i_if) => le_X.
    move=> vm1 eq_s1_vm1; case: (Hc X _ i_elseE _ vm1 eq_s1_vm1).
    + by SvD.fsetdec.
    move=> vm2 eq_s2_vm2 sem_i_else; exists vm2 => //.
    apply/sem_seq1/EmkI; apply: Eif_false => //.
    rewrite - eq_globs -He.
    rewrite -read_e_eq_on_empty // -/(read_e _).
    by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' sem_s1_s2 H_s1_s2.
    move=> sem_s2_e sem_s2_s3 H_s2_s3 sem_s3_s4 H_s3_s4.
    move=> ii X c'' /=; t_xrbindP=> d dE d' d'E {c''}<-.
    rewrite !(read_Ii, write_Ii) !(read_i_while, write_i_while).
    move=> le_X vm1 eq_s1_vm1.
    case: (H_s1_s2 X _ dE _ _ eq_s1_vm1); first by SvD.fsetdec.
    move=> vm2 eq_s2_vm2 sem_vm1_vm2.
    case: (H_s2_s3 X _ d'E _ _ eq_s2_vm2); first by SvD.fsetdec.
    move=> vm3 eq_s3_vm3 sem_vm2_vm3.
    case: (H_s3_s4 ii X [:: MkI ii (Cwhile a d e d')] _ _ vm3) => //=.
    + by rewrite dE d'E.
    + rewrite !(read_Ii, write_Ii) !(read_i_while, write_i_while).
      by SvD.fsetdec.
    move=> vm4 eq_s4_vm4 sem_vm3_vm4; exists vm4 => //.
    apply/sem_seq1/EmkI; apply: (Ewhile_true sem_vm1_vm2 _ sem_vm2_vm3).
    + rewrite -(make_referenceprog_globs Hp) -sem_s2_e.
      rewrite -read_e_eq_on_empty // -/(read_e _).
      by apply: (eq_onI _ eq_s2_vm2); SvD.fsetdec.
    by elim/sem_seq1I: sem_vm3_vm4 => /sem_IE.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
   move=> s1 s2 a c e c' He Hc eq_s_e ii X c'' /=.
   t_xrbindP => while_false while_falseE c''' eq_c' <-.
   rewrite !(read_Ii, write_Ii) !(read_i_while, write_i_while).
   move => le_X vm1 eq_s1_vm1.
   case: (Hc X _ while_falseE _ vm1 eq_s1_vm1).
   + by SvD.fsetdec.
   move => vm2 eq_s2_vm2 sem_while_false; exists vm2 => //.
   apply/sem_seq1/EmkI.
   apply Ewhile_false => //.
   rewrite -(make_referenceprog_globs Hp) - eq_s_e.
   rewrite -read_e_eq_on_empty // -/(read_e _).
   by apply: (eq_onI _ eq_s2_vm2) ; SvD.fsetdec.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    move => s1 x c X c' Hc le_X vm1 eq_s1_vm1.
    by exists vm1 => //; constructor.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move => s1 s2 s3 s4 x w ws c eq_s2 sem_s2_s3 H_s2_s3 H_s3_s4 Pfor_s3_s4 X c'.
    move => eq_c' le_X vm1 eq_s1_vm1.
    case : (write_var_eq_on eq_s2 eq_s1_vm1) => vm2 eq_write eq_s2_vm2.
    case : (H_s2_s3 X _ eq_c' _ vm2).
    + by SvD.fsetdec.
    + by apply: (eq_onI _ eq_s2_vm2) ; SvD.fsetdec.
    move => vm3 eq_s3_vm3 sem_vm2_vm3.
    case : (Pfor_s3_s4 X _ eq_c' _ vm3 eq_s3_vm3) => //.
    move => vm4 eq_s4_vm4 sem_vm3_vm4.
    exists vm4 => //.
    by apply (EForOne eq_write sem_vm2_vm3 sem_vm3_vm4).
  Qed.

  Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 x d lo hi c vlo vhi cpl_lo cpl_hi cpl_for sem_s1_s2.
    move=> ii X c' /=; t_xrbindP=> {c'} c' c'E <-.
    rewrite !(read_Ii, write_Ii) !(read_i_for, write_i_for).
    move=> le_X vm1 eq_s1_vm1.
    case: (sem_s1_s2 X _ c'E _ _ eq_s1_vm1); first by SvD.fsetdec.
    move=> vm2 eq_s2_vm2 sem_vm1_vm2; exists vm2 => //.
    apply/sem_seq1/EmkI/(Efor (vlo := vlo) (vhi := vhi)) => //.
    + rewrite -(make_referenceprog_globs Hp) - cpl_lo.
      rewrite -read_e_eq_on_empty // -/(read_e _).
      by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
    rewrite - eq_globs - cpl_hi.
    rewrite -read_e_eq_on_empty // -/(read_e _).
    by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
  Qed.

  Lemma is_reg_ptr_expr_ty b ii ctr x ty lv y:
     is_reg_ptr_expr fresh_id b ii ctr x ty lv = Some y -> vtype y = ty.
  Proof. by case: lv => //= [? | _ _ _ ? _]; case: ifP => // _ [<-]. Qed.

  Lemma make_prologueP X ii s:
     forall xfty ctr args Y pl args',
       make_prologue fresh_id ii Y ctr xfty args = ok (pl, args') ->
       Sv.Subset X Y ->
       Sv.Subset (read_es args) X ->
     forall vargs vs vm1,
       sem_pexprs true (p_globs p) s args = ok vargs ->
       mapM2 ErrType truncate_val (map snd xfty) vargs = ok vs ->
       evm s =[X] vm1 ->
     exists vm2 vargs', [/\
      sem p' ev (with_vm s vm1) pl (with_vm s vm2),
      sem_pexprs true (p_globs p') (with_vm s vm2) args' = ok vargs',
      mapM2 ErrType truncate_val (map snd xfty) vargs' = ok vs &
      vm1 =[Y] vm2].
  Proof.
    elim.
    + move=> ctr [] //= Y _ _ [<- <-] _ _ _ _ vm1 [<-] [<-] _.
      exists vm1, [::]; split => //; constructor.
    move=> [[b x] ty] xfty ih ctr [] //= a args Y _pl _args'; rewrite read_es_cons.
    move=> hisr hXY hX _vargs _vs vm1; t_xrbindP => va hva vargs hvargs <- {_vargs}.
    t_xrbindP => v hv vs hvs <- {_vs} heqvm.
    have [haX hasX]: Sv.Subset (read_e a) X /\ Sv.Subset (read_es args) X by split; SvD.fsetdec.
    case E: is_reg_ptr_expr hisr => [y | ]; t_xrbindP; last first.
    + move=> [c args'] hmk [<- <-] {_pl _args'}.
      have [vm2 [vargs' [h1 h2 h3 h4]]]:= ih _ _ _ _ _ hmk hXY hasX _ _ vm1 hvargs hvs heqvm.
      exists vm2, [:: va & vargs']; split => //=; last by rewrite hv h3.
      rewrite -(eq_on_sem_pexpr _ _ (s:= s)) //=; last first.
      + by apply (eq_onT (vm2:= vm1));[apply: eq_onI heqvm => //| apply: eq_onI h4; SvD.fsetdec ].
      by rewrite h2 -(make_referenceprog_globs Hp) hva.
    move=> /Sv_memP hnin [c args'] hmk [<- <-]{_pl _args'}.
    have ? := is_reg_ptr_expr_ty E; subst ty.

    pose vm1' := vm1.[y <- v].
    have [|| vm2 [vargs' [h1 h2 h3 h4]]]:= ih _ _ _ _ _ hmk _ hasX _ _ vm1' hvargs hvs.
    + by SvD.fsetdec.
    + by apply: (eq_onT heqvm)=> z hz; rewrite /vm1' Vm.setP_neq //; apply/eqP => h;apply hnin; SvD.fsetdec.
    exists vm2, [:: v & vargs']; split => //; first last.
    + apply (eq_onT (vm2:= vm1')); last by apply: eq_onI h4; SvD.fsetdec.
      by move=> z hz; rewrite /vm1' Vm.setP_neq //; apply/eqP => h;apply hnin; SvD.fsetdec.
    + by rewrite (truncate_val_idem hv) h3.
    + rewrite /= /get_gvar /= /get_var -(h4 y); last by SvD.fsetdec.
      rewrite /vm1' Vm.setP_eq /= vm_truncate_val_eq; last by apply: truncate_val_has_type hv.
      by rewrite (truncate_val_defined hv) /= h2.
    apply: Eseq h1; apply/EmkI; econstructor; eauto.
    + rewrite -hva -(make_referenceprog_globs Hp); apply eq_on_sem_pexpr => //.
      by rewrite evm_with_vm; apply/eq_onS/eq_onI/heqvm.
    rewrite /write_lval; apply/write_var_eq_type.
    + by apply: truncate_val_has_type hv.
    by apply: truncate_val_DB hv.
  Qed.

  Lemma make_epilogueP X ii s1 s2 xfty lv lv' ep vres vs vm1 :
    make_epilogue fresh_id ii X xfty lv = ok (lv', ep) ->
    Sv.Subset (Sv.union (read_rvs lv) (vrvs lv)) X ->
    write_lvals true (p_globs p) s1 lv vs = ok s2 ->
    mapM2 ErrType truncate_val (map snd xfty) vres = ok vs ->
    evm s1 =[X] vm1 ->
    exists vm2 s2', [/\
      write_lvals true (p_globs p') (with_vm s1 vm1) lv' vs = ok s2',
      sem p' ev s2' ep (with_vm s2 vm2) &
      evm s2 =[X] vm2].
  Proof.
    move=> eqE hsub hw htr heqon; move: eqE; rewrite /make_epilogue.
    t_xrbindP => pinstrs Hpseudo Hswap.
    have [vm2 Hsem_pis eq_s2_vm2]:= make_pseudo_codeP Hpseudo htr hsub hw heqon.
    have [sy [vmy] [Hwrite_lvals Hsem /= eq_vm2_vmy]]:= swapableP Hswap Hsem_pis.
    exists vmy, sy ; split => //.
    by apply/(eq_onT eq_s2_vm2)/vm_eq_eq_on.
  Qed.

  Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 scs m s2 lv fn args vargs aout eval_args h1 h2 h3.
    move=> ii' X c' hupd; rewrite !(read_Ii, write_Ii).
    rewrite !(read_i_call, write_i_call) => le_X vm1 eq_s1_vm1.
    case: (sem_callE h1) hupd => fnd [fnE] [vs] [s1'] [s2'] [s3'] [vres] [vsE] [_ hwrinit] _ [hgetout aoutE] _.
    rewrite /= /get_sig fnE.
    have heqin : map snd (map2 mk_info (f_params fnd) (f_tyin fnd)) = f_tyin fnd.
    + have [_ h] := size_mapM2 vsE; rewrite -(size_fold2 hwrinit) in h.
      by rewrite map2E -map_comp -{2}(unzip2_zip (eq_leq h)); apply map_ext.
    have heqout : map snd (map2 mk_info (f_res fnd) (f_tyout fnd)) = f_tyout fnd.
    + have [h _] := size_mapM2 aoutE; rewrite -(size_mapM hgetout) in h.
      by rewrite map2E -map_comp -{2}(unzip2_zip (eq_leq h)); apply map_ext.
    move=> {s1' s2' s3' hwrinit hgetout}.
    t_xrbindP=> -[pl eargs] plE; t_xrbindP=> -[lvaout ep] epE [] <-.
    rewrite -heqin in vsE.
    have [|]:= make_prologueP plE (@SvP.MP.subset_refl X) _ eval_args vsE eq_s1_vm1; first by SvD.fsetdec.
    rewrite heqin.
    move=> vmx [vargs'] [sem_pl eval_vargs' trunc_vargs' eq_vm1_vmx].
    rewrite -heqout in aoutE.
    have [|vm2 [s3] [Hwr_lvals Hsem eq_s2_vm2]]:=
      make_epilogueP epE _ h3 aoutE (eq_onT eq_s1_vm1 eq_vm1_vmx); first by SvD.fsetdec.
    exists vm2 => //.
    apply : (sem_app sem_pl); apply : (Eseq _ Hsem); apply : EmkI.
    econstructor.
    + by apply eval_vargs'.
    2: by apply Hwr_lvals.
    by apply (h2 _ _ fnE); rewrite trunc_vargs' -vsE heqin.
  Qed.

  Lemma eq_extra : p_extra p = p_extra p'.
    move : Hp.
    rewrite /makereference_prog.
    by t_xrbindP => y Hmap <-.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> sc1 m1 sc2 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hf Hvargs.
    move=> Hs0 Hs1 Hsem_s2 Hs2 Hvres Hvres' Hscs2 Hm2 f' vargs1.
    rewrite Hf => -[?] h; subst f'; rewrite h in Hvargs => {h}.
    have H := (all_progP _ Hf).
    rewrite eq_extra in Hs0.
    move : Hp; rewrite /makereference_prog; t_xrbindP => y Hmap ?.
    subst p'.
    case : (get_map_cfprog_gen Hmap Hf) => x Hupdate Hy.
    move : Hupdate.
    rewrite /update_fd.
    t_xrbindP => z Hupdate_c Hwith_body.
    subst x => /=.
    have [||x Hevms2 Hsem] := (Hs2 _ _ Hupdate_c _ (evm s1)) => //; first by SvD.fsetdec.
    rewrite with_vm_same in Hsem.
    eapply EcallRun ; try by eassumption.
    rewrite -Hvres -!(sem_pexprs_get_var _ (p_globs p)).
    symmetry; move : Hevms2; rewrite -read_esE; apply : read_es_eq_on.
  Qed.

  Lemma exec_syscall_truncate scs m o ves scs' m' vs:
    exec_syscall (pT := progUnit) scs m o ves = ok (scs', m', vs) ->
    exists2 ves',
      mapM2 ErrType truncate_val [seq i.2 | i <- (get_syscall_sig o).1] ves = ok ves' &
      mapM2 ErrType truncate_val [seq i.2 | i <- (get_syscall_sig o).2] vs = ok vs.
  Proof.
    case: o => len /=; t_xrbindP; rewrite /exec_getrandom_u => -[scs1 vs1] hex _ _ <- /=.
    case: ves hex => // v [] //=; t_xrbindP => t ht t' hfill ??; subst scs1 vs1.
    rewrite /truncate_val /= ht /= WArray.castK; eexists; eauto.
  Qed.

  Lemma exec_syscall_eq_tr scs m o ves ves' scs' m' vs :
    mapM2 ErrType truncate_val [seq i.2 | i <- (get_syscall_sig o).1] ves =
      mapM2 ErrType truncate_val [seq i.2 | i <- (get_syscall_sig o).1] ves' ->
    exec_syscall (pT := progUnit) scs m o ves = ok (scs', m', vs) ->
    exec_syscall (pT := progUnit) scs m o ves' = ok (scs', m', vs).
  Proof.
    case: o => len /=; t_xrbindP; rewrite /exec_getrandom_u.
    case: ves ves' => // v [] // ves' heq [scs1 vs'].
    t_xrbindP => t ht t' hfill ?????; subst scs1 vs' scs' m' vs.
    move: heq; rewrite /truncate_val /= ht /=.
    case: ves' => // v' ves' h; have {h}:= sym_eq h.
    by t_xrbindP => ?? h <- ?; case: ves' => // -[?] /Varr_inj [?] ??; subst; rewrite h hfill.
  Qed.

  Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> s1 scs m s2 o xs es ves vs hes ho hw ii X c /=.
    t_xrbindP => -[pl es'] plE; apply: rbindP => -[xs' el] elE [<-]{c}.
    rewrite read_Ii read_i_syscall write_Ii write_i_syscall => hsub vm1 hvm1.
    have [ves1]:= exec_syscall_truncate ho.
    rewrite /get_syscall_sig /= => htves htvs.
    have []:= make_prologueP plE (@SvP.MP.subset_refl X) _ hes htves hvm1; first by SvD.fsetdec.
    move=> vmx [ves' [hpl hves' htves' vm1_vmx]].
    have [] := make_epilogueP elE _ hw htvs (eq_onT hvm1 vm1_vmx); first by SvD.fsetdec.
    move=> vm2 [s2' [hw' hel s2_svm2]]; exists vm2 => //.
    apply : (sem_app hpl); apply : (Eseq _ hel); apply : EmkI.
    econstructor; eauto; last by apply hw'.
    by apply: exec_syscall_eq_tr ho; rewrite htves'.
  Qed.

  Lemma makeReferenceArguments_callP f scs mem scs' mem' va vr:
    sem_call p ev scs mem f va scs' mem' vr ->
    sem_call p' ev scs mem f va scs' mem' vr.
  Proof.
    move=> Hsem; case: (sem_callE Hsem) => fd [hget _].
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
         Hproc
         Hsem
         _ _
         hget).
  Qed.

End WITH_PARAMS.
