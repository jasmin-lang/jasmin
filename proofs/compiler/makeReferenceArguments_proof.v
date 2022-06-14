(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem compiler_util.
Require Export makeReferenceArguments.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

  Section DiagonalInduction2.
  Context {Ta Tb : Type} (P : seq Ta -> seq Tb -> Prop).
  Hypothesis Pa0 : forall a , P a [::].
  Hypothesis P0b : forall b , P [::] b.
  Hypothesis Pcons2 : forall ha hb ta tb , P ta tb -> P (ha::ta) (hb::tb).

  Lemma diagonal_induction_2 a b:
    P a b.
  Proof.
    elim : a b => // ha ta Ih [] // hb tb.
    by apply : Pcons2.
  Qed.

  End DiagonalInduction2.

  Section DiagonalInduction2Eq.
  Context {Ta Tb : Type} (P : seq Ta -> seq Tb -> Prop).
  Hypothesis P00 : P [::] [::].
  Hypothesis Pcons2 : forall ha hb ta tb , size ta = size tb -> P ta tb -> P (ha::ta) (hb::tb).

  Lemma diagonal_induction_2_eq a b:
    size a = size b -> P a b.
  Proof.
    elim : a b => [|ha ta ih] /= b.
    + by move /esym /size0nil => ->.
    case : b => //= hb tb [] eqsab.
    apply Pcons2 => //.
    by apply ih.
  Qed.

  End DiagonalInduction2Eq.

  Section DiagonalInduction3.
  Context {Ta Tb Tc : Type} (P : seq Ta -> seq Tb -> seq Tc -> Prop).
  Hypothesis Pab0 : forall a b , P a b [::].
  Hypothesis Pa0c : forall a c , P a [::] c.
  Hypothesis P0bc : forall b c , P [::] b c.
  Hypothesis Pcons3 : forall ha hb hc ta tb tc , P ta tb tc -> P (ha::ta) (hb::tb) (hc::tc).

  Lemma diagonal_induction_3 a b c:
    P a b c.
  Proof.
    move : a b c.
    apply : diagonal_induction_2 => // ha hb ta tb Ihab.
    elim => // hc tc Ihc.
    apply : Pcons3.
    by apply Ihab.
  Qed.

  End DiagonalInduction3.

  Section DiagonalInduction3Eq.
  Context {Ta Tb Tc : Type} (P : seq Ta -> seq Tb -> seq Tc -> Prop).
  Hypothesis P000 : P [::] [::] [::].
  Hypothesis Pcons3 : forall ha hb hc ta tb tc , size ta = size tb -> size tb = size tc -> P ta tb tc -> P (ha::ta) (hb::tb) (hc::tc).

  Lemma diagonal_induction_3_eq a b c:
    size a = size b -> size b = size c -> P a b c.
  Proof.
    elim : a b c => [|ha ta ih] /= b c.
    + move /esym /size0nil => -> /=.
      by move /esym /size0nil => ->.
    case : b => //= hb tb [] eqsab.
    case : c => //= hc tc [] eqsbc.
    apply Pcons3 => //.
    by apply ih.
  Qed.

  End DiagonalInduction3Eq.

  Section DiagonalInduction4.
  Context {Ta Tb Tc Td : Type} (P : seq Ta -> seq Tb -> seq Tc -> seq Td -> Prop).
  Hypothesis Pabc0 : forall a b c , P a b c [::].
  Hypothesis Pab0d : forall a b d , P a b [::] d.
  Hypothesis Pa0cd : forall a c d , P a [::] c d.
  Hypothesis P0bcd : forall b c d , P [::] b c d.
  Hypothesis Pcons4 : forall ha hb hc hd ta tb tc td , P ta tb tc td -> P (ha::ta) (hb::tb) (hc::tc) (hd::td).

  Lemma diagonal_induction_4 a b c d:
    P a b c d.
  Proof.
    move : a b c d.
    apply : diagonal_induction_2 => // ha hb ta tb Ihab.
    apply : diagonal_induction_2 => // hc hd tc td Ihcd.
    apply : Pcons4.
    by apply Ihab.
  Qed.

  End DiagonalInduction4.

  Section DiagonalInduction4Eq.
  Context {Ta Tb Tc Td : Type} (P : seq Ta -> seq Tb -> seq Tc -> seq Td -> Prop).
  Hypothesis P0000 : P [::] [::] [::] [::].
  Hypothesis Pcons4 : forall ha hb hc hd ta tb tc td , size ta = size tb -> size tb = size tc -> size tc = size td -> P ta tb tc td -> P (ha::ta) (hb::tb) (hc::tc) (hd::td).

  Lemma diagonal_induction_4_eq a b c d:
    size a = size b -> size b = size c -> size c = size d -> P a b c d.
  Proof.
    elim : a b c d => [|ha ta ih] /= b c d.
    + move /esym /size0nil => -> /=.
      move /esym /size0nil => -> /=.
      by move /esym /size0nil => ->.
    case : b => //= hb tb [] eqsab.
    case : c => //= hc tc [] eqsbc.
    case : d => //= hd td [] eqscd.
    apply Pcons4 => //.
    by apply ih.
  Qed.

  End DiagonalInduction4Eq.

  Section DiagonalInduction5eq.
  Context {Ta Tb Tc Td Te : Type} (P : seq Ta -> seq Tb -> seq Tc -> seq Td -> seq Te -> Prop).
  Hypothesis P00000 : P [::] [::] [::] [::] [::].
  Hypothesis Pcons5 : forall ha hb hc hd he ta tb tc td te, size ta = size tb -> size tb = size tc -> size tc = size td -> size td = size te -> P ta tb tc td te -> P (ha::ta) (hb::tb) (hc::tc)  (hd::td) (he::te).

  Lemma diagonal_induction_5_eq a b c d e:
    size a = size b -> size b = size c -> size c = size d -> size d = size e -> P a b c d e.
  Proof.
    elim : a b c d e => [|ha ta ih] /= b c d e.
    + move /esym /size0nil => -> /=.
      move /esym /size0nil => -> /=.
      move /esym /size0nil => -> /=.
      by move /esym /size0nil => ->.
    case : b => //= hb tb [] eqsab.
    case : c => //= hc tc [] eqsbc.
    case : d => //= hd td [] eqscd.
    case : e => //= he te [] eqsde.
    apply Pcons5 => //.
    by apply ih.
  Qed.

  End DiagonalInduction5eq.

  Lemma zip_nilL {T U : Type} (xs : seq U) : zip ([::] : seq T) xs = [::].
  Proof. by case: xs. Qed.

  Lemma zip_nilR {T U : Type} (xs : seq T) : zip xs ([::] : seq U) = [::].
  Proof. by case: xs. Qed.

  Definition zip_nil := (@zip_nilL, @zip_nilR).


Section SemInversion.
Context {pd: PointerData}.
Context `{asmop:asmOp}.
Context (T : eqType) (pT : progT T) (cs : semCallParams).
Context (p : prog) (ev : extra_val_t).

Lemma sem_nilI s1 s2 (P : estate -> estate -> Prop) :
  P s2 s2 -> sem p ev s1 [::] s2 -> P s1 s2.
Proof. by move=> ? /semE <-. Qed.

Lemma sem_consI s1 i c s2 (P : estate -> instr -> cmd -> estate -> Prop) :
  (forall s3, sem_I p ev s1 i s3 -> sem p ev s3 c s2 -> P s1 i c s2) ->
  sem p ev s1 (i::c) s2 -> P s1 i c s2.
Proof. by move=> h /semE [s3 [] /h]. Qed.

Lemma set_var_rename (vm vm' vm'' : vmap) (x y : var) (v : value) :
     vtype x = vtype y
  -> set_var vm x v = ok vm'
  -> exists vm''', set_var vm'' y v = ok vm'''.
Proof.
case: x y => [ty nx] [? ny] /= <-.
set x := {| vname := nx |}; set y := {| vname := ny |}.
apply: set_varP => /=.
+ by move=> t okt /esym vm'E ; exists vm''.[y <- ok t] ; rewrite /set_var okt.
+ move=> tybool tyvE /esym vm'E; exists vm''.[y <- pundef_addr ty].
  by rewrite /set_var tybool tyvE.
Qed.

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

Section Section.

  Context
    {pd: PointerData}
    `{asmop:asmOp}
    (is_reg_ptr : var -> bool)
    (fresh_id : glob_decls -> var -> Ident.ident).

  Lemma make_referenceprog_globs (p p' : uprog) :
    makereference_prog is_reg_ptr fresh_id p = ok p' ->
      p.(p_globs) = p'.(p_globs).
  Proof.
    case: p p' => [???] [???]; t_xrbindP.
    by rewrite /makereference_prog; t_xrbindP.
  Qed.

  Lemma make_prologue0 (p : uprog) ii X :
    make_prologue is_reg_ptr fresh_id p ii X [::] [::] [::] = ok ([::], [::]).
  Proof. by []. Qed.

  Lemma make_prologueS_None (p : uprog) ii X x xs fty ftys pe pes c args :
       is_reg_ptr_expr is_reg_ptr fresh_id p (v_var x) pe = None
    -> make_prologue is_reg_ptr fresh_id p ii X xs ftys pes = ok (c, args)
    -> make_prologue is_reg_ptr fresh_id p ii X (x :: xs) (fty :: ftys) (pe :: pes)
       = ok (c, pe :: args).
  Proof. by move=> /= -> ->. Qed.

  Lemma make_prologueS_Some (p : uprog) ii X x xs fty ftys pe pes (y : var_i) c args :
       fty = vtype y -> ~~ is_sbool fty -> ~~Sv.mem y X
    -> is_reg_ptr_expr is_reg_ptr fresh_id p (v_var x) pe = Some y
    -> make_prologue is_reg_ptr fresh_id p ii (Sv.add y X) xs ftys pes = ok (c, args)
    -> make_prologue is_reg_ptr fresh_id p ii X (x :: xs) (fty :: ftys) (pe :: pes)
       = ok ((MkI ii (Cassgn (Lvar y) AT_rename fty pe) :: c, Plvar y :: args)).
  Proof. by move=> eq1 eq2 eq3 /= ->; rewrite eq2 eq1 eq3 eqxx /= => ->. Qed.

  Section MakePrologueInd.
  Variable P : Sv.t -> seq var_i -> seq stype -> pexprs -> cmd -> pexprs -> Prop.
  Variable (p : uprog) (ii : instr_info).

  Hypothesis P0 : forall X, P X [::] [::] [::] [::] [::].

  Hypothesis PSNone :
    forall X x xs fty ftys pe pes c args,
         is_reg_ptr_expr is_reg_ptr fresh_id p (v_var x) pe = None
      -> make_prologue is_reg_ptr fresh_id p ii X xs ftys pes = ok (c, args)
      -> P X xs ftys pes c args
      -> P X (x :: xs) (fty :: ftys) (pe :: pes) c (pe :: args).

  Hypothesis PSSome :
    forall X x xs fty ftys pe pes (y : var_i) c args,
       fty = vtype y -> ~~ is_sbool fty -> ~~Sv.mem y X
    -> is_reg_ptr_expr is_reg_ptr fresh_id p (v_var x) pe = Some y
    -> make_prologue is_reg_ptr fresh_id p ii (Sv.add y X) xs ftys pes = ok (c, args)
    -> P (Sv.add y X) xs ftys pes c args
    -> P X (x :: xs) (fty :: ftys) (pe :: pes)
         (MkI ii (Cassgn (Lvar y) AT_rename fty pe) :: c) (Plvar y :: args).

  Lemma make_prologueW X xs ftys pes c args :
       make_prologue is_reg_ptr fresh_id p ii X xs ftys pes = ok (c, args)
    -> P X xs ftys pes c args.
  Proof.
  move: xs ftys pes X c args; apply: diagonal_induction_3;
    last 1 [idtac] || by case=> [|??] [|??] //= X c args [<- <-].
  move=> x fty pe xs ftys pes ih X c args /=.
  case E: (is_reg_ptr_expr _ _ _ _ _) => [y|] /=; last first.
  + by t_xrbindP; case=> c' args' h [<- <-]; apply/PSNone/ih.
  + t_xrbindP=> /= /and3P[/eqP h1 h2 h3] [c' args'].
    by move=> h [<- <-]; apply/PSSome/ih.
  Qed.
  End MakePrologueInd.

  Variant make_prologue_spec (p : uprog) (ii : instr_info) :
    Sv.t -> seq var_i -> seq stype -> pexprs -> cmd -> pexprs -> Prop
  :=

  | MakePrologue0 X :
       make_prologue_spec p ii X [::] [::] [::] [::] [::]

  | MakePrologueS_None X x xs fty ftys pe pes c args :
       is_reg_ptr_expr is_reg_ptr fresh_id p (v_var x) pe = None
    -> make_prologue is_reg_ptr fresh_id p ii X xs ftys pes = ok (c, args)
    -> make_prologue_spec p ii X (x :: xs) (fty :: ftys) (pe :: pes) c (pe :: args)

  | MakePrologueS_Some X x xs fty ftys pe pes (y : var_i) c args :
       fty = vtype y -> ~~ is_sbool fty -> ~~Sv.mem y X
    -> is_reg_ptr_expr is_reg_ptr fresh_id p (v_var x) pe = Some y
    -> make_prologue is_reg_ptr fresh_id p ii (Sv.add y X) xs ftys pes = ok (c, args)
    -> make_prologue_spec p ii X (x :: xs) (fty :: ftys) (pe :: pes)
         (MkI ii (Cassgn (Lvar y) AT_rename fty pe) :: c) (Plvar y :: args).

  Lemma make_prologueP p ii X xs ftys pes c args :
       make_prologue is_reg_ptr fresh_id p ii X xs ftys pes = ok (c, args)
    -> make_prologue_spec p ii X xs ftys pes c args.
  Proof.
  elim/make_prologueW=> {X xs ftys pes c args} X.
  + by constructor.
  + by move=> x xs fty ftys pe pes c args *; apply: MakePrologueS_None.
  + by move=> x xs fty ftys pe pes c args *; apply: MakePrologueS_Some.
  Qed.

  Lemma make_prologue_size (p : uprog) ii X xs ftys pes c args :
      make_prologue is_reg_ptr fresh_id p ii X xs ftys pes = ok (c, args)
   -> (size xs = size ftys /\ size ftys = size pes).
  Proof.
  elim/make_prologueW=> {X xs ftys pes c args} X // x xs fty ftys pe pes c args.
  + by move=> _ _ /= [-> ->]. + by move=> _ _ _ _ _ _ /= [-> ->].
  Qed.

  Lemma make_pseudo_epilogue0 (p : uprog) ii X :
    make_pseudo_epilogue is_reg_ptr fresh_id p ii X [::] [::] [::] = ok ([::]).
  Proof. by []. Qed.

  Lemma make_pseudo_epilogueS_None (p : uprog) ii X x xs fty ftys lv lvs args :
       is_reg_ptr_lval is_reg_ptr fresh_id p (v_var x) lv = None
    -> make_pseudo_epilogue is_reg_ptr fresh_id p ii X xs ftys lvs = ok args
    -> make_pseudo_epilogue is_reg_ptr fresh_id p ii X (x :: xs) (fty :: ftys) (lv :: lvs)
       = ok (PI_lv lv :: args).
  Proof. by move => /= -> -> /=. Qed.

  Lemma make_pseudo_epilogueS_Some (p : uprog) ii X x xs fty ftys lv lvs (y : var_i) args :
       fty = vtype y -> ~~ is_sbool fty -> ~~Sv.mem y X
    -> is_reg_ptr_lval is_reg_ptr fresh_id p (v_var x) lv = Some y
    -> make_pseudo_epilogue is_reg_ptr fresh_id p ii X xs ftys lvs = ok args
    -> make_pseudo_epilogue is_reg_ptr fresh_id p ii X (x :: xs) (fty :: ftys) (lv :: lvs)
       = ok (PI_lv (Lvar y) :: (PI_i lv fty y) :: args).
  Proof. by move=> eq1 eq2 eq3 /= ->; rewrite eq2 eq1 eq3 eqxx /= => ->. Qed.

  Section MakeEpilogueInd.
  Variable P : seq var_i -> seq stype -> lvals -> seq pseudo_instr -> Prop.
  Variable (p : uprog) (ii : instr_info) (X:Sv.t).

  Hypothesis P0 : P [::] [::] [::] [::].

  Hypothesis PSNone :
    forall x xs fty ftys lv lvs args,
         is_reg_ptr_lval is_reg_ptr fresh_id p (v_var x) lv = None
      -> make_pseudo_epilogue is_reg_ptr fresh_id p ii X xs ftys lvs = ok args
      -> P xs ftys lvs args
      -> P (x :: xs) (fty :: ftys) (lv :: lvs) (PI_lv lv :: args).

  Hypothesis PSSome :
    forall x xs fty ftys lv lvs (y : var_i) args,
       fty = vtype y -> ~~ is_sbool fty -> ~~Sv.mem y X
    -> is_reg_ptr_lval is_reg_ptr fresh_id p (v_var x) lv = Some y
    -> make_pseudo_epilogue is_reg_ptr fresh_id p ii X xs ftys lvs = ok args
    -> P xs ftys lvs args
    -> P (x :: xs) (fty :: ftys) (lv :: lvs)
         (PI_lv (Lvar y) :: (PI_i lv fty y) :: args).

  Lemma make_pseudo_epilogueW xs ftys lvs args :
       make_pseudo_epilogue is_reg_ptr fresh_id p ii X xs ftys lvs = ok args
    -> P xs ftys lvs args.
  Proof.
  move: xs ftys lvs args; apply: diagonal_induction_3;
    last 1 [idtac] || by case=> [|??] [|??] //= args [<-].
  move=> x fty lv xs ftys lvs ih args /=.
  case E: (is_reg_ptr_lval _ _ _ _ _) => [y|] /=; last first.
  + by t_xrbindP => args' h <-; apply/PSNone/ih.
  + t_xrbindP=> /= /and3P[/eqP h1 h2 h3] args'.
    by move=> h <-; apply/PSSome/ih.
  Qed.
  End MakeEpilogueInd.

  Context (p p' : uprog).
  Context (ev : unit).

  Hypothesis Hp : makereference_prog is_reg_ptr fresh_id p = ok p'.

  Inductive sem_pis ii : estate -> seq pseudo_instr -> values -> estate -> Prop :=
   | SPI_nil : forall s, sem_pis ii s [::] [::] s
   | SPI_lv  : forall s1 s2 s3 lv pis v vs,
     write_lval (p_globs p') lv v s1 = ok s2 ->
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
        [/\ vs = v ::vs', write_lval (p_globs p') lv v s1 = ok s2 & sem_pis ii s2 pis' vs' s3 ]
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

  Lemma eq_funcs : map_cfprog (update_fd is_reg_ptr fresh_id p (get_sig p)) (p_funcs p) = ok (p_funcs p').
  Proof.
    move : Hp.
    rewrite /makereference_prog.
    by t_xrbindP => fdecls Hmap_cfprog <- /=.
  Qed.

  Lemma truncate_val_pof_val ty v vt:
    truncate_val ty v = ok vt ->
    exists w, pof_val ty vt = ok w /\ pto_val w = vt.
  Proof.
    case: v => [b | z | len a | s ws | ty' ?].
    + by move=> /truncate_val_bool [??]; subst ty vt => /=; exists b.
    + by move=> /truncate_val_int [??]; subst ty vt => /=; exists z.
    + rewrite /truncate_val; case: ty => //=.
      t_xrbindP=> len' a' hc <-; eexists;split; last reflexivity.
      by rewrite /to_arr WArray.castK.
    + move=> /truncate_val_word [ws' [? hsub ?]]; subst ty vt => /=.
      case: Sumbool.sumbool_of_bool; first by eauto.
      by rewrite cmp_le_refl.
    by rewrite /truncate_val of_val_undef.
  Qed.

  Lemma truncate_val_idem (t : stype) (v v' : value) :
    truncate_val t v = ok v' -> truncate_val t v' = ok v'.
  Proof.
  rewrite /truncate_val; case: t v => [||q|w].
  + by move=> x; t_xrbindP=> b bE <-.
  + by move=> x; t_xrbindP=> i iE <-.
  + move=> x; t_xrbindP=> a aE <- /=.
    by rewrite /WArray.cast Z.leb_refl /=; case: (a).
  + move=> x; t_xrbindP=> w' w'E <- /=.
    by rewrite truncate_word_u.
  Qed.

  Lemma make_pseudo_codeP ii X xs tys lvs pis s1 s2 vm1 vs vst:
    make_pseudo_epilogue is_reg_ptr fresh_id p ii X xs tys lvs = ok pis ->
    wf_vm vm1 ->
    mapM2 ErrType truncate_val tys vs = ok vst ->
    Sv.Subset (Sv.union (read_rvs lvs) (vrvs lvs)) X ->
    write_lvals (p_globs p) s1 lvs vst = ok s2 ->
    evm s1 =[X] vm1 ->
    exists vm2,
      [ /\ wf_vm vm2
      , sem_pis ii (with_vm s1 vm1) pis vst (with_vm s2 vm2)
      & evm s2 =[X] vm2].
  Proof.
    move=> h; elim /make_pseudo_epilogueW : h s1 vm1 vs vst => {xs tys lvs pis}.
    + by move=> s1 vm1 [] // _ wf_vm1 [] <- _ [<-] ?; exists vm1; split => //; constructor.
    + move=> x xs ty tys lv lvs pis hnone _ ih s1 vm1 [ //| v vs] vst' wf_vm1 /=.
      t_xrbindP => vt ht vst hts <- {vst'}.
      rewrite read_rvs_cons vrvs_cons => leX /=.
      t_xrbindP => s1' hw hws eqvm.
      have [|vm1' [eqvm' hw']]:= write_lval_eq_on _ hw eqvm; first by SvD.fsetdec.
      have := (wf_write_lval _ hw') => /= wf_vm1_vm1' ; have wf_vm1' := (wf_vm1_vm1' wf_vm1).
      case: (ih _ vm1' _ _ wf_vm1' hts _ hws _).
      - by SvD.fsetdec.
      - by apply: eq_onI eqvm'; SvD.fsetdec.
      move=> vm2' [ih1 ih2]; exists vm2'; split => //.
      econstructor; eauto.
      by rewrite -eq_globs.
    move=> x xs ty tys lv lvs y pis -> hb /Sv_memP hyX hsome _ ih s1 vm1 [ //| v vs] vst' /= wf_vm1.
    t_xrbindP => vt ht vst hts <- {vst'}.
    rewrite read_rvs_cons vrvs_cons => leX /=.
    t_xrbindP => s1' hw hws eqvm.
    have [vmy [hw' eqvmy semy]]: exists vmy,
      [/\ write_lval (p_globs p') y vt (with_vm s1 vm1) = ok (with_vm s1 vmy),
          evm s1 =[X] vmy &
          sem_pexpr (p_globs p') (with_vm s1 vmy) (Plvar y) = ok vt].
    + rewrite /write_lval /= /write_var evm_with_vm /set_var.
      case: (truncate_val_pof_val ht) => w [-> /= ?]; subst vt.
      exists (vm1.[y <- ok w]); split => //.
      - move=> z hz; rewrite Fv.setP_neq; first by apply eqvm.
        by apply/eqP => ?;subst z;SvD.fsetdec.
      by rewrite /get_gvar /= /get_var Fv.setP_eq.
    set I := mk_ep_i ii lv (vtype y) y.
    have := (wf_write_lval _ hw') => /= wf_vm1_vmy ; have wf_vmy := (wf_vm1_vmy wf_vm1).
    have [vm1' [wf_vm1' semI eqvm1']]: exists vm1',
     [/\ wf_vm vm1'
     , sem_I p' ev (with_vm s1 vmy) I (with_vm s1' vm1')
     & evm s1' =[X]  vm1'].
    + have [ | vm1' [eqvm1' hwvm1']]:= write_lval_eq_on (X:=X) _ hw eqvmy;first by SvD.fsetdec.
      exists vm1'; split; last by apply: eq_onI eqvm1'; SvD.fsetdec.
      - by have := (wf_write_lval _ hwvm1') => /= wf_vmy_vm1' ; apply wf_vmy_vm1'.
      constructor; apply Eassgn with vt vt => //.
      - by apply: truncate_val_idem ht.
      by rewrite -eq_globs.
    have [|vm2 [sem2 eqvm2]]:= ih s1' vm1' vs vst wf_vm1' hts _ hws eqvm1' ; first by SvD.fsetdec.
    exists vm2; split => //.
    econstructor; eauto; econstructor; eauto.
  Qed.

  (* Move the section in psem *)
  Section Sem_eqv.

  Let Pc s1 c s2 :=
    forall vm1 X,
      Sv.Subset (read_c c) X ->
      evm s1 =[X] vm1 ->
      exists vm2, sem p' ev (with_vm s1 vm1) c (with_vm s2 vm2) /\ evm s2 =[X] vm2.

  Let Pi s1 (i:instr) s2 :=
    forall vm1 X,
      Sv.Subset (read_I i) X ->
      evm s1 =[X] vm1 ->
      exists vm2, sem_I p' ev (with_vm s1 vm1) i (with_vm s2 vm2) /\ evm s2 =[X] vm2.

  Let Pi_r s1 (i:instr_r) s2 :=
    forall vm1 X,
      Sv.Subset (read_i i) X ->
      evm s1 =[X] vm1 ->
      exists vm2, sem_i p' ev (with_vm s1 vm1) i (with_vm s2 vm2) /\ evm s2 =[X] vm2.

  Let Pfor (i:var_i) zs s1 c s2 :=
    forall vm1 X,
      Sv.Subset (read_c c) X ->
        evm s1 =[X] vm1 ->
        exists vm2, sem_for p' ev i zs (with_vm s1 vm1) c (with_vm s2 vm2) /\ evm s2 =[X] vm2.

  Let Pfun (m:mem) (fn:funname) (args: values) (m':mem) (res:values) := true.

  Lemma read_cP X s1 c s2 vm1 :
    sem p' ev s1 c s2 ->
    Sv.Subset (read_c c) X ->
    evm s1 =[X] vm1 ->
    exists vm2, sem p' ev (with_vm s1 vm1) c (with_vm s2 vm2) /\ evm s2 =[X] vm2.
  Proof.
    move=> hsem;move: hsem vm1 X.
    apply : (sem_Ind (Pc := Pc) (Pi := Pi) (Pi_r := Pi_r) (Pfor := Pfor) (Pfun := Pfun)) => {s1 c s2}.
    + by move=> s vm1 X hsub heq; exists vm1; split => //;constructor.
    + move=> s1 s2 s3 i c _ ihi _ ihc vm1 X; rewrite read_c_cons => hsub heq1.
      case: (ihi vm1 X _ heq1); first by SvD.fsetdec.
      move=> vm2 [hi heq2].
      case: (ihc vm2 X _ heq2); first by SvD.fsetdec.
      by move=> vm3 [hc heq3]; exists vm3;split => //; econstructor; eauto.
    + move=> ii i s1 s2 _ ih vm1 X; rewrite read_Ii => hsub heq1.
      by case: (ih vm1 X hsub heq1) => vm2 [??];exists vm2; split.
    + move=> s1 s2 x t ty e v v' he htr hw vm1 X.
      rewrite read_i_assgn => hsub heq1.
      case: (write_lval_eq_on _ hw heq1); first by SvD.fsetdec.
      move=> vm2 [ heq2 ?];exists vm2; split.
      + econstructor; eauto.
        rewrite -(@read_e_eq_on _ _ Sv.empty) //.
        by rewrite read_eE => z hz; apply heq1; SvD.fsetdec.
      by move=> z hz;apply heq2; SvD.fsetdec.
    + move=> s1 s2 t o xs es.
      rewrite /sem_sopn; t_xrbindP => vargs vres hes hex hw vm1 X.
      rewrite read_i_opn => hsub heq1.
      case: (write_lvals_eq_on _ hw heq1); first by SvD.fsetdec.
      move=> vm2 [heq2 hw2]; exists vm2; split => //.
      econstructor; eauto.
      rewrite /sem_sopn -(@read_es_eq_on _ _ _ X) //; last first.
      + by move=> z;rewrite read_esE => hz;apply heq1; SvD.fsetdec.
      by rewrite hes /= hex /= hw2.
      by apply: eq_onI heq2; SvD.fsetdec.
    + move=> s1 s2 e c1 c2 he _ ih vm1 X.
      rewrite read_i_if => hsub heq1.
      case: (ih vm1 X _ heq1); first SvD.fsetdec.
      move=> vm2 [hs2 heq2]; exists vm2;split => //.
      apply Eif_true => //.
      rewrite -(@read_e_eq_on _ _ Sv.empty) //.
      by rewrite read_eE; apply: eq_onI heq1; SvD.fsetdec.
    + move=> s1 s2 e c1 c2 he _ ih vm1 X.
      rewrite read_i_if => hsub heq1.
      case: (ih vm1 X _ heq1); first SvD.fsetdec.
      move=> vm2 [hs2 heq2]; exists vm2;split => //.
      apply Eif_false => //.
      rewrite -(@read_e_eq_on _ _ Sv.empty) //.
      by rewrite read_eE; apply: eq_onI heq1; SvD.fsetdec.
    + move=> s1 s2 s3 s4 a c1 e c2 _ ih1 he _ ih2 _ ihw vm1 X.
      rewrite read_i_while => hsub heq1.
      case: (ih1 vm1 X _ heq1); first SvD.fsetdec.
      move=> vm2 [hs1 heq2]; case: (ih2 vm2 X _ heq2); first SvD.fsetdec.
      move=> vm3 [hs2 heq3]; case: (ihw vm3 X _ heq3); first by rewrite read_i_while.
      move=> vm4 [hs3 heq4]; exists vm4; split => //.
      apply: Ewhile_true; eauto.
      rewrite -(@read_e_eq_on _ _ Sv.empty) //.
      by rewrite read_eE; apply: eq_onI heq2; SvD.fsetdec.
    + move=> s1 s2 a c1 e c2 _ ih1 he vm1 X.
      rewrite read_i_while => hsub heq1.
      case: (ih1 vm1 X _ heq1); first SvD.fsetdec.
      move=> vm2 [hs1 heq2]; exists vm2; split => //.
      apply: Ewhile_false; eauto.
      rewrite -(@read_e_eq_on _ _ Sv.empty) //.
      by rewrite read_eE; apply: eq_onI heq2; SvD.fsetdec.
    + move=> s1 s2 i d lo hi c vlo vhi hlo hhi _ ih vm1 X.
      rewrite read_i_for => hsub heq1.
      case: (ih vm1 X _ heq1); first by SvD.fsetdec.
      move=> vm2 [? heq2]; exists vm2; split => //.
      by econstructor; eauto; rewrite -(@read_e_eq_on _ _ Sv.empty) // read_eE; apply: eq_onI heq1; SvD.fsetdec.
    + move=> s1 i c vm1 X hsub heq1.
      by exists vm1; split => //;constructor.
    + move=> s1 s2 s3 s4 i z zs c hwi _ ihc _ ihf vm1 X hsub heq1.
      case: (write_var_eq_on hwi heq1) => vm2 [heq2 hw2].
      case: (ihc vm2 X hsub); first by apply: eq_onI heq2; SvD.fsetdec.
      move=> vm3 [? heq3].
      case: (ihf vm3 X hsub heq3) => vm4 [? heq4]; exists vm4; split => //.
      by econstructor; eauto.
    + move=> s1 m2 s2 ii xs fn args vargs vs hargs hcall _ hw vm1 X.
      rewrite read_i_call => hsub heq1.
      case: (write_lvals_eq_on _ hw heq1); first by SvD.fsetdec.
      move=> vm2 [heq2 hw2]; exists vm2; split; last by apply: eq_onI heq2; SvD.fsetdec.
      econstructor; eauto.
      by rewrite -(@read_es_eq_on _ _ _ X) // read_esE;
        apply: eq_onI heq1;
        SvD.fsetdec.
    done.
  Qed.

  Lemma sem_eqv s1 c s2 vm1:
    sem p' ev s1 c s2 ->
    evm s1 =v vm1 ->
    exists vm2, sem p' ev (with_vm s1 vm1) c (with_vm s2 vm2) /\ evm s2 =v vm2.
  Proof.
    move=> hsem heq1.
    case: (read_cP (vm1 := vm1) (X:= Sv.union (read_c c) (write_c c)) hsem).
    + by SvD.fsetdec.
    + by move=> x hx;apply heq1.
    move=> vm2 [hsem2 heq2]; exists vm2; split => //.
    move=> x; case: (Sv_memP x (write_c c)) => hx.
    + by apply heq2; SvD.fsetdec.
    rewrite -(writeP hsem) // heq1.
    by have := writeP hsem2; rewrite !evm_with_vm => ->.
  Qed.

  Lemma set_var_spec x v vm1 vm2 vm1' :
    set_var vm1 x v = ok vm2 ->
    exists vm2', [/\ set_var vm1' x v = ok vm2', vm1' = vm2' [\ Sv.singleton x] & vm2'.[x] = vm2.[x]  ].
  Proof.
    rewrite /set_var.
    apply: set_varP => [ w -> | -> ->] /= <-.
    + exists vm1'.[x <- ok w]; split => //; last by rewrite !Fv.setP_eq.
      by move=> z hz; rewrite Fv.setP_neq //; apply/eqP; SvD.fsetdec.
    exists vm1'.[x <- pundef_addr (vtype x)]; split => //; last by rewrite !Fv.setP_eq.
    by move=> z hz; rewrite Fv.setP_neq //; apply/eqP; SvD.fsetdec.
  Qed.

  Lemma write_var_spec x v s1 s2 s1':
    write_var x v s1 = ok s2 ->
    exists vmx, [/\ write_var x v s1' = ok (with_vm s1' vmx),
                    evm s1' = vmx [\ Sv.singleton x] & vmx.[x] = (evm s2).[x]].
  Proof.
    rewrite /write_var; t_xrbindP => vm hs <- {s2}.
    by have [vmx [-> ?? /=]] := set_var_spec (evm s1') hs; exists vmx.
  Qed.

  End Sem_eqv.

  Lemma sem_pexpr_noload s m e v:
    noload e ->
    sem_pexpr (p_globs p') s e = ok v ->
    sem_pexpr (p_globs p') (with_mem s m) e = ok v.
  Proof.
    case: s => sm vm; rewrite /with_mem /=.
    pose P e :=
      forall v,
      noload e → sem_pexpr (p_globs p') {| emem := sm; evm := vm |} e = ok v → sem_pexpr (p_globs p') {| emem := m; evm := vm |} e = ok v.
    pose Q es :=
      forall vs,
      all noload es -> sem_pexprs (p_globs p') {| emem := sm; evm := vm |} es = ok vs →
      sem_pexprs (p_globs p') {| emem := m; evm := vm |} es = ok vs.
    apply: (pexpr_mut_ind (P:= P) (Q:= Q))=> {e v}; split; rewrite /P /Q //= => {P Q}.
    + move=> e ihe es ihes vs /andP [] /ihe{ihe}ihe /ihes{ihes}ihes.
      by t_xrbindP => ? /ihe -> /= ? /ihes -> /= <-.
    + move=> aa sz x e ih v /ih{ih}ih.
      apply: on_arr_gvarP => n t hx ->.
      by rewrite /on_arr_var /=; t_xrbindP => ze ve /ih -> /= -> ? /= -> <-.
    + move=> aa sz len x e ih v /ih{ih}ih.
      apply: on_arr_gvarP => n t hx ->.
      by rewrite /on_arr_var /=; t_xrbindP => ze ve /ih -> /= -> ? /= -> <-.
    + by move=> o e ih v /ih{ih}ih; t_xrbindP => ve /ih -> /= ->.
    + move=> o e1 ih1 e2 ih2 v /andP [] /ih1{ih1}ih1 /ih2{ih2}ih2.
      by t_xrbindP => ve1 /ih1 -> /= ve2 /ih2 -> /=.
    + move=> e es ihes v /ihes{ihes}ihes; t_xrbindP => ? /ihes.
      by rewrite /sem_pexprs => -> /=.
    move=> t e ihe e1 ihe1 e2 ihe2 v /and3P [] he he1 he2.
    by t_xrbindP => ?? /(ihe _ he) -> /= -> ?? /(ihe1 _ he1) -> /= -> ?? /(ihe2 _ he2) -> /= -> <-.
  Qed.

  Lemma sem_pexpr_noload_eq_on s1 s2 e v:
    noload e -> evm s1 =[read_e e] evm s2 ->
    sem_pexpr (p_globs p') s1 e = ok v ->
    sem_pexpr (p_globs p') s2 e = ok v.
  Proof.
    case: s2 => m2 vm2 hno heq he.
    have <- := sem_pexpr_noload m2 hno he.
    by apply eq_on_sem_pexpr => //=; apply eq_onS.
  Qed.

  Lemma swapableP ii pis lvs vs c s1 s2:
    swapable ii pis = ok (lvs, c) ->
    sem_pis ii s1 pis vs s2 ->
    exists s1' vm2,
      [/\ write_lvals (p_globs p') s1 lvs vs = ok s1',
          sem p' ev s1' c (with_vm s2 vm2) & Fv.ext_eq (evm s2) vm2].
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
    have [{nwm_pi} vm3 [hvm3 hw3]] := write_lvals_eq_on (@SvP.MP.subset_refl _) hws heqr.
    have hy : sem_pexpr (p_globs p') (with_vm s1' vm3) (Plvar y) = ok v.
    + rewrite -H; rewrite /=; apply: (get_gvar_eq_on _ (@SvP.MP.subset_refl _)).
      rewrite /read_gvar /= => y' /SvD.F.singleton_iff ?; subst y'.
      have := (disjoint_eq_ons (s:= Sv.singleton y) _ hw3).
      rewrite !evm_with_vm => <- //; last by SvD.fsetdec.
      apply/Sv.is_empty_spec; move/Sv.is_empty_spec: hwr.
      by rewrite /read_I_rec /write_I_rec /= read_rvE /read_gvar /=; SvD.fsetdec.
    have heqnw: evm s1' = vm3 [\ Sv.union (vrv lv) (vrvs lvs)].
    + move=> x hx; have /= <- := vrvsP hw3; last by SvD.fsetdec.
      rewrite -(vrvsP hws); last by SvD.fsetdec.
      by rewrite -(vrvP H3) //; SvD.fsetdec.
    have [vmi [hsemi heqv]]: exists vmi, write_lval (p_globs p') lv v' (with_vm s1' vm3) = ok (with_vm s1' vmi) /\ evm s1' =v vmi.
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
      rewrite (@get_var_eq_on (Sv.singleton x) (evm s1)); first last.
      + by move=> z hz; have := vrvsP hw3; rewrite !evm_with_vm => -> //; SvD.fsetdec.
      + by SvD.fsetdec.
      rewrite hget /=.
      have -> := sem_pexpr_noload_eq_on hnoload _ he; last first.
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
    have [vm4 []]:= sem_eqv hsem heqv.
    rewrite with_vm_idem => {hsem}hsem heqvm4.
    exists (with_vm s1' vm3), vm4; split.
    + by have -> // : s1 = (with_vm s3 (evm s1)); rewrite /with_vm -heqm; case: (s1).
    + by econstructor;eauto.
    by move=> x; rewrite (heqvm x) (heqvm4 x).
  Qed.

  Let Pi s1 (i:instr) s2:=
    forall (X:Sv.t) c', update_i is_reg_ptr fresh_id p (get_sig p) X i = ok c' ->
     Sv.Subset (Sv.union (read_I i) (write_I i)) X ->
     forall vm1, wf_vm vm1 -> evm s1 =[X] vm1 ->
     exists vm2, [/\ wf_vm vm2, evm s2 =[X] vm2 &
        sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2)].

  Let Pi_r s1 (i:instr_r) s2 :=
    forall ii, Pi s1 (MkI ii i) s2.

  Let Pc s1 (c:cmd) s2:=
    forall (X:Sv.t) c', update_c (update_i is_reg_ptr fresh_id p (get_sig p) X) c = ok c' ->
     Sv.Subset (Sv.union (read_c c) (write_c c)) X ->
     forall vm1, wf_vm vm1 -> evm s1 =[X] vm1 ->
     exists vm2, [/\ wf_vm vm2, evm s2 =[X] vm2 &
        sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2)].

  Let Pfor (i:var_i) vs s1 c s2 :=
    forall X c',
    update_c (update_i is_reg_ptr fresh_id p (get_sig p) X) c = ok c' ->
    Sv.Subset (Sv.add i (Sv.union (read_c c) (write_c c))) X ->
    forall vm1, wf_vm vm1 -> evm s1 =[X] vm1 ->
    exists vm2, [/\ wf_vm vm2, evm s2 =[X] vm2  &
      sem_for p' ev i vs (with_vm s1 vm1) c' (with_vm s2 vm2)].

  Let Pfun m fn vargs m' vres :=
    sem_call p' ev m fn vargs m' vres.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof.
    by move=> s X _ [<-] hs vm1 hvm1; exists vm1; split => //; constructor.
  Qed.

  Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ hi _ hc X c'; rewrite /update_c /=.
    t_xrbindP => lc ci {}/hi hi cc hcc <- <-.
    rewrite read_c_cons write_c_cons => hsub vm1 wf_vm1 hvm1.
    have [|vm2 [wf_vm2 hvm2 hs2]]:= hi _ vm1 wf_vm1 hvm1; first by SvD.fsetdec.
    have /hc : update_c (update_i is_reg_ptr fresh_id p (get_sig p) X) c = ok (flatten cc).
    + by rewrite /update_c hcc.
    move=> /(_ _ vm2 wf_vm2 hvm2) [|vm3 [wf_vm3 hvm3 hs3]]; first by SvD.fsetdec.
    by exists vm3; split => //=; apply: sem_app hs2 hs3.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by move=> ii i s1 s2 _ Hi X c' /Hi. Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x t ty e v v' he htr hw ii X c' [<-].
    rewrite read_Ii /write_I /write_I_rec vrv_recE read_i_assgn => hsub vm1 wf_vm1 hvm1.
    move: he; rewrite (read_e_eq_on _ (s := Sv.empty) (vm' := vm1)); last first.
    + by apply: eq_onI hvm1; rewrite read_eE; SvD.fsetdec.
    rewrite eq_globs => he; case: (write_lval_eq_on _ hw hvm1).
    + by SvD.fsetdec.
    move => vm2 [eq_s2_vm2 H_write_lval]; exists vm2; split.
    + by apply: (wf_write_lval _ H_write_lval).
    + by apply: (eq_onI _ eq_s2_vm2); SvD.fsetdec.
    by apply/sem_seq1/EmkI/(Eassgn _ _ he htr); rewrite -eq_globs.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es He ii X c' [<-].
    rewrite read_Ii read_i_opn /write_I /write_I_rec vrvs_recE => hsub vm1 wf_vm1 hvm1.
    move: He; rewrite eq_globs /sem_sopn Let_Let.
    t_xrbindP => vs Hsem_pexprs res Hexec_sopn hw.
    case: (write_lvals_eq_on _ hw hvm1); first by SvD.fsetdec.
    move=> vm2 [eq_s2_vm2 H_write_lvals]; exists vm2 ; split => //.
    + by apply: (wf_write_lvals _ H_write_lvals).
    + by apply: (eq_onI _ eq_s2_vm2); SvD.fsetdec.
    apply/sem_seq1/EmkI; constructor.
    rewrite /sem_sopn Let_Let - (@read_es_eq_on _ _ _ X) ; last first.
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
    move=> vm1 wf_vm1 eq_s1_vm1; case: (Hc X _ i_thenE _ vm1 wf_vm1 eq_s1_vm1).
    + by SvD.fsetdec.
    move=> vm2 [eq_s2_vm2 sem_i_then]; exists vm2; split=> //.
    apply/sem_seq1/EmkI; apply: Eif_true => //.
    rewrite - eq_globs -He.
    rewrite -(@read_e_eq_on _ _ Sv.empty) // -/(read_e _).
    by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 He Hs Hc ii X c' /=.
    t_xrbindP => i_then i_thenE i_else i_elseE {c'}<-.
    rewrite !(read_Ii, write_Ii) !(read_i_if, write_i_if) => le_X.
    move=> vm1 wf_vm1 eq_s1_vm1; case: (Hc X _ i_elseE _ vm1 wf_vm1 eq_s1_vm1).
    + by SvD.fsetdec.
    move=> vm2 [eq_s2_vm2 sem_i_else]; exists vm2; split=> //.
    apply/sem_seq1/EmkI; apply: Eif_false => //.
    rewrite - eq_globs -He.
    rewrite -(@read_e_eq_on _ _ Sv.empty) // -/(read_e _).
    by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' sem_s1_s2 H_s1_s2.
    move=> sem_s2_e sem_s2_s3 H_s2_s3 sem_s3_s4 H_s3_s4.
    move=> ii X c'' /=; t_xrbindP=> d dE d' d'E {c''}<-.
    rewrite !(read_Ii, write_Ii) !(read_i_while, write_i_while).
    move=> le_X vm1 wf_vm1 eq_s1_vm1.
    case: (H_s1_s2 X _ dE _ _ wf_vm1 eq_s1_vm1); first by SvD.fsetdec.
    move=> vm2 [wf_vm2 eq_s2_vm2 sem_vm1_vm2].
    case: (H_s2_s3 X _ d'E _ _ wf_vm2 eq_s2_vm2); first by SvD.fsetdec.
    move=> vm3 [wf_vm3 eq_s3_vm3 sem_vm2_vm3].
    case: (H_s3_s4 ii X [:: MkI ii (Cwhile a d e d')] _ _ vm3) => //=.
    + by rewrite dE d'E.
    + rewrite !(read_Ii, write_Ii) !(read_i_while, write_i_while).
      by SvD.fsetdec.
    move=> vm4 [wf_vm4 eq_s4_vm4 sem_vm3_vm4]; exists vm4; split=> //.
    apply/sem_seq1/EmkI; apply: (Ewhile_true sem_vm1_vm2 _ sem_vm2_vm3).
    + rewrite -(make_referenceprog_globs Hp) -sem_s2_e.
      rewrite -(@read_e_eq_on _ _ Sv.empty) // -/(read_e _).
      by apply: (eq_onI _ eq_s2_vm2); SvD.fsetdec.
    by elim/sem_seq1I: sem_vm3_vm4 => /sem_IE.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
   move=> s1 s2 a c e c' He Hc eq_s_e ii X c'' /=.
   t_xrbindP => while_false while_falseE c''' eq_c' <-.
   rewrite !(read_Ii, write_Ii) !(read_i_while, write_i_while).
   move => le_X vm1 wf_vm1 eq_s1_vm1.
   case: (Hc X _ while_falseE _ vm1 wf_vm1 eq_s1_vm1).
   + by SvD.fsetdec.
   move => vm2 [wf_vm2 eq_s2_vm2 sem_while_false].
   exists vm2 ; split => //.
   apply/sem_seq1/EmkI.
   apply Ewhile_false => //.
   rewrite -(make_referenceprog_globs Hp) - eq_s_e.
   rewrite -(@read_e_eq_on _ _ Sv.empty) // -/(read_e _).
   by apply: (eq_onI _ eq_s2_vm2) ; SvD.fsetdec.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    move => s1 x c X c' Hc le_X vm1 eq_s1_vm1.
    exists vm1 ; split => //.
    by constructor.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
    move => s1 s2 s3 s4 x w ws c eq_s2 sem_s2_s3 H_s2_s3 H_s3_s4 Pfor_s3_s4 X c'.
    move => eq_c' le_X vm1 wf_vm1 eq_s1_vm1.
    case : (write_var_eq_on eq_s2 eq_s1_vm1) => vm2 [eq_s2_vm2 eq_write].
    case : (H_s2_s3 X _ eq_c' _ vm2).
    + by SvD.fsetdec.
    + by apply: (wf_write_var _ eq_write).
    + by apply: (eq_onI _ eq_s2_vm2) ; SvD.fsetdec.
    move => vm3 [wf_vm3 eq_s3_vm3 sem_vm2_vm3].
    case : (Pfor_s3_s4 X _ eq_c' _ vm3 wf_vm3 eq_s3_vm3) => //.
    move => vm4 [wf_vm4 eq_s4_vm4 sem_vm3_vm4].
    exists vm4 ; split => //.
    by apply (EForOne eq_write sem_vm2_vm3 sem_vm3_vm4).
  Qed.

  Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 x d lo hi c vlo vhi cpl_lo cpl_hi cpl_for sem_s1_s2.
    move=> ii X c' /=; t_xrbindP=> {c'} c' c'E <-.
    rewrite !(read_Ii, write_Ii) !(read_i_for, write_i_for).
    move=> le_X vm1 wf_vm1 eq_s1_vm1.
    case: (sem_s1_s2 X _ c'E _ _ wf_vm1 eq_s1_vm1); first by SvD.fsetdec.
    move=> vm2 [wf_vm2 eq_s2_vm2 sem_vm1_vm2]; exists vm2.
    split=> //; apply/sem_seq1/EmkI/(Efor (vlo := vlo) (vhi := vhi)) => //.
    + rewrite -(make_referenceprog_globs Hp) -cpl_lo.
      rewrite -(@read_e_eq_on _ _ Sv.empty) // -/(read_e _).
      by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
    + rewrite - eq_globs -cpl_hi.
      rewrite -(@read_e_eq_on _ _ Sv.empty) // -/(read_e _).
      by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
  Qed.

  Lemma read_es_eq_on_sym
     (gd : glob_decls) (es : pexprs) (X : Sv.t) (s : estate) (vm vm' : vmap)
  :
     vm =[read_es_rec X es]  vm' ->
       sem_pexprs gd (with_vm s vm) es = sem_pexprs gd (with_vm s vm') es.
  Proof.
  by apply: @read_es_eq_on gd es X (with_vm s vm) vm'.
  Qed.

  Lemma read_e_eq_on_sym
     (gd : glob_decls) (e : pexpr) (X : Sv.t) (s : estate) (vm vm' : vmap)
  :
     vm =[read_e_rec X e]  vm' ->
       sem_pexpr gd (with_vm s vm) e = sem_pexpr gd (with_vm s vm') e.
  Proof.
  by apply: @read_e_eq_on gd X vm' (with_vm s vm) e.
  Qed.

  Definition make_prologue1_1 (pp : uprog) ii fty x e :=
    if   is_reg_ptr_expr is_reg_ptr fresh_id pp (v_var x) e is Some y
    then Some (MkI ii (Cassgn y AT_rename fty e))
    else None.

  Lemma get_set_var vm vm' x v v':
    ~is_sbool (vtype x) ->
    truncate_val (vtype x) v = ok v' ->
    set_var vm x v' = ok vm' ->
    get_var vm' x = ok v'.
  Proof.
    rewrite /get_var /set_var => hty htr; apply on_vuP; last by case: is_sbool hty.
    move=> vt hvt <-.
    rewrite /on_vu Fv.setP_eq.
    case: (vtype x) vt htr hvt => /=.
    + by move=> b _ /to_boolI ->.
    + by move=> i _ /to_intI ->.
    + move=> n t; case: v => //= n' t'.
      by rewrite /truncate_val /=; t_xrbindP => t1 hc <-; rewrite /to_arr WArray.castK => -[->].
    move => w vt; rewrite /truncate_val /=; t_xrbindP => w' h <-.
    rewrite /to_pword.
    assert (h1 := cmp_le_refl w); case: Sumbool.sumbool_of_bool; last by rewrite h1.
    by move=> h2 [<-] /=.
  Qed.

  Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 m s2 ii lv fn args vargs aout eval_args h1 h2 h3.
    move=> ii' X c' hupd; rewrite !(read_Ii, write_Ii).
    rewrite !(read_i_call, write_i_call) => le_X vm1 wf_vm1 eq_s1_vm1.
    case/sem_callE: h1 hupd => fnd [fnE] [vs] [s1'] [s2'] [s3'] [vres].
    case=> vsE /= [[{s1'}<-] hwrinit] sem_body [vresE aoutE] mE.
    subst m; rewrite /(get_sig p) fnE.
    t_xrbindP=> -[pl eargs] plE; t_xrbindP=> -[lvaout ep] epE.
    move => [] <-.
    have eqglob: p_globs p = p_globs p'.
    + by apply: make_referenceprog_globs.
    have : exists vmx vargs', [/\
        wf_vm vmx
      , sem p' ev (with_vm s1 vm1) pl (with_vm s1 vmx)
      , sem_pexprs (p_globs p') (with_vm s1 vmx) eargs = ok vargs'
      , mapM2 ErrType truncate_val (f_tyin fnd) vargs' = ok vs
      & vm1 =[X] vmx].
    + move=> {epE lvaout ep aoutE vresE sem_body vres h3 h2 fnE s3' aout}.
      have: (Sv.Subset X X) by SvD.fsetdec.
      move: {1 3 4}X plE => Y plE le_XY.
      move: plE vargs vs le_XY vmap0 vm1 wf_vm1 eq_s1_vm1 s2' le_X eval_args vsE hwrinit.
      elim/make_prologueW => {Y args pl eargs} Y.
      - move=> _ _ _ vmap0 vm1 wf_vm1 _ _ /= _ [<-] /= [<-] _.
        by exists vm1, [::]; split=> // ; constructor.
      - move=> x xs fty ftys pe pes c args eq_ptr_expr eq_mk_prologue ih.
        move=> vargs' vs' subXY vmap0 vm1 wf_vm1 eq_s1_vm1 s2' subUX.
        rewrite [X in X -> _]/=; t_xrbindP=> v vE vargs vargsE ?; subst vargs'.
        rewrite [X in X -> _]/=; t_xrbindP=> vt vtE vs vsE ?; subst vs'.
        rewrite [X in X -> _]/=; t_xrbindP=> svm0' wr_init1 wr_init.
        have [vm0' ?]: exists vm0', svm0' = with_vm s1 vm0'; last subst svm0'.
        * move: wr_init1; rewrite /write_var; t_xrbindP.
          by move=> vm0' h <-; exists vm0'.
        case: (ih vargs vs subXY vm0' vm1 wf_vm1 _ s2') => //.
        * by move: subUX; rewrite read_es_cons; SvD.fsetdec.
        * move=> vmx [vargs'] [ih0 ih1 ih2 ih3 ih4]; exists vmx, (v :: vargs'); split => //=.
          + rewrite [X in Let _ := X in _](_ : _ = ok v) 1?ih2 //=.
            rewrite -vE  eq_globs; apply: eq_on_sem_pexpr => //=.
            apply/eq_onS/(@eq_onI _ _ X).
            - by move: subUX; rewrite read_es_cons; SvD.fsetdec.
            - by apply: (eq_onT eq_s1_vm1); apply: eq_onI ih4.
          + by rewrite vtE /= ih3.
      - move=> x xs fty ftys pe pes y c args eq_fty notB_fty notM_y_Y.
        move=> eq_ptr_expr eq_mk_prologue ih.
        move=> vargs' vs' subXY vmap0 vm1 wf_vm1 eq_s1_vm1 s2' subUX.
        move: subUX; rewrite read_es_cons => subUX.
        rewrite [X in X -> _]/=; t_xrbindP=> v vE vargs vargsE ?; subst vargs'.
        rewrite [X in X -> _]/=; t_xrbindP=> vt vtE vs vsE ?; subst vs'.
        rewrite [X in X -> _]/=; t_xrbindP=> svm0' wr_init1 wr_init.
        have [vm0' ?]: exists vm0', svm0' = with_vm s1 vm0'; last subst svm0'.
        * move: wr_init1; rewrite /write_var; t_xrbindP.
          by move=> vm0' h <-; exists vm0'.
        have [vmx' [wf_vmx' hvmx']]: exists vmx', wf_vm vmx' /\ write_var y vt (with_vm s1 vm1) = ok (with_vm s1 vmx').
        * move: wr_init1; rewrite /write_var /=; t_xrbindP.
          move=> vm0'' vm0'E ?; subst vm0''.
          have /(_ vm1)[] := set_var_rename (y := y) _ _ vm0'E.
          - move: eq_ptr_expr; rewrite /is_reg_ptr_expr ; case: (pe) => //.
            + by move=> g; case: ifP => // _ [<-].
            + by move=> _ _ _ g _ [<-].
          by move=> vmx' vmx'E; exists vmx' ; split ; [apply (wf_set_var wf_vm1 vmx'E)|rewrite vmx'E].
        have [] := ih vargs vs _ vm0' vmx' wf_vmx' _ s2' => //.
        * by SvD.fsetdec.
        * apply: (eq_onT eq_s1_vm1); move/vrvP_var: hvmx'.
          move/vmap_eq_except_eq_on=> /= /(_ vmx' X (fun _ _ => erefl _)).
          by apply: eq_onI; move/Sv_memP: notM_y_Y; SvD.fsetdec.
        * by SvD.fsetdec.
        move=> vmx'' [vargs'] [ih0 ih1 ih2 ih3 ih4]; exists vmx'', (vt :: vargs'); split=> //=.
        * rewrite -cat1s; apply/(sem_app _ ih1)/sem_seq1/EmkI/Eassgn; first 2 last.
          + by apply: hvmx'.
          + rewrite -eqglob -(@read_e_eq_on _ _ X).
            - by apply: vE.
            - apply: (@eq_onI _ _ X); first by rewrite read_eE; SvD.fsetdec.
              by apply : (eq_onT eq_s1_vm1).
          + by done.
        * rewrite /get_gvar /= -(get_var_eq_on _ ih4); last by SvD.fsetdec.
          move: hvmx'; rewrite /write_var; t_xrbindP=> vmx3 vmx'E ?; subst vmx3.
          rewrite eq_fty in notB_fty, vtE.
          by have ->/= := get_set_var (negP notB_fty) vtE vmx'E; rewrite ih2.
        * by rewrite (truncate_val_idem vtE) /= ih3.
        * apply: (@eq_onT _ _ vmx'); last by apply: (eq_onI _ ih4); SvD.fsetdec.
          move/vrvP_var: hvmx' => /vmap_eq_except_eq_on.
          move/(_ vmx' Y (fun _ _ => erefl _)).
          by apply: eq_onI; move/Sv_memP: notM_y_Y; SvD.fsetdec.

    case=> [vmx] [vargs'] [wf_vmx sem_pl eval_vargs' trunc_vargs' eq_vm1_vmx].

    case: (get_map_cfprog_gen eq_funcs fnE) => fdef Hfdef Hget_fundef.

    have Hep:
    exists vm2 s2', [/\
         wf_vm vm2
       , write_lvals (p_globs p') (with_vm s3' vmx) lvaout aout = ok s2'
       , sem p' ev s2' ep (with_vm s2 vm2)
       & evm s2 =[X] vm2].
    + move=> {vs vsE hwrinit trunc_vargs' vargs' eval_args eval_vargs' eargs pl plE fnE}
             {sem_pl fdef Hfdef Hget_fundef h2 sem_body vargs}.
      move : epE.
      rewrite /make_epilogue.
      t_xrbindP => pinstrs Hpseudo Hswap.
      have le_X' : Sv.Subset (Sv.union (read_rvs lv) (vrvs lv)) X by SvD.fsetdec.
      have eq_evm : evm (with_mem s1 (emem s3')) =[X] evm (with_vm s3' vmx) by apply: (eq_onT eq_s1_vm1).
      case : (make_pseudo_codeP Hpseudo _ aoutE le_X' h3 eq_evm).
      - by rewrite /=.
      move => vm2 ; rewrite evm_with_vm => - [wf_vm2 Hsem_pis eq_s2_vm2].
      case : (swapableP Hswap Hsem_pis).
      move => sy [vmy] [Hwrite_lvals Hsem].
      move => /= eq_vm2_vmy.
      exists vmy, sy ; split => //.
      - have := (wf_sem Hsem).
        have := (wf_write_lvals _ Hwrite_lvals).
        rewrite /=.
        by move => wf_imp1 wf_imp2 ; apply wf_imp2 ; apply wf_imp1.
      move => z Hz.
      by rewrite eq_s2_vm2.

    case : Hep => vm2 [s3] [wf_vm2 Hwr_lvals Hsem eq_s2_vm2].


    exists vm2.
    split => //.
    apply : (sem_app sem_pl).
    apply : (Eseq _ Hsem).
    apply : EmkI.
    econstructor.
    + by apply eval_vargs'.
    2 : by apply Hwr_lvals.
    case/sem_callE: h2 => f [] H [] ? [] ? [] ? [] ? [] ? [] H0 [] ? ? ? [] ? ? ?.
    econstructor ; eauto.
    move : vsE trunc_vargs'.
    have : f_tyin fnd = f_tyin f.
    + move : (p_funcs p) (p_funcs p') (size_mapM eq_funcs) eq_funcs fnE H.
      apply : diagonal_induction_2_eq => //= [[hfp1 hfp2] [hfp'1 hfp'2]] tfp tfp' eq_size_tfp ih.
      t_xrbindP => y h.
      case Hupdate_fd : (update_fd _ _ _ _ _) => //= - [] hh.
      rewrite hh in Hupdate_fd.
      move => ?; subst y.
      move => tfp'c Hmap_cfprog [? ?] ? ; subst hfp'1 ; subst hfp'2 ; subst tfp'c.
      case : (fn == hfp1) ; last by apply : ih.
      move => [?] [?] ; subst fnd ; subst f.
      move : Hupdate_fd.
      by rewrite /update_fd ; t_xrbindP => c _ <-.
    move => ->.
    by rewrite H0 => - [] ->.
  Qed.

  Lemma eq_extra : p_extra p = p_extra p'.
    move : Hp.
    rewrite /makereference_prog.
    by t_xrbindP => y Hmap <-.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> m1 m2 fn f vargs vargs' s0 s1 s2 vres vres' Hf Hvargs.
    move=> Hs0 Hs1 Hsem_s2 Hs2 Hvres Hvres' Hm2.
    have H := (all_progP _ Hf).
    rewrite eq_extra in Hs0.
    rewrite /Pfun.
    move : Hp.
    rewrite /makereference_prog.
    t_xrbindP => y Hmap ?.
    subst p'.
    case : (get_map_cfprog_gen Hmap Hf) => x Hupdate Hy.
    move : Hupdate.
    rewrite /update_fd.
    t_xrbindP => z Hupdate_c Hwith_body.
    subst x => /=.
    have [] := (Hs2 _ _ Hupdate_c _ (evm s1)) => //.
    + by SvD.fsetdec.
    + apply: (wf_write_vars _ Hs1); move: Hs0.
      by rewrite /init_state /= => -[<-]; apply: wf_vmap0.
    move => x [wf_x Hevms2 Hsem].
    rewrite with_vm_same in Hsem.
    eapply EcallRun ; try by eassumption.
    rewrite - Hvres -! (@sem_pexprs_get_var _ (p_globs p)).
    symmetry.
    move : Hevms2.
    rewrite - read_esE.
    by apply : read_es_eq_on.
  Qed.

  Lemma makeReferenceArguments_callP f mem mem' va vr:
    sem_call p ev mem f va mem' vr ->
    sem_call p' ev mem f va mem' vr.
  Proof.
    move=> Hsem.
    apply (@sem_call_Ind _ _ _ _ _ _ p ev Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
               Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc
               mem f va mem' vr Hsem).
  Qed.

End Section.
