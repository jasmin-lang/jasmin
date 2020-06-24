(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

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
Context (T : eqType) (pT : progT T) (cs : semCallParams).
Context (p : prog) (ev : extra_val_t).

Derive Inversion_clear sem_nilI
  with (forall s1 s2,  @sem T pT cs p ev s1 [::] s2)
  Sort Prop.

Derive Inversion_clear sem_consI
  with (forall s1 i c s2,  @sem T pT cs p ev s1 (i :: c) s2)
  Sort Prop.

Lemma set_var_rename (vm vm' vm'' : vmap) (x y : var) (v : value) :
     vtype x = vtype y
  -> set_var vm x v = ok vm'
  -> exists vm''', set_var vm'' y v = ok vm'''.
Proof.
case: x y => [ty nx] [_ ny] [/= <-].
set x := {| vname := nx |}; set y := {| vname := ny |}.
apply: set_varP => /=.
+ by move=> t okt /esym vm'E ; exists vm''.[y <- ok t] ; rewrite /set_var okt.
+ move=> tybool tyvE /esym vm'E; exists vm''.[y <- pundef_addr ty].
  by rewrite /set_var tybool tyvE.
Qed.

Section SemInversionSeq1.
  Context (s1 : estate) (i : instr) (s2 : estate).
  Context
    (P : ∀ (T : eqType) (pT : progT T),
           semCallParams → prog -> extra_val_t -> estate -> instr -> estate -> Prop).

  Hypothesis Hi :
    (sem_I p ev s1 i s2 -> @P T pT cs p ev s1 i s2).

  Lemma sem_seq1I : sem p ev s1 [:: i] s2 → @P T pT cs p ev s1 i s2.
  Proof.
  by elim/sem_consI=> s hs h_nil; elim/sem_nilI: h_nil hs => /Hi.
  Qed.
End SemInversionSeq1.
End SemInversion.

Section Section.
  Context (is_reg_ptr : var -> bool) (fresh_id : glob_decls -> var -> Ident.ident).

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
  + t_xrbindP=> /= _ /assertP /and3P[/eqP h1 h2 h3] [c' args'].
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

  Context (p p' : uprog).
  Context (ev : unit).

  Hypothesis Hp : makereference_prog is_reg_ptr fresh_id p = ok p'.

  Lemma eq_globs : p_globs p = p_globs p'.
  Proof.
   case : p Hp => /= p_funcs p_globs extra.
   rewrite /makereference_prog.
   t_xrbindP => /=.
   by move => y _ <-.
  Qed.

  Definition get_sig n :=       (* FIXME: duplicated *)
   if get_fundef p.(p_funcs) n is Some fd then
      (fd.(f_params), fd.(f_tyin), fd.(f_res), fd.(f_tyout))
   else ([::], [::], [::], [::]).

  Let Pi s1 (i:instr) s2:=
    forall (X:Sv.t) c', update_i is_reg_ptr fresh_id p get_sig X i = ok c' ->
     Sv.Subset (Sv.union (read_I i) (write_I i)) X ->
     forall vm1, wf_vm vm1 -> evm s1 =[X] vm1 ->
     exists vm2, [/\ wf_vm vm2, evm s2 =[X] vm2 &
        sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2)].

  Let Pi_r s1 (i:instr_r) s2 :=
    forall ii, Pi s1 (MkI ii i) s2.

  Let Pc s1 (c:cmd) s2:=
    forall (X:Sv.t) c', update_c (update_i is_reg_ptr fresh_id p get_sig X) c = ok c' ->
     Sv.Subset (Sv.union (read_c c) (write_c c)) X ->
     forall vm1, wf_vm vm1 -> evm s1 =[X] vm1 ->
     exists vm2, [/\ wf_vm vm2, evm s2 =[X] vm2 &
        sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2)].

  Let Pfor (i:var_i) vs s1 c s2 :=
    forall X c',
    update_c (update_i is_reg_ptr fresh_id p get_sig X) c = ok c' ->
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
    have /hc : update_c (update_i is_reg_ptr fresh_id p get_sig X) c = ok (flatten cc).
    + by rewrite /update_c hcc.
    move=> /(_ _ vm2 wf_vm2 hvm2) [|vm3 [wf_vm3 hvm3 hs3]]; first by SvD.fsetdec.
    by exists vm3; split => //=; apply: sem_app hs2 hs3.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by move=> ii i s1 s2 _ Hi X c' /Hi. Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x t ty e v v' he htr hw ii X c' [<-].
    rewrite read_Ii /write_I /= vrv_recE read_i_assgn => hsub vm1 wf_vm1 hvm1.
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
    rewrite read_Ii read_i_opn /write_I /= vrvs_recE => hsub vm1 wf_vm1 hvm1.
    move: He; rewrite eq_globs /sem_sopn Let_Let.
    t_xrbindP => vs Hsem_pexprs res Hexec_sopn hw.
    case: (write_lvals_eq_on _ hw hvm1); first by SvD.fsetdec.
    move=> vm2 [eq_s2_vm2 H_write_lvals]; exists vm2 ; split => //.
    + by apply: (wf_write_lvals _ H_write_lvals).
    + by apply: (eq_onI _ eq_s2_vm2); SvD.fsetdec.
    apply/sem_seq1/EmkI; constructor.
    rewrite /sem_sopn Let_Let - (@read_es_eq_on _ _ X) ; last first.
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
    rewrite -(@read_e_eq_on _ Sv.empty) // -/(read_e _).
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
    rewrite -(@read_e_eq_on _ Sv.empty) // -/(read_e _).
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
      rewrite -(@read_e_eq_on _ Sv.empty) // -/(read_e _).
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
   rewrite -(@read_e_eq_on _ Sv.empty) // -/(read_e _).
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
      rewrite -(@read_e_eq_on _ Sv.empty) // -/(read_e _).
      by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
    + rewrite - eq_globs -cpl_hi.
      rewrite -(@read_e_eq_on _ Sv.empty) // -/(read_e _).
      by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
  Qed.

  Lemma mapM_size {eT aT bT : Type} (f : aT -> result eT bT) xs ys :
    mapM f xs = ok ys -> size xs = size ys.
  Proof.
  elim: xs ys => /= [|x xs ih] ys; first by case: ys.
  by t_xrbindP=> v _ vs /ih -> <-.
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

  Lemma size_mapM (E A B : Type) (f : (A → result E B)) v1 v2:
    mapM f v1 = ok v2 ->
    size v1 = size v2.
  Proof. by elim: v1 v2 => [ | x xs ih ] /= [] // ; t_xrbindP => // ????? /ih -> _ ->. Qed.

  Lemma size_mapM2 (A B E R : Type) (e : E) (f : (A → B → result E R)) v1 v2 v3:
    mapM2 e f v1 v2 = ok v3 ->
    size v1 = size v3 /\ size v2 = size v3.
  Proof.
   elim: v1 v2 v3 => [ | x xs ih ] [|y ys] [|z zs] //= ; t_xrbindP => // t eqt ts /ih.
   by case => -> -> _ ->.
  Qed.

  Lemma size_fold2 (A B E R : Type) (e: E) (f : (A → B → R → result E R)) xs ys x0 v:
    fold2 e f xs ys x0 = ok v -> size xs = size ys.
  Proof.
    by elim : xs ys x0 => [|x xs ih] [|y ys] x0 //= ; t_xrbindP => // t _ /ih ->.
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
    + move=> n t; case: v => //= [ n' t' | [] //]. 
      rewrite /truncate_val /= /WArray.cast.
      by case: ifP => //= ? [<-] /= [<-]; rewrite /WArray.inject Z.ltb_irrefl.
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
    subst m; rewrite /get_sig fnE.
    t_xrbindP=> -[pl eargs] plE; t_xrbindP=> -[ep lvaout] epE [<-] {c'}.

    have eqglob: p_globs p = p_globs p'.
    + by apply: make_referenceprog_globs.

    have : exists vmx vargs', [/\
        sem p' ev (with_vm s1 vm1) pl (with_vm s1 vmx)
      , sem_pexprs (p_globs p') (with_vm s1 vmx) eargs = ok vargs'
      , mapM2 ErrType truncate_val (f_tyin fnd) vargs' = ok vs
      & vm1 =[X] vmx].

    + move=> {epE lvaout ep aoutE vresE sem_body vres h3 h2 fnE wf_vm1 s3' aout}.
      have: (Sv.Subset X X) by SvD.fsetdec.
      move: {1 3}X plE => Y plE le_XY.
      move: plE vargs vs le_XY vmap0 le_X eval_args vsE hwrinit.
      elim/make_prologueW=> {Y args pl eargs} Y.
      - by move=> _ _ _ vmap0 /= _ [<-] /= [<-] _; exists vm1, [::]; split=> //; constructor.
      - move=> x xs fty ftys pe pes c args eq_ptr_expr eq_mk_prologue ih.
        move=> vargs' vs' subXY vmap0 subUX.
        rewrite [X in X -> _]/=; t_xrbindP=> v vE vargs vargsE ?; subst vargs'.
        rewrite [X in X -> _]/=; t_xrbindP=> vt vtE vs vsE ?; subst vs'.
        rewrite [X in X -> _]/=; t_xrbindP=> svm0' wr_init1 wr_init.
        have [vm0' ?]: exists vm0', svm0' = with_vm s1 vm0'; last subst svm0'.
        + move: wr_init1; rewrite /write_var; t_xrbindP.
          by move=> vm0' h <-; exists vm0'.
        case: (ih vargs vs subXY vm0') => //.
        + by move: subUX; rewrite read_es_cons; SvD.fsetdec.
        + move=> vmx [vargs'] [ih1 ih2 ih3 ih4]; exists vmx, (v :: vargs'); split => //=.
          * rewrite [X in Let _ := X in _](_ : _ = ok v) 1?ih2 //=.
            rewrite -vE  eq_globs; apply: eq_on_sem_pexpr => //=.
            apply/eq_onS/(@eq_onI _ X).
            - by move: subUX; rewrite read_es_cons; SvD.fsetdec.
            - by apply: (eq_onT eq_s1_vm1).
          * by rewrite vtE /= ih3.










































    + move=> {uq_ep fs_ep epE lvaout ep aoutE vresE sem_body vres h3 h2 c' fnE wf_vm1 s3' aout}.
      move: plE uq_pl fs_pl; rewrite [X in X = (pl, eargs)]surjective_pairing => -[].
      have [eqsz1 eqsz2] := (size_mapM2 vsE).
      have eqsz3:= (size_fold2 hwrinit).
      have eqsz4 := (size_mapM eval_args).
      have eqzs5 : size (f_tyin fnd) = size (f_params fnd) by rewrite eqsz1 -eqsz3.
      rewrite !(make_prologueE1, make_prologueE2_same_size) //; last first.
      - by rewrite eqsz3 eqsz4 eqsz2.
      move=> /esym -> /esym -> {pl eargs}.

      move: vmap0 le_X eval_args vsE hwrinit.
      have: size (f_params fnd) = size (f_tyin fnd).
      - by rewrite eqsz3 eqsz1.
      have: size vs = size (f_params fnd).
      - by rewrite eqsz3.
      move : eqsz4 eqsz2.
      move => {eqsz1 eqsz3}.
      move: args vargs vs (f_params fnd) (f_tyin fnd); move: s2' => vminit.
      apply: diagonal_induction_5_eq.
      + by move=> vm0 _ _ _ _ _ _; exists vm1, [::]; split=> //; constructor.
      move=> arg1 varg1 v1 f_param1 f_tyin1 args vargs vs f_params f_tyins.
      move=> eqsz1 eqsz2 eqsz3 eqsz4 ih vm0 le_X eval_args trunc_vargs wr_init.
      move=> uq_pl fresh_pl; move: eval_args; rewrite [_ = ok (varg1 :: _)]/=; t_xrbindP.
      move=> varg1' eval_arg1 vargs' eval_args ??; subst varg1' vargs'.
      move: trunc_vargs; rewrite [_ = ok (v1 :: _)]/=; t_xrbindP.
      move=> v1' trunc_varg1 vs' trunc_vargs ??; subst v1' vs'.
      move: wr_init; rewrite [_ = ok vminit]/=; t_xrbindP=> svm0' wr_init1 wr_init.
      have [vm0' ?]: exists vm0', svm0' = with_vm s1 vm0'; last subst svm0'.
      + move: wr_init1; rewrite /write_var; t_xrbindP.
        by move=> vm0' h <-; exists vm0'.
      move: le_X; rewrite read_es_cons => le_X.
      case hE: (is_reg_ptr_expr is_reg_ptr fresh_id p f_param1 arg1) => [y|]; last first.

(**)
      + move: uq_pl fresh_pl; rewrite [pmap _ _]/=.
        rewrite [X in oapp _ _ X]/make_prologue1_1 hE [oapp _ _ _]/=.
        move=> uq_pl fresh_pl. case: (ih vm0') => //.
        * by SvD.fsetdec.
        move=> vmx [vargs'] [ih1 ih2 ih3 ih4]; exists vmx, (varg1 :: vargs'); split => //=.
        * rewrite {2}/make_prologue1_2 hE -!eq_globs.
          rewrite [X in Let _ := X in _](_ : _ = ok varg1) /=.
          - by rewrite eq_globs ih2.
          rewrite -eval_arg1; apply: eq_on_sem_pexpr => //=.
          apply/eq_onS/(@eq_onI _ X).
          - by SvD.fsetdec.
          - by apply: eq_onT ih4.
        * by rewrite trunc_varg1 /= ih3.
(**)

      + move: uq_pl fresh_pl; rewrite [pmap _ _]/=.
        rewrite [X in oapp _ _ X]/make_prologue1_1 hE [oapp _ _ _]/=.
        rewrite fresh_vars_in_prologueE rev_uniq rev_cons.
        rewrite -cats1 pmap_cat uniq_catC [uniq _]/= => /andP[].
        rewrite -mem_rev -rev_uniq -!fresh_vars_in_prologueE.
        set S := rev _ => y_fresh pl_uniq fresh_pl. case: (ih vm0') => //=.
        * by SvD.fsetdec.
        * rewrite -/S => x hx; apply: fresh_pl.
          by rewrite rev_cat mem_cat -!fresh_vars_in_prologueE hx orbT.
        move=> vmx [vargs'] [ih1 ih2 ih3 ih4].
        have [vmx' hvmx']: exists vmx', write_var y v1 (with_vm s1 vmx) = ok (with_vm s1 vmx').
        * move: wr_init1; rewrite /write_var /=; t_xrbindP.
          move=> vm0'' vm0'E ?; subst vm0''.
          have /(_ vmx)[] := set_var_rename (y := y) _ _ vm0'E.
          - move: hE; rewrite /is_reg_ptr_expr; case: (arg1) => //.
            + by move=> g; case: ifP => // _ [<-].
            + by move=> _ _ _ g _ [<-].
          by move=> vmx' vmx'E; exists vmx'; rewrite vmx'E.
        exists vmx', (v1 :: vargs'); split=> //.
        * apply/(sem_app ih1)/sem_seq1/EmkI/Eassgn; first 2 last.
          + by apply: hvmx'.
          + rewrite -eqglob -(@read_e_eq_on _ X).
            - by apply: eval_arg1.
            - apply : (@eq_onI _ X); first by rewrite read_eE; SvD.fsetdec.
              by apply : (eq_onT eq_s1_vm1).
          + done.
        * rewrite {2}/make_prologue1_2 hE /=.
          have ->/=: get_gvar (p_globs p') vmx' (mk_lvar y) = ok v1.
          + move: hvmx'; rewrite /write_var; t_xrbindP=> /= vmx'' vmx'E ?; subst vmx''.
            have /(_ varg1) := (get_set_var _ _ vmx'E); apply.
            * admit.
            * admit.
          rewrite (@eq_on_sem_pexprs (with_vm s1 vmx)) //=; first by rewrite ih2.
          set Y := (X in _ =[X] _); suff yNY: ~ (Sv.In y Y).
          + move/vrvP_var: hvmx' => /= hvmx'.
            have /(_ Y)/eq_onS := vmap_eq_except_eq_on hvmx' (fun x _ => (erefl _)).
            by apply: eq_onI; SvD.fsetdec.
          apply/Sv_memP; have: ~~ Sv.mem y X.
          + by apply: fresh_pl; rewrite mem_rev mem_cat /= mem_seq1 eqxx orbT.
          apply: contra; move: le_X y_fresh; rewrite /S /Y fresh_vars_in_prologueE.
          have: size f_tyins = size args.
          + by rewrite -eqsz4 -eqsz3 -eqsz2 -eqsz1.
          move: (f_params) (f_tyins) (args) (eqsz4).
          apply: diagonal_induction_3_eq => //=.
          move=> param1 fty1 arg'1 params ftys args' eq1 eq2 {ih}ih le_X.
          case E: (is_reg_ptr_expr is_reg_ptr fresh_id p param1 arg'1) => [z|].
          + rewrite [_ arg'1]/make_prologue1_1 [X in read_es (X :: _)]/make_prologue1_2 E /=.
            rewrite mem_rev rev_cons -cats1 pmap_cat mem_cat negb_or -mem_rev.
            case/andP => {}/ih ih /=; rewrite mem_seq1 => ne_yz.
            rewrite read_es_cons SvP.union_mem; case/orP.
            - rewrite SvP.union_mem /read_gvar /= SvP.empty_mem orbF.
              by move/SvP.singleton_mem_3/esym/eqP; rewrite (negbTE ne_yz).
            - by apply: ih; move: le_X; rewrite read_es_cons; SvD.fsetdec.
          + rewrite [_ arg'1]/make_prologue1_1 [X in read_es (X :: _)]/make_prologue1_2 E /=.
            move=> {}/ih ih; rewrite read_es_cons SvP.union_mem; case/orP.
            - move: le_X; rewrite read_es_cons => le_X.
              by move/Sv_memP=> ?; apply/Sv_memP; SvD.fsetdec.
            - by apply: ih; move: le_X; rewrite read_es_cons; SvD.fsetdec.
        * by move/truncate_val_idem: trunc_varg1 => -> /=; rewrite ih3.
        * apply: (eq_onT ih4); have /= /vmap_eq_except_eq_on := vrvP_var hvmx'.
          move/(_ vmx' X (fun _ _ => (erefl _))); apply/eq_onI.
          suff: ~(Sv.In y X) by SvD.fsetdec. move/Sv_memP; apply/negP.
          by apply: fresh_pl; rewrite mem_rev /= mem_cat mem_seq1 eqxx orbT.

  Admitted.

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
    case : (get_map_cfprog Hmap Hf) => x Hupdate Hy.
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
    rewrite - Hvres -! (@sem_pexprs_get_var (p_globs p)).
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
    apply (@sem_call_Ind _ _ _ p ev Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
               Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc
               mem f va mem' vr Hsem).
  Qed.

End Section.
