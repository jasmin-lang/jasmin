From HB Require Import structures.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg word_ssrZ.
Require Import compiler_util psem psem_facts safety safety_shared_proof.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

Section SAFETY_PROOF.
#[local] Existing Instance progUnit.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

#[local] Existing Instance sCP_unit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.
#[local] Existing Instance withassert.
Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Variable (p :uprog) (ev:extra_val_t).

Notation gd := (p_globs p).
Notation sem_pexpr_wc := (sem_pexpr (wc:=withcatch)).
Notation sem_pexprs_wc := (sem_pexprs (wc:=withcatch)).
Notation sem_cond_wc := (sem_cond (wc:=withcatch)).
Notation write_lvals_wc := (write_lvals (wc:=withcatch)).

(* ----- Aux Lemmas ----- *)
Lemma gvar_init_arr s x len :
  vtype (gv x) = sarr len ->
  sem_cond gd (eands (sc_gvar x)) s = ok true.
Proof. by move=> h; rewrite /sc_gvar /sc_var h; case: ifP. Qed.

Lemma var_init_arr s (x: var_i) len :
  vtype x = sarr len ->
  sem_cond gd (eands (sc_var x)) s = ok true.
Proof. by move=> h; rewrite /sc_var h. Qed.

Lemma sc_is_aligned_ifP s (i : sem_t sint) al aa sz e :
  sem_pexpr_wc true gd s e = ok (to_val i) ->
  sem_cond_wc gd (eands (sc_is_aligned_if al aa sz e)) s = ok true ->
  is_aligned_if (Pointer := WArray.PointerZ) al (i * mk_scale aa sz) sz.
Proof.
  rewrite /sc_is_aligned_if /is_aligned_if => hi.
  case: al => //=.
  case: aa => /=.
  + rewrite Z.mul_1_r /sem_cond /=.
     by rewrite hi.
  by move=> _; apply WArray.is_align_scale.
Qed.

Lemma sc_in_boundP s len (i ilen : sem_t sint) aa sz (e elen : pexpr) :
  sem_pexpr_wc true gd s e = ok (to_val i) ->
  sem_pexpr_wc true gd s elen = ok (to_val ilen) ->
  sem_cond_wc gd (eands (sc_in_bound (sarr len) aa sz e elen)) s = ok true ->
  (0 <= i * mk_scale aa sz /\ i * mk_scale aa sz + ilen <= len)%Z.
Proof.
  rewrite /sc_in_bound /= /emk_scale /emuli /sem_cond => he helen /=.
  case: aa => /=; rewrite helen he => /= -[]/andP [/ZleP h1 /ZleP h2]; Lia.lia.
Qed.

Lemma sc_in_boundP_all s len (t : sem_t (sarr len)) (i: sem_t sint) aa sz e :
  sem_pexpr_wc true gd s e = ok (to_val i) ->
  sem_cond_wc gd (eands(sc_in_bound (sarr len) aa sz e (Pconst(wsize_size sz)))) s = ok true ->
  all (fun j => WArray.in_bound t (i * mk_scale aa sz + j)) (ziota 0 (wsize_size sz)).
Proof.
  move=> he hscs.
  have helen : sem_pexpr (wc:=withcatch) true gd s (Pconst (wsize_size sz)) =
                 ok (to_val (t:=sint) (wsize_size sz)) by done.
  have [h1 h2] := sc_in_boundP he helen hscs.
  apply /allP => j /in_ziotaP ?; apply/WArray.in_boundP; Lia.lia.
Qed.

Lemma sc_in_sub_boundP s len (t : sem_t (sarr len)) a e1 e2 (ve1 ve2: Z) :
  sem_pexpr_wc true gd s e1 = ok (Vint ve1) ->
  sem_pexpr_wc true gd s e2 = ok (Vint ve2) ->
  0 <= a < ve2 ->
  sem_cond_wc gd (eands (sc_in_bound' (sarr len) e1 e2)) s = ok true ->
  WArray.in_bound t ((ve1 + a)).
Proof.
  move=> he1 he2 hb.
  have {}hb : ve1 <= ve1 + a < ve1 + ve2 by Lia.lia.
  rewrite /sem_cond /= he1 he2 /=.
  move=> []/andP [/Z.leb_le hlo /Z.leb_le hhi].
  rewrite/ WArray.in_bound; apply/andP; split.
  + apply/Z.leb_le; Lia.lia.
  apply/Z.ltb_lt; Lia.lia.
Qed.

Section GLOBALS.

(* FIXME : this require a check *)
Hypothesis get_global_arr_init :
  forall x len (t:WArray.array len) ,
  get_global gd x = ok (Varr t) →
  all (WArray.is_init t) (ziota 0 len).

Opaque wsize_size.

Lemma sc_arr_initP s len (t : WArray.array len) (i : sem_t sint) x aa sz e :
  sem_pexpr_wc true gd s e = ok (to_val i) ->
  get_gvar true gd (evm s) x = ok (Varr t) ->
  sem_cond_wc gd (eands (sc_arr_init (sarr len) x aa sz e)) s = ok true ->
  all (fun j => WArray.in_bound t (i * mk_scale aa sz + j)) (ziota 0 (wsize_size sz)) ->
  all (fun j => WArray.is_init t (i * mk_scale aa sz + j)) (ziota 0 (wsize_size sz)).
Proof.
  rewrite /sem_cond.
  rewrite /sc_arr_init /get_gvar /emk_scale /emuli /= /get_gvar /= => hi.
  case: ifP => /= hloc.
  + rewrite /get_gvar hloc => -> /= + _.
    case: aa; rewrite /= hi /= /sem_opN /= WArray.castK /= => -[] /allP h;
    by apply/allP => j /in_ziotaP ?; apply/h/in_ziotaP; Lia.nia.
  move=> /get_global_arr_init /allP hinit _ /allP hbound.
  apply/allP => j h; have /in_ziotaP ? := h.
  apply/hinit/in_ziotaP. have /WArray.in_boundP := hbound j h; Lia.lia.
Qed.

Lemma arr_isdef s x len : vtype (gv x) = sarr len -> is_defined (evm s).[gv x].
Proof.
  move=> hty; have := Vm.getP (evm s) (gv x).
  by rewrite hty => /compat_valEl [? ->].
Qed.

Lemma arr_catch_get_gvar {n} s x (t: WArray.array n) :
  vtype (gv x) = sarr n ->
  get_gvar (wc:=withcatch) true gd (evm s) x = ok (Varr t) ->
  get_gvar true gd (evm s) x = ok (Varr t).
Proof. by rewrite /get_gvar /get_var => /(arr_isdef s) ->. Qed.

Lemma is_wi1P o :
  match is_wi1 o with
  | Some(s, oi) => o = Owi1 s oi
  | None =>
     let t := etype_of_op1 o in
     sign_of_etype t.1 = None /\ sign_of_etype t.2 = None
  end.
Proof. by case: o => // -[]. Qed.

Lemma estate_eq:
  forall s s', st_rel (λ _ : unit, eq) tt s s' ->
  s = s'.
Proof. by move=> [???][>][] /= *; subst. Qed.
(* ----- Aux Lemmas ----- *)

(* Safety Lemma: pexpr *)
Let Pe e :=
  forall s v,
  sem_cond_wc gd (eands (sc_pexpr e)) s = ok true ->
  sem_pexpr_wc true gd s e = ok v ->
  sem_pexpr true gd s e = ok v.

Let Qe es :=
  forall s vs,
  sem_cond_wc gd (eands (conc_map sc_pexpr es)) s = ok true ->
  sem_pexprs_wc true gd s es = ok vs ->
  sem_pexprs true gd s es = ok vs .

Lemma sc_pexprP_aux: (forall e, Pe e) /\ (forall es, Qe es).
Proof.
  apply: pexprs_ind_pair; subst Pe Qe; split => //=; t_xrbindP => //.
  + by move=> e he es hes s vs /eandsE_cat[/he{}he] /hes{}hes v {}/he -> vs' /hes -> <- /=.

  (* Gvar *)
  + move=> x s v.
    rewrite /sc_gvar /get_gvar /sem_cond /=.
    case: (is_lvar x) => //.
    rewrite /sc_var /get_var /=.
    case harr: is_sarr.
    + move: harr => /is_sarrP[len htx].
      by have -> := arr_isdef s htx.
    by t_xrbindP => z /= [] <- /= [] ->.

  (* Array access *)
  + move=> al aa sz x e he s v /eandsE_cat[/he{}he].
    rewrite /sc_arr_get => /eandsE_cat[+ /eandsE_cat[]].
    move=> hal hbound hinit; apply on_arr_gvarP => n r htx.
    have xdef := arr_isdef s htx; move=> /(arr_catch_get_gvar htx) hgvr /=.
    t_xrbindP=> zi z hewc /to_intI ? w wcatch <-; subst z.
    have {}he := he _ hewc; rewrite he hgvr /=.
    move: wcatch; rewrite /WArray.get /read /=.
    have -> /= := sc_is_aligned_ifP hewc hal.
    move: hbound; rewrite htx => /(sc_in_boundP_all r hewc) hbound.
    rewrite htx in hinit.
    have {}hinit := sc_arr_initP hewc hgvr hinit hbound.
    have : exists l, mapM (λ k : Z,
      WArray.get8 r (add (zi * mk_scale aa sz) k)) (ziota 0 (wsize_size sz)) = ok l;
    last first.
    + by move=> [l -> /=] [->].
    elim: (ziota 0 (wsize_size sz)) hbound hinit => //=; eauto.
    move=> j js hrec /andP [h1 h2] /andP [h3 h4].
    rewrite {2}/WArray.get8 WArray.addE h1 /= h3 /=.
    by have [l -> /=] := hrec h2 h4; eauto.

  (* Subarray access *)
  + move=> aa sz len x e he s v /eandsE_cat[/he {}he].
    move=> hbound; apply on_arr_gvarP => n r htx.
    have xdef := arr_isdef s htx; move=> /(arr_catch_get_gvar htx) hgvr /=.
    t_xrbindP=> zi z hewc /to_intI ? w wcatch <-; subst z.
    have {}he := he _ hewc; rewrite he hgvr /=.
    move: wcatch; rewrite /WArray.get /read /=.
    have helen : sem_pexpr_wc true gd s (Pconst (arr_size sz len)) =
                   ok (to_val (t:=sint) (arr_size sz len)) by done.
    move: hbound; rewrite htx => /(sc_in_boundP hewc helen) []/ZleP h1 /ZleP h2.
    by rewrite /WArray.get_sub h1 h2 /= => [][->].

  (* Memory read *)
  + move=> al sz e he s v /eandsE_cat[/he{}he].
    move=> /eandsE_cat[hal hmem] w wv hewc.
    have {}he := he _ hewc; rewrite /read he => /= topow w2.
    move: hmem; rewrite /sem_cond /=.
    t_xrbindP => z w3 w3v; rewrite hewc => -[]?; subst w3v.
    rewrite topow => /= -[]?; subst w3 => <- [] + + <-.
    have -> /= : is_aligned_if al w sz.
    + move: hal; rewrite /sc_is_aligned_if_m /sem_cond; case: al=>//=.
      rewrite /sem_sop2 /sem_sop1 /is_align /= p_to_zE; t_xrbindP.
      by rewrite hewc=> ???? [<-] /=; rewrite topow /= => -[ <-] /= [<-] /=.
    elim: ziota => [|k ks hrec] /=; first by move=> _ [->].
    rewrite (get_read8 _ Unaligned) addE.
    move=> /andP[] /is_okP[w8 ->] /hrec{}hrec /=.
    case h: (mapM _ ks) hrec => //=.
    by move=> hrec [] ->.

  (* Unary operator *)
  + move=> op e he s v /eandsE_cat[/he{}he].
    move=> hop v1 hewc; have {}he := he _ hewc.
    rewrite he /= /sem_sop1.
    have {}hdef := sem_pexpr_defined he.
    case hval: of_val=> [a|e0] /=; last first.
    + by have -> := isdef_errtype hdef hval.

    move: hop; rewrite /sc_op1 /sc_wiop1.
    case: is_wi1 (is_wi1P op); last first.
    + case: op a hval=> //=; first by case.
      by move=> sg +++ []; case.
    t_xrbindP; case=> sg wop ?; subst op.

    case: wop a hval => //=.
    + move=> ws z /to_intI ?; subst.
      by move=> /(sc_wi_range_of_int hewc) ->.
    move=> ws w /to_wordI [ws2 [w2] [? htr]]; subst v1 => /=.
    rewrite /signed /safety_shared.sc_op1 /=.

    case: sg; rewrite /sem_cond /= hewc /=;
      rewrite /sem_sop1 /= htr => -[] /ZeqbP.
    + rewrite /wint_of_int /in_wint_range /in_sint_range /=.
      move=> /wsigned_opp -> /=.
      by have [/ZleP -> /ZleP ->] := wsigned_range (-w).
    by move=> ->.

  (* Binary operator *)
  + move=> op e1 he1 e2 he2 s v /eandsE_cat[/he1{}he1].
    move=> /eandsE_cat[/he2{}he2] hop v2 he1wc v3 he2wc.
    have {}he1 := he1 _ he1wc.
    have {}he2 := he2 _ he2wc.
    rewrite he1 he2 /sem_sop2 /=.
    have {}hdef1 := sem_pexpr_defined he1.
    have {}hdef2 := sem_pexpr_defined he2.
    case hval2: of_val=> [a2|er2];
    case hval1: of_val=> [a1|er1] //=; last first.
    1,3: by have -> := isdef_errtype hdef1 hval1.
    + by have -> := isdef_errtype hdef2 hval2.

    case: op hop a1 hval1 a2 hval2=> //=; try by case.
    1-2: by move=> sg; case=>// ws hsc;
      move=> w1' /to_wordI[ws1] [w1] [? tr1]; subst v2;
      move=> w2' /to_wordI[ws2] [w2] [? tr2]; subst v3;
      rewrite /mk_sem_divmod (sem_sc_divmod _ _ hsc) //=;
      rewrite /sem_sop1 /sem_sop2 /of_val; t_simpl_rewrites.

    move=> sg ws; case=> //= hsc;
    move=> w1' /to_wordI[ws1] [w1] [? tr1]; subst v2;
    move=> w2' /to_wordI[ws2] [w2] [? tr2]; subst v3.
    1-3:
      by move: hsc; rewrite /mk_sem_wiop2 /sc_wi_range_op2 => hsc;
      rewrite (sc_wi_range_of_int _ hsc) //=;
      rewrite /sem_sop1 /sem_sop2; t_simpl_rewrites.
    1-2:
      by rewrite /mk_sem_divmod (sem_sc_divmod _ _ hsc) //=;
      rewrite /sem_sop1 /sem_sop2; t_simpl_rewrites.
    + rewrite /mk_sem_wishift /wint_of_int.
      rewrite (sc_wi_rangeP (wc:=withcatch) (gd:=gd) (s:=s) (e := (elsli (toint sg ws e1) (toint Unsigned U8 e2)))) //=.
      by rewrite /elsli /= he1wc he2wc /= /sem_sop1 /sem_sop2 /= tr1 /= tr2 /=.
    by rewrite /mk_sem_wishift /wint_of_int in_wint_range_zasr.

  (* N-ary opertors *)
  + move=> op es he s v /he{}he v2 {}/he.
    rewrite /sem_pexprs /sem_opN => he; rewrite he /=.
    have := [elaborate sem_opN_typed_ok op].
    move: (type_of_opN op) (sem_opN_typed op)=> [tin tout] /=.
    elim: tin v2 es he => [| tin tins hrec] [|v' vs'] es he semop //=.
    + by move=> [semtout ->].
    move: es he=> [| e es] //= + hok.
    t_xrbindP=> z /sem_pexpr_defined v'def zs hes ? ? ; subst z zs.
    case hval: (of_val tin v')=> [semtin|] //=;
    last by rewrite (isdef_errtype v'def hval).
    exact: hrec _ _ hes _ (hok semtin).

  (* Conditional expression *)
  + move=> ty e he e1 he1 e2 he2 s v /eandsE_cat[/he{}he].
    move=> /eandsE_cat[/he1{}he1] /he2{}he2.
    by move=> v2 v3 {}/he -> /= -> v5 v6 {}/he1 -> /= -> v7 v8 {}/he2 -> /= -> <-.

  (* Big expression *)
  + move=> idx hidx op vi body hbody start hstart len hlen s v.
    move=> /eandsE_cat[/hidx{}hidx] /eandsE_cat[/hstart{}hstart].
    move=> /eandsE_cat[/hlen{}hlen] /eandsE_cons[] hop hbig.
    move=> zstart z0 hstartwc /to_intI ? zlen z1 hlenwc /to_intI ?.
    subst z0 z1; move=> vacc vidx hidxwc htruidx.
    have {}hstart := hstart _ hstartwc.
    have {}hlen := hlen _ hlenwc.
    have {}hidx := hidx _ hidxwc.
    rewrite hstart hlen hidx /= htruidx /=.
    have hdef1 := truncate_val_defined htruidx; clear htruidx.

    move: hbig=> /eandsE_cons[] /=.
    rewrite /sem_cond /= hstartwc hlenwc => /= + _.
    t_xrbindP => z0 + /to_boolI ?; subst z0.

    elim: ziota vacc hdef1 => [| k ks hrec] //= vacc hdef1.
    t_xrbindP => vw s1 -> vscbody h1 op2; rewrite /sem_sop2 in op2; move: op2 => /=.
    case heq: to_bool => [vb | er] /=; last first.
    + by have -> := (isdef_errtype (t:=sbool) (sem_pexpr_defined h1)) heq.
    move=> [?] hfold v2 s2 [?] vbody h2; subst vw s2 => /=.

    have: vb = (Vbool true).
    + move: hfold; clear k hrec heq; elim: ks vb => /=.
      + by move=> ? [->].
    t_xrbindP => k ks hrec init v1 vf fok vp pok.
    rewrite /sem_sop2 /=.
    case heq: to_bool => [vpb | er] /=; last first.
    + by have -> := (isdef_errtype (t:=sbool) (sem_pexpr_defined pok)) heq.
    by move=> [?]; subst v1 => /hrec /andb_prop[].
    move: heq => /to_boolI ? ?; subst vscbody vb.

    move: hfold => /hrec{}hrec hcatch /hrec{}hrec.
    move: hbody; rewrite /sem_cond => /(_ s1 vbody); rewrite h1 h2 /=.
    move=> /(_ erefl erefl) {}h2; rewrite h2 /=.
    move: hcatch; rewrite /sem_sop2 /=.
    have hdef2 := sem_pexpr_defined h2.

    case hval2: of_val=> [a2|er2];
    case hval1: of_val=> [a1|er1] //=; last first.
    1,3: by have -> := isdef_errtype hdef1 hval1.
    + by have -> := isdef_errtype hdef2 hval2.

    case: op hop hrec a1 hval1 a2 hval2 => //=.
    1-3: by move=> _ hrec a1 /to_boolI ? a2 /to_boolI ? [?]; subst vacc vbody v2; apply hrec.
    1-3: case; first by move=> _ hrec a1 /to_intI ? a2 /to_intI ? [?]; subst vacc vbody v2; apply hrec.
      1-3: by move=> ws _ hrec a1 /to_wordI[ws1][w1][? _] a2 /to_wordI[ws2][w2][? _] [?]; subst vacc vbody v2; apply hrec.
    1-2: by move=> sg; case=> //=; first by move=> _ hrec a1 /to_intI ? a2 /to_intI ? [?]; subst vacc vbody v2; apply hrec.
    1-4: by move=> ws _ hrec a1 /to_wordI[ws1][w1][? _] a2 /to_wordI[ws2][w2][? _] [?]; subst vacc vbody v2; apply hrec.
    1-2: case=> //=; first by move=> _ hrec a1 /to_intI ? a2 /to_intI ? [?]; subst vacc vbody v2; apply hrec.
      1-2: by move=> ws _ hrec a1 /to_wordI[ws1][w1][? _] a2 /to_wordI[ws2][w2][? _] [?]; subst vacc vbody v2; apply hrec.
    1-2: by move=> ws _ hrec a1 /to_wordI[ws1][w1][? _] a2 /to_wordI[ws2][w2][? _] [?]; subst vacc vbody v2; apply hrec.
    1-2: case=> //=; first by move=> _ hrec a1 /to_intI ? a2 /to_intI ? [?]; subst vacc vbody v2; apply hrec.
      1-2: by move=> ws _ hrec a1 /to_wordI[ws1][w1][? _] a2 /to_wordI[ws2][w2][? _] [?]; subst vacc vbody v2; apply hrec.
    1-4: case=> //=; first by move=> _ hrec a1 /to_intI ? a2 /to_intI ? [?]; subst vacc vbody v2; apply hrec.
      1-4: by move=> sg ws _ hrec a1 /to_wordI[ws1][w1][? _] a2 /to_wordI[ws2][w2][? _] [?]; subst vacc vbody v2; apply hrec.
    1-6: by move=> ? ws _ hrec a1 /to_wordI[ws1][w1][? _] a2 /to_wordI[ws2][w2][? _] [?]; subst vacc vbody v2; apply hrec.

    move=> sg ws; case=> //= hsc hrec;
    move=> w1' /to_wordI[ws1] [w1] [? tr1]; subst vacc;
    move=> w2' /to_wordI[ws2] [w2] [? tr2]; subst vbody.
    + by rewrite /mk_sem_wishift /wint_of_int in_wint_range_zasr => /= -[?]; subst v2; apply hrec.
    1-6: by move=> [?]; subst v2; apply hrec.

  (* Pis_mem_init*)
  move=> e1 e2 he1 he2 s v /eandsE_cat[/he1{}he1] /he2{}he2.
  by move=> w1 v1 {}/he1 -> /= -> w2 v2 {}/he2 -> /= -> <-.
Qed.

Lemma sc_pexprP : forall e, Pe e.
Proof. by case sc_pexprP_aux. Qed.

Lemma sc_pexprsP : forall es, Qe es.
Proof. by case sc_pexprP_aux. Qed.

(* ---- ---- *)

Lemma DB_to_val ty (v : sem_t ty) wdb : DB wdb (to_val v).
Proof. by case: ty v; rewrite /DB /= orbT. Qed.

Lemma compat_val_to_val ty (v : sem_t ty) : compat_val ty (to_val v).
Proof. by case: ty v => *; rewrite /compat_val /= eq_refl. Qed.

Local Lemma all_get_read8 mem al wlo sz :
  all (λ i : Z,
       is_ok (read mem al (wlo + wrepr Uptr i)%R U8))
      (ziota 0 sz)
  =
  all (λ i : Z,
       is_ok (get mem (wlo + wrepr Uptr i)%R))
      (ziota 0 sz).
Proof.
  elim: ziota => [| k ks hrec] //=.
  by rewrite -get_read8 hrec.
Qed.

Local Lemma set_allgetok ks mem mem' q w wlo :
  all (fun i => is_ok (get mem (wlo + wrepr Uptr i)%R)) ks ->
  set mem q w = ok mem' ->
  all (fun i => is_ok (get mem' (wlo + wrepr Uptr i)%R)) ks.
Proof.
  move=> + hset.
  elim: ks => [// | k ks hind].
  move=> /andP[h1 h2] /=.
  rewrite hind //= (setP _ hset).
  case: eqP => //; by rewrite h1.
Qed.

(* Safety Lemma: lval *)
Lemma sc_lvalP l v s s':
  sem_cond_wc gd (eands (sc_lval l)) s = ok true ->
  write_lval (wc:=withcatch) true gd l v s = ok s' ->
  write_lval true gd l v s = ok s'.
Proof.
  case: l => [vi tynone | x | al sz x e | al aa sz x e | aa sz pos x e ] //=.
  + (* Lmem *)
    t_xrbindP => /eandsE_cat[] /sc_pexprP he /eandsE_cat[hal hmem] wpt vpt hewc.
    have {}he := he _ hewc.
    rewrite he => /to_wordI[sz2 [w2]] [? htr2]; subst vpt.
    move=> w /to_wordI[sz3[w3]] [? htr3] me + ?; subst v s'.
    rewrite /= htr2 htr3 /= /write.
    have -> /= : is_aligned_if al wpt sz.
      + move: hal; rewrite /sc_is_aligned_if_m /sem_cond; case: al => //=.
        by rewrite hewc /= /sem_sop2 /sem_sop1 /= htr2.
    suff : [elaborate exists l, foldM
         (λ (k : Z) (m : mem),
            set m (add wpt k) (LE.wread8 w k))
         (emem s) (ziota 0 (wsize_size sz)) = ok l].
    + by move=> [l -> /=] [->].
    move: hmem; rewrite /sem_cond /=.
    rewrite hewc /= htr2 => /= -[].
    set m' := (emem s).
    rewrite all_get_read8.
    elim: ziota m' => [| k ks hrec m'] /=; first by eauto.
    move=> /andP[] /is_okP [gv okg] okgs.
    apply (getok_setok (LE.wread8 w k)) in okg.
    move: okg => [fmem hset] /=.
    have {}okgs := set_allgetok okgs hset.
    have {}hrec := hrec fmem okgs.
    by rewrite hset /=.

  + (* Laset *)
    rewrite /sc_arr_set => /eandsE_cat[] /sc_pexprP he /eandsE_cat[hal hbound].
    rewrite /on_arr_var; t_xrbindP => v1 getx; rewrite getx /=.
    case: v1 getx => //= len r; t_xrbindP => /get_varI htx z v2 hewc.
    have {}he := he _ hewc.
    rewrite he => /= /to_intI ?; subst v2 => w -> r2 + <- /=.
    rewrite /WArray.set /write /=.
    have -> /= := sc_is_aligned_ifP hewc hal.
    move: hbound; rewrite htx => /(sc_in_boundP_all r hewc) hbound.
    have : exists l, foldM (λ (k : Z) (m : WArray.array len),
                       WArray.set8 m (add (z * mk_scale aa sz) k)
                         (LE.wread8 w k)) r (ziota 0 (wsize_size sz)) = ok l; last first.
  + by move=> [rf ->] /= [->].
    elim: (ziota 0 (wsize_size sz)) r hbound  => //=; eauto.
    move=> j js hrec r /andP [h1 h2].
    rewrite {2}/WArray.set8 WArray.addE h1 /=.
    have [l -> /=] := hrec {| WArray.arr_data :=
                             Mz.set (WArray.arr_data r) (z * mk_scale aa sz + j)
                              (LE.wread8 w j) |} h2.
    by eauto.

  + (* Lasub *)
    move=> /eandsE_cat[] /sc_pexprP he hbound.
    rewrite /on_arr_var; t_xrbindP => v1 getx; rewrite getx /=.
    case: v1 getx => //= len r; t_xrbindP => /get_varI htx z v2 hewc.
    have {}he := he _ hewc.
    rewrite he => /= /to_intI ?; subst v2 => w -> r2 + <- /=.
    rewrite /WArray.set_sub /=; rewrite htx in hbound.
    have [//|] := sc_in_boundP hewc _ hbound (len:=len) (aa:=aa) (ilen:=arr_size sz pos).
    move=> /ZleP -> /ZleP -> /=.
    rewrite /write_var /set_var /= htx eq_refl => -[<-] /=.
    by eauto.
Qed.

Lemma sc_lvalsP ls vs s0 s s' okmem:
  sem_cond_wc gd (eands (sc_lvals ls okmem)) s0 = ok true ->
  (evm s0 = evm s) ->
  (okmem -> emem s0 = emem s) ->
  write_lvals_wc true gd s ls vs = ok s' ->
  write_lvals true gd s ls vs = ok s'.
Proof.
  move=> hscs hvm.
  have {}hvm : evm s0 =[\Sv.empty] evm s by rewrite hvm.
  move: hscs hvm; rewrite /sc_lvals => /eandsE_cons[].
  rewrite {1}/sem_cond /= => -[].
  elim: ls vs s Sv.empty okmem => [|l ls hrec] [|v vs] s W okmem //=.
  rewrite Bool.andb_assoc => /= /andP[] /andP[] hmemok hdisj hcheck.
  t_xrbindP => /eandsE_cat[] hsc hscs hvm hokm sf hw hws.
  rewrite (check_scP _ s hmemok hdisj hvm hokm) in hsc.
  have -> /= := sc_lvalP hsc hw.
  apply: (hrec _ _ _ _ hcheck) hws => //.
  + rewrite vrv_recE.
    apply (eq_exT (vm2:= evm s)).
    + by apply: eq_exI hvm; SvD.fsetdec.
    by apply: eq_exI (vrvP hw); SvD.fsetdec.
  by move=> /andP [/hokm -> hlv]; apply: lv_write_memP hw.
Qed.

Let pi := (map_prog sc_fun p).

Lemma sem_pre_sc fn fs :
  sem_pre (wc:=withcatch) pi fn fs = ok tt ->
  sem_pre p fn fs = ok tt.
Proof.
  rewrite /sem_pre get_map_prog /=.
  case: get_fundef=> [fd | //] /=.
  case: fd => /= _ [] // func funty _ _ _ _ _.
  t_xrbindP=> vst -> /= s -> /= us + _.
  elim: (f_pre func) us => [|a l] //=.
  t_xrbindP => hrec us hsca us' /hrec{}hrec ?; subst us.
  move: hsca; rewrite /sem_assert /= -cats1.
  t_xrbindP; case=> // /eandsE_cat[] hsce /=.
  rewrite /sem_cond; t_xrbindP => v hewc /to_boolI ? _ _; subst v.
  have he := sc_pexprP hsce hewc; rewrite he /=.
  move: hrec; rewrite /sem_assert /sem_cond /=.
  elim: l => [| a' as' hrec'] //=.
  t_xrbindP=> us1 b v -> /to_boolI ?; subst v; case:b=> // _ _ us2.
  by move=> -> ? _; subst us1.
Qed.

Lemma sem_post_sc fn vs fs :
  sem_post (wc:=withcatch) pi fn vs fs = ok tt ->
  sem_post p fn vs fs = ok tt.
Proof.
  rewrite /sem_post get_map_prog /=.
  case: get_fundef=> [fd | //] /=.
  case: fd => /= _ [] // func funty _ _ _ _ _.
  t_xrbindP=> vst -> /= s1 -> /= s2 -> /= s3 + _.
  elim: (f_post func) s3 => [|a l] //=.
  t_xrbindP => hrec us hsca us' /hrec{}hrec ?; subst us.
  move: hsca; rewrite /sem_assert /= -cats1.
  t_xrbindP; case=> // /eandsE_cat[] hsce /=.
  rewrite /sem_cond; t_xrbindP => v hewc /to_boolI ? _ _; subst v.
  have he := sc_pexprP hsce hewc; rewrite he /=.
  move: hrec; rewrite /sem_assert /sem_cond /=.
  elim: l => [| a' as' hrec'] //=.
  t_xrbindP=> us1 b v -> /to_boolI ?; subst v; case:b=> // _ _ us2.
  by move=> -> ? _; subst us1.
Qed.

Opaque eands.

Lemma nth_sem_pexprs gd s es pos e vs :
  List.nth_error es pos = Some e →
  sem_pexprs_wc true gd s es = ok vs →
  sem_pexpr_wc true gd s e = ok (nth undef_b vs pos).
Proof.
  elim: pos es vs => [ | n hrec] [ | e0 es] //=; t_xrbindP.
  + by move=> ? [->] ve -> ? _ <-.
  by move=> ? hnth v0 he0 vs hes <- /=; apply: hrec hes.
Qed.

Lemma sem_cond_interp_safe gd s es vs sc:
  sem_pexprs_wc true gd s es = ok vs →
  sem_cond_wc gd (safe_cond_to_e es sc) s = ok true →
  interp_safe_cond vs sc.
Proof.
  case: sc => //=.
  + move=> ws pos hes.
    case heq: List.nth_error => [e|//].
    rewrite /sem_cond /= (nth_sem_pexprs heq hes) /=.
    move=> + w hw.
    by rewrite /sem_sop1 /= hw /= => -[] /eqP.

  + move=> ws signedness; case: es => // hi [] // lo [] // dv l /=; t_xrbindP.
    move=> vhi hhi ? vlo hlo ? vdv hdv ? _ <- <- <- /=; t_xrbindP.
    move=> + whi wlo wdv ? hwhi ?? hwlo ?? hwdv ? _ <- <- ? [] ???; subst.
Opaque wbase.
    case: signedness => /eandE [] /=;
      rewrite /sem_cond /= hhi hlo hdv /= /sem_sop1 /sem_sop2 /=
        hwhi hwlo hwdv /= => -[] /eqP /eqP /negPf -> [].
    + rewrite negb_or /wdwords => /andP [/negbTE -> /negbTE].
      by rewrite Z.gtb_ltb => ->.
    by rewrite Z.gtb_ltb => /negbTE ->.
Transparent wbase.

  + move=> ws zmin zmax pos hes.
    case heq: List.nth_error => [e|//] + w hw.
    rewrite /sem_cond /= (nth_sem_pexprs heq hes) /=.
    by rewrite /sem_sop1 /sem_sop2 /= hw /= => -[] /andP [] /ZleP ? /ZleP.

  + move=> ws pos z hes.
    case heq: List.nth_error => [e|//] + w hw.
    by rewrite /sem_cond /= (nth_sem_pexprs heq hes) /= /sem_sop1 /= hw /= => -[] /ZltP.

  + move=> ws pos z hes.
    case heq: List.nth_error => [e|//] + w hw.
    by rewrite /sem_cond /= (nth_sem_pexprs heq hes) /= /sem_sop1 /= hw /= => -[] /ZleP.

  + move=> ws pos0 pos1 z hes.
    case heq0: List.nth_error => [e0|//].
    case heq1: List.nth_error => [e1|//] + w0 w1 hw0 hw1.
    rewrite /sem_cond /= (nth_sem_pexprs heq0 hes) /= (nth_sem_pexprs heq1 hes) /=.
    by rewrite /sem_sop1 /sem_sop2 /= hw0 hw1 /= => -[] /ZleP.

  move=> ws len pos hes.
  case heq: List.nth_error => [e|//] + t hw i hi.
  rewrite /sem_cond /= (nth_sem_pexprs heq hes) /= /sem_opN /= hw /= => -[].
  move=> /allP his_init.
  rewrite /WArray.get readE /is_aligned_if WArray.is_align_scale /=.
  suff : [elaborate exists l, mapM (λ k : Z, read t Aligned (add (i * wsize_size ws) k) U8) (ziota 0 (wsize_size ws)) = ok l].
  + by move=> [l ->] /=; eexists; eauto.
  apply ziota_ind => [ | j j_s hj /= [l ->]] /=.
  + by exists [::].
  rewrite -get_read8 /get /=.
  have hin : add (i * wsize_size ws) j \in ziota 0 (arr_size ws len).
  + by rewrite WArray.addE /arr_size; apply/in_ziotaP; Lia.nia.
  have := his_init (add (i * wsize_size ws) j) hin.
  rewrite /WArray.get8 /WArray.is_init ; case: Mz.get => // w _.
  have -> /=: WArray.in_bound t (add (i * wsize_size ws) j).
  + by apply /WArray.in_boundP/in_ziotaP/hin.
  by eexists;eauto.
Qed.

Lemma sem_cond_interp_safes gd s es vs sc :
  sem_pexprs_wc true gd s es = ok vs →
  sem_cond_wc gd (eands [seq safe_cond_to_e es i | i <- sc]) s = ok true →
  List.Forall (interp_safe_cond vs) sc.
Proof.
  move=> hes; elim: sc => [ | sc scs hrec] /=.
  + by move=> _; constructor.
  move=> /eandsE_cons [hsc hscs]; constructor; last exact: hrec.
  by apply: sem_cond_interp_safe hsc.
Qed.

(* FIXME : move this *)
Lemma type_of_val_to_val v ty v' :
  type_of_val v = ty →
  is_defined v →
  of_val ty v = ok v' →
  to_val v' = v.
Proof.
  move=> hty; case: (ty) v' (type_of_valI hty) => /=.
  1,2: by move=> ? [|[?]] -> // _ [->].
  + by move=> ?? [t ->] _ /to_arrI [->].
  by move=> ?? [|[?]] -> // _ /=; rewrite truncate_word_u => -[->].
Qed.

(* FIXME : move this *)
Lemma sem_pexpr_type_of gd s e v :
  sem_pexpr true gd s e = ok v ->
  type_of_val v = type_of_expr e.
Proof.
  case: e => /=.
  1-3: by move=> > [<-].
  + by move=> x /type_of_get_gvar /eqP.
  1-2: by move=> >; apply on_arr_gvarP; t_xrbindP => > _ _ > _ _ > _ <-.
  + by move=> >; t_xrbindP => > _ _ > _ <-.
  + by move=> >; t_xrbindP => > _ /sem_sop1I [?] [?] [_ _ ->]; apply type_of_to_val.
  + by move=> >; t_xrbindP => > _ > _ /sem_sop2I [?] [?] [?] [_ _ _ ->]; apply type_of_to_val.
  + by rewrite /sem_opN => >; t_xrbindP => > _ > _ <-; apply type_of_to_val.
  + t_xrbindP => > _ _ > _ ht1 > _ ht2 <-; case: ifP => ?.
    + by apply: truncate_val_has_type ht1.
    by apply: truncate_val_has_type ht2.
  + t_xrbindP => > _ _ > _ _ v0 > _ htr.
    have := truncate_val_has_type htr.
    move=> {htr}; elim: ziota v0 => [ | j js ih] v0 /=.
    + by move=> ? [<-].
    by t_xrbindP => _ > _ > _ /sem_sop2I [?] [?] [?] [_ _ _ ->]; apply/ih/type_of_to_val.
  + by move=> > [<-].
  by t_xrbindP => > _ _ > _ _ <-.
Qed.

(* Safety Lemma: instructions *)
Lemma safety_callP_aux fn :
  wiequiv_f_wa withcatch nocatch withassert withassert
    pi p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:= eq_spec)).
Proof.
  apply wequiv_fun_ind_wa => hrec {}fn _ fs _ [<- <-] fd hgetsc.
  have : exists fd', get_fundef (p_funcs p) fn = Some fd' /\
                     fd = sc_fun fd'.
  + move: hgetsc; rewrite /sc_prog compiler_util.get_map_prog /=.
    by case heq: get_fundef => [fd'|] //= [?]; subst fd; eauto.

  move=> [fd'] [hget ?]; rewrite hget; subst fd; exists fd'=> // hpre; split.
  + by apply sem_pre_sc. (* NOTE: we dont need to rewrite hget hgetsc*)
  move=> s1 hinit; exists s1 => //.
  + move: hinit hpre; rewrite /initialize_funcall /sem_pre /sc_fun /= hgetsc /=.
    by clear hget hgetsc; case: fd' => //=.

  exists (st_rel (fun _ => eq) tt), (st_rel (fun _ => eq) tt); split => //.
  + rewrite /sc_fun /=; clear hget hinit hgetsc.
    case: fd' => //= finf fcont ftin ftparam fbody ftout fres _.

    set Pi := (fun i =>
                 wequiv_rec (wc1 := withcatch) (wc2 := nocatch)
                   (wa1 := withassert) (wa2 := withassert)
                   pi p ev ev eq_spec (st_rel (λ _ : unit, eq) tt)
                   (sc_instr i) [::i] (st_rel (λ _ : unit, eq) tt)).

    set Pc := (fun c =>
                 wequiv_rec (wc1 := withcatch) (wc2 := nocatch)
                   (wa1 := withassert) (wa2 := withassert)
                   pi p ev ev eq_spec (st_rel (λ _ : unit, eq) tt)
                   (conc_map sc_instr c) c (st_rel (λ _ : unit, eq) tt)).

    set Pi_r := (fun ir => forall ii,
                 wequiv_rec (wc1 := withcatch) (wc2 := nocatch)
                   (wa1 := withassert) (wa2 := withassert)
                   pi p ev ev eq_spec
                   (fun si s => st_rel (λ _ : unit, eq) tt si s /\
                     sem_cond (wc:=withcatch) (p_globs p) (eands (sc_instr_ir ii ir).1) si = ok true)
                   ([:: MkI ii (sc_instr_ir ii ir).2]) ([::MkI ii ir])
                   (st_rel (λ _ : unit, eq) tt)).

    rewrite -{2}(cats0 fbody).
    apply wequiv_cat with (st_rel (λ _ : unit, eq) tt); last first.
    + rewrite /safe_assert.
      have -> : [seq MkI dummy_instr_info (Cassert (safety_lbl, e)) | e <- conc_map sc_var fres] =
                [seq MkI dummy_instr_info (Cassert a) | a <- [seq (safety_lbl, e) | e <- conc_map sc_var fres]].
      + by rewrite -map_comp.
      by apply wequiv_asserts_left.
    apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => //;
      subst Pi_r Pi Pc => /= {fn fs hpre s1 finf fcont ftin ftparam fbody ftout}.

    + move=> ir ii hi; rewrite -(cat0s [:: MkI _ _]) -cats1.
      apply wequiv_cat with (fun si s => st_rel (λ _ : unit, eq) tt si s /\
           sem_cond (wc:=withcatch) (p_globs pi) (eands (sc_instr_ir ii ir).1) si = ok true).
      + by apply safe_assertP.
      by apply hi.

    + by apply wequiv_nil.

    + move=> i c hi hc; rewrite /conc_map /= -cat1s.
      by apply wequiv_cat with (st_rel (λ _ : unit, eq) tt).

    + move=> x tg ty e ii.
      apply wequiv_assgn_core.
      move=> si s si' [/estate_eq ->] /eandsE_cat [hscx1 hsce1].
      rewrite /sem_assgn; t_xrbindP=> vei hvei vei' htri hwi.
      have {}hvei := sc_pexprP hsce1 hvei.
      have {}hwi := sc_lvalP hscx1 hwi.
      by rewrite hvei /= htri /= hwi; eexists.

    + move=> xs tg o es ii.
      apply wkequiv_eq_pred; move=> s _ [/estate_eq <-].
      move=> /eandsE_cons[] hwt /eandsE_cons[] hmem /eandsE_cat[] hscx /eandsE_cat[] hsco hsce.
      apply wequiv_opn with (fun vs1 vs2 => [/\ vs1=vs2,
                                  sem_pexprs_wc true gd s es = ok vs1 &
                                  sem_pexprs true gd s es = ok vs2]) eq.
      + by move=> s1 s2 sf [] ??; subst s1 s2 => he; have -> := sc_pexprsP hsce he; exists sf.
      + move=> s1 s2 [] ??; subst s1 s2 => vs _ vf [] <- hewc he.
        rewrite /exec_sopn /sopn_sem /=; case h: i_valid=> //=.
        have := i_semi_safe h.
        have := sem_cond_interp_safes hewc hsco.
        have := sem_pexprs_defined he.
        have : List.Forall2 (fun ty vs => type_of_val vs = ty) (tin (get_instr_desc o)) vs.
        + move: hwt he => [] {hewc hsco hsce}.
          elim: (tin _) es vs => [ | ty tys ih] [ | e es] //=.
          + by move=> vs _ [<-]; constructor.
          move=> vs' /andP [/eqP <- htys]; t_xrbindP => v he vs hes <-; constructor.
          + by apply: sem_pexpr_type_of he.
          by apply: ih htys hes.
        rewrite -{3}(cat0s vs) /sopn_sem_ /interp_safe_cond_ty.
        move=> {hewc he}.
        elim: (tin (get_instr_desc o)) (semi (get_instr_desc o)) {1 2}[::] vs.
        + move=> semi vs1 [] //=; rewrite cats0 => _ _ hall /(_ hall) [vr] -> /= [<-].
          by exists (list_ltuple vr).
        move=> ty tys ih semi vs1 [] //= v vs /List.Forall2_cons_iff [hty htys] /andP [hv hvs].
        rewrite -cat_rcons => hall_safe hinterp.
        case hof: of_val => [v' /= | e]; last by rewrite (isdef_errtype hv hof).
        apply: ih => //.
        by rewrite (type_of_val_to_val hty hv hof).

      move=> vs _ <- s1 s2 sf [] ??; subst s1 s2 => hws.
      have := sc_lvalsP _ _ _ hws; have /eandsE_cons {}hmem := conj hmem hscx.
      by move=> /(_ _ _ hmem erefl (fun _ => erefl)) ->; exists sf.

    + move => xs o es ii.
      apply wkequivP' => si0 s0.
      apply wequiv_syscall with
      eq (fun fs1 fs2 => [/\ fs1 = fs2, emem si0 = fmem fs1
                          & map type_of_val fs1.(fvals) = (scs_tout (syscall_sig_u o))]).
      + apply wrequiv_weaken with
          (fun t s => t = s /\
            sem_cond_wc gd (eands (conc_map sc_pexpr es)) t =
           ok true) eq => //.
        + by move=> ??[ [-> ->] []] /estate_eq -> /= /eandsE_cons [] _ /eandsE_cat [_].
        move=> s1 s2 vs [? hwc] h; subst s2.
        by rewrite (sc_pexprsP hwc h); exists vs.
      + move=> s s' [][] ?? [] /estate_eq ?; subst si0 s0 s'.
        move=> hcond vs vs' fs ?; subst vs' => hex.
        by have /= [-> <-] := syscall_u_toutP hex; exists fs.
      move=> fs1 _ [] <- efmem htyof si s sf [][] ?? [] /estate_eq ?.
      rewrite /upd_estate; subst si0 s0 si => + hws.
      move=> /eandsE_cons[] hmem /eandsE_cat[] hscx hsce.
      have := sc_lvalsP _ _ _ hws; have /eandsE_cons {}hmem := conj hmem hscx.
      by move=> /(_ _ _ hmem erefl (fun _ => efmem)) ->; exists sf.

    + move=> a ii; apply wequiv_assert => /= _; split => //.
      move=> si s [/estate_eq ? hsce]; subst si.
      rewrite /sem_cond; t_xrbindP => v he /to_boolI ?; subst v.
      by have -> := sc_pexprP hsce he; eexists.

    + move=> e c1 c2 hc1 hc2 ii.
      apply wequiv_if.
      + move=> si s b [/estate_eq ? hsce]; subst si.
        rewrite /sem_cond; t_xrbindP => v he /to_boolI ?; subst v.
        by have -> := sc_pexprP hsce he; eexists.
        move=> b; apply wequiv_weaken with (st_rel (λ _ : unit, eq) tt)
          (st_rel (λ _ : unit, eq) tt) => //; first by move=> ??[/estate_eq ->].
      by case: b.

    + move=> x dir lo hi c hc ii.
      apply wequiv_for_eq with (st_rel (λ _ : unit, eq) tt) => //.
      + by move=> > [].
      + move=> s1 s2 vs [/estate_eq ->] /eandsE_cat[hsclo hschi] /=.
        t_xrbindP => vlo hlo z0 vhi hhi ? ?; subst z0 vs.
        have -> := sc_pexprP hsclo hlo.
        have -> := sc_pexprP hschi hhi.
        by eexists.
      move=> i si s si' /estate_eq -> hw.
      by exists si'.

    + move=> al c e ii' c' hc hc' ii.
      apply wequiv_weaken with (st_rel (λ _ : unit, eq) tt)
                        (fun si s => st_rel (λ _ : unit, eq) tt si s /\
                  sem_cond_wc (p_globs pi) (eands (sc_pexpr e)) si = ok true).
      1-2: by move=> > [].
      apply wequiv_while.
      + move=> s s' b []/estate_eq ?; subst s'=> /sc_pexprP he.
        by rewrite /sem_cond; t_xrbindP=> v /he -> /to_boolI ?; subst v; exists b.
      + rewrite -{2}(cats0 c); apply wequiv_cat with (st_rel (λ _ : unit, eq) tt) => //.
        by apply safe_assertP.
      by apply wequiv_weaken with (st_rel (λ _ : unit, eq) tt)
                                  (st_rel (λ _ : unit, eq) tt) => // > [].

    + move=> xs f es ii.
      apply wequiv_call_wa with (rpreF (eS:=eq_spec)) (rpostF (eS:=eq_spec)) eq.
      + move=> s s' vs [] /estate_eq ?; subst s'.
        move=> /eandsE_cons[] hmem /eandsE_cat[] hscx hsce hewc.
        by have -> := sc_pexprsP hsce hewc; eauto.
      + move=> s s' vs vs' [] /estate_eq ? + ?; subst s' vs'.
        move=> /eandsE_cons[] hmem /eandsE_cat[] hscx hsce.
        by apply sem_pre_sc.
      + move=> s s' vs vs' [] /estate_eq ? + ?; subst s' vs'.
        by move=> /eandsE_cons[] hmem /eandsE_cat[] hscx hsce.
      + move=> fs fs' fr fr' [_ ?]; subst fs' => /= ?; subst fr'.
        by apply sem_post_sc.
      + by apply hrec.
      move=> fs fs' fr fr' [_ ?]; subst fs' => /= ?; subst fr'.
      move=> s s' sf [] /estate_eq ?; subst s'.
      rewrite /upd_estate=> /eandsE_cons[] hmem /eandsE_cat[] hscx hsce hw; exists sf=> //.
      have := sc_lvalsP; have /eandsE_cons {}hmem := conj hmem hscx.
      have falseP : forall p, false -> p by[].
      move=> /(_ _ _ _ _ _ _ _ _ _ hw).
      by move=> /(_ _ _ hmem erefl (falseP _ )).

    + move=> s s' fs' /estate_eq ?; subst s'.
      case: fd' hgetsc hget hinit => //.
      rewrite get_map_prog /finalize_funcall /=.
      case: get_fundef => //= > -[] <- [] -> /= ?.
      by t_xrbindP => vs -> /= vs' -> /= <-; eauto.
    by move=> ?? ->; apply sem_post_sc.
Qed.

End GLOBALS.

Lemma safety_callP pi:
  sc_prog p = ok pi ->
  forall fn,
  wiequiv_f_wa withcatch nocatch withassert withassert
    pi p ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:= eq_spec)).
Proof.
  rewrite /sc_prog; t_xrbindP => hall <-.
  apply safety_callP_aux.
  move=> x len t /get_globalI [gv] [hget hgv hty].
Opaque ziota.
  elim: gd hget hall => // -[y yd] gd ih /=.
  case: eqP => // heq; last by move=> + /andP [_ ].
  move=> [->] /andP [] {ih}.
  by case: gv hgv => //= len' t' /Varr_inj [?] ?; subst len' t'.
Qed.

End SAFETY_PROOF.
