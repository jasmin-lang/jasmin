From HB Require Import structures.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import psem safety.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

Section GLOB_DECLS.
Context {gd: glob_decls}.

Section SAFE_PEXPR.
Local Existing Instance nosubword.
#[local] Existing Instance withassert.
Context
  {syscall_state: Type}
  {ep: EstateParams syscall_state}
  {spp: SemPexprParams}.

Definition sem_sc_err (s : estate) (sc : pexpr) := sem_cond gd sc s.

Definition sem_scs_err (s : estate) := mapM (sem_sc_err s).

Definition sem_sc s sc :=
  match sem_sc_err s sc with
  | Ok b => b
  | _ => false
  end.

Definition sem_scs s scs :=
  match sem_scs_err s scs with
  | Ok bs => all id bs
  | _ => false
  end.

Fixpoint valid_scs s (scs : seq pexpr) :=
  match scs with
  | [::] => True
  | sc :: scs => is_ok(sem_cond gd sc s) /\ (sem_sc s sc -> valid_scs s scs)
  end.

(* ----- Scs management lemmas ----- *)
Lemma scs_err_cat s sc1 sc2 :
  is_ok (sem_scs_err s (sc1 ++ sc2)) = is_ok (sem_scs_err s sc1) && is_ok (sem_scs_err s sc2).
Proof.
  rewrite /sem_scs_err mapM_cat.
  case: (mapM _ sc1) => //= b1.
  case: (mapM _ sc2) => //= b2.
Qed.

Lemma sem_scs_cat s sc1 sc2 :
  sem_scs s (sc1 ++ sc2) = (sem_scs s sc1) && (sem_scs s sc2).
Proof.
  rewrite /sem_scs /sem_scs_err mapM_cat.
  case: (mapM _ sc1) => //= b1.
  case: (mapM _ sc2) => //= b2.
  + by rewrite all_cat.
  by rewrite andbF.
Qed.

Lemma sem_scs_cons s sc scs :  sem_scs s (sc :: scs) = sem_sc s sc && sem_scs s scs.
Proof.
  rewrite /sem_scs /sem_sc /=.
  case: sem_sc_err => //= b; case: sem_scs_err => //=.
  by rewrite andbF.
Qed.

Lemma valid_scs_cat s scs1 scs2 :
  valid_scs s scs1 ->
  (sem_scs s scs1 -> valid_scs s scs2) ->
  valid_scs s (scs1 ++ scs2).
Proof.
  elim: scs1 => [|sc1 scs1 hrec] /=.
  + by move=> _ /(_ (erefl true)).
  move=> [h1 h2] h; split => // hsc1.
  apply hrec.
  + by apply h2.
  by move=> hscs1; apply h; rewrite sem_scs_cons hsc1 hscs1.
Qed.

Lemma valid_scs_cat' s scs1 scs2 :
  valid_scs s scs1 ->
  valid_scs s scs2 ->
  valid_scs s (scs1 ++ scs2).
Proof. by move=> h1 h2; apply valid_scs_cat. Qed.

(* ----- Aux Lemmas ----- *)
Opaque wsize_size.

Lemma is_def_type_of v :
  is_defined v →
  ∃ v' : sem_t (type_of_val v), v = (to_val v').
Proof. case: v => //=; eauto. Qed.

Lemma vtypeP s x:
  valid_scs s (sc_var x) ∧ (sem_cond gd (eands (sc_var x)) s = ok true →
  ∃ v : sem_t (vtype x), get_var true (evm s) x = ok (to_val v)).
Proof.
  rewrite /get_var /sc_var.
  case: ifP.
  + move=> /is_sarrP [len h]; rewrite h; split => // _.
    by have := Vm.getP (evm s) x; rewrite h => /compat_valEl [? ->] /=; eauto.
  rewrite /sem_cond /= /sem_sc /= => _; split => // -[]hd /=.
  have := Vm.getP (evm s) x; rewrite /compat_val /= /compat_type /= hd.
  move=> /eqP <- /=.
  have [v -> ] := is_def_type_of hd.
  rewrite type_of_to_val; eauto.
Qed.

Lemma gvar_init_arr s x len :
  vtype (gv x) = sarr len ->
  sem_cond gd (eands (sc_gvar x)) s = ok true.
Proof. by move=> h; rewrite /sc_gvar /sc_var h; case: ifP. Qed.

Lemma var_init_arr s (x: var_i) len :
  vtype x = sarr len ->
  sem_cond gd (eands (sc_var x)) s = ok true.
Proof. by move=> h; rewrite /sc_var h. Qed.

Lemma sc_is_aligned_ifP s (i : sem_t sint) al aa sz e :
  sem_pexpr true gd s e = ok (to_val i) ->
  sem_cond gd (eands (sc_is_aligned_if al aa sz e)) s = ok true ->
  is_aligned_if (Pointer := WArray.PointerZ) al (i * mk_scale aa sz) sz.
Proof.
  rewrite /sc_is_aligned_if /is_aligned_if => hi.
  case: al => //=.
  case: aa => /=.
  + rewrite Z.mul_1_r /sem_scs /sem_scs_err /sem_sc_err /sem_cond /=.
     by rewrite hi.
  by move=> _; apply WArray.is_align_scale.
Qed.

Lemma sc_in_boundP s len (i ilen : sem_t sint) aa sz (e elen : pexpr) :
  sem_pexpr true gd s e = ok (to_val i) ->
  sem_pexpr true gd s elen = ok (to_val ilen) ->
  sem_cond gd (eands (sc_in_bound (sarr len) aa sz e elen)) s = ok true ->
  (0 <= i * mk_scale aa sz /\ i * mk_scale aa sz + ilen <= len)%Z.
Proof.
  rewrite /sc_in_bound /sem_scs /= /emk_scale /emuli /sem_sc_err /sem_cond => he helen /=.
  case: aa => /=; rewrite helen he => /= -[]/andP [/ZleP h1 /ZleP h2]; Lia.lia.
Qed.

Lemma sc_in_boundP_all s len (t : sem_t (sarr len)) (i: sem_t sint) aa sz e :
  sem_pexpr true gd s e = ok (to_val i) ->
  sem_cond gd (eands(sc_in_bound (sarr len) aa sz e (Pconst(wsize_size sz)))) s = ok true ->
  all (fun j => WArray.in_bound t (i * mk_scale aa sz + j)) (ziota 0 (wsize_size sz)).
Proof.
  move=> he hscs.
  have helen : sem_pexpr true gd s (Pconst (wsize_size sz)) =
                 ok (to_val (t:=sint) (wsize_size sz)) by done.
  have [h1 h2] := sc_in_boundP he helen hscs.
  apply /allP => j /in_ziotaP ?; apply/WArray.in_boundP; Lia.lia.
Qed.

Lemma sc_in_sub_boundP s len (t : sem_t (sarr len)) a e1 e2 (ve1 ve2: Z) :
  sem_pexpr true gd s e1 = ok (Vint ve1) ->
  sem_pexpr true gd s e2 = ok (Vint ve2) ->
  0 <= a < ve2 ->
  sem_cond gd (eands (sc_in_bound' (sarr len) e1 e2)) s = ok true ->
  WArray.in_bound t ((ve1 + a)).
Proof.
  move=> he1 he2 hb.
  have {}hb : ve1 <= ve1 + a < ve1 + ve2 by Lia.lia.
  rewrite /sem_scs /sem_scs_err /sem_sc_err /sem_cond /= he1 he2 /=.
  move=> []/andP [/Z.leb_le hlo /Z.leb_le hhi].
  rewrite/ WArray.in_bound; apply/andP; split.
  + apply/Z.leb_le; Lia.lia.
  apply/Z.ltb_lt; Lia.lia.
Qed.

Axiom ziota_add : forall p n, ziota p n = map (fun j => p + j) (ziota 0 n).

(* FIXME : this require a check *)
Axiom get_global_arr_init :
   forall x len (t:WArray.array len) ,
   get_global gd x = ok (Varr t) →
   all (λ j : Z, WArray.is_init t j) (ziota 0 len).

Lemma sc_arr_initP s len (t : WArray.array len) (i : sem_t sint) x aa sz e :
  sem_pexpr true gd s e = ok (to_val i) ->
  get_gvar true gd (evm s) x = ok (Varr t) ->
  sem_cond gd (eands (sc_arr_init x aa sz e)) s = ok true ->
  all (fun j => WArray.in_bound t (i * mk_scale aa sz + j)) (ziota 0 (wsize_size sz)) ->
  all (fun j => WArray.is_init t (i * mk_scale aa sz + j)) (ziota 0 (wsize_size sz)).
Proof.
  rewrite /sem_scs /sem_scs_err /sem_sc_err /sem_cond.
  rewrite /sc_arr_init /get_gvar /emk_scale /emuli /= => hi.
  case: ifP => /= hloc.
  + move=> -> /= + _.
    case: aa => /=; rewrite hi /= => -[] //. by rewrite Z.mul_1_r.
  move=> /get_global_arr_init /allP hinit _ /allP hbound.
  apply/allP => j h; have /in_ziotaP ? := h.
  apply/hinit/in_ziotaP. have /WArray.in_boundP := hbound j h; Lia.lia.
Qed.

Axiom subtype_of_val :
  forall ty1 ty2 (v : sem_t ty2),
    subtype ty1 ty2 ->
    exists2 v', of_val ty1 (to_val v) = ok v' & value_uincl (to_val v') (to_val v).

Opaque of_val value_uincl subtype.

Lemma sc_divmodP_w s ety1 ety2 e1 e2 sg (ve1 : sem_t ety1) (ve2 : sem_t ety2) w o:
  sem_pexpr true gd s e1 = ok (to_val ve1) ->
  sem_pexpr true gd s e2 = ok (to_val ve2) ->
  subtype (sword w) ety1 ->
  ∀ ve1' : word w,
  of_val (sword w) (to_val ve1) = ok ve1' ->
  value_uincl (Vword ve1') (to_val ve1) ->
  subtype (sword w) ety2 ->
  ∀ ve2' : word w,
  of_val (sword w) (to_val ve2) = ok ve2' ->
  value_uincl (Vword ve2') (to_val ve2) ->
  sem_cond gd (eands
    (sc_divmod sg w (eint_of_word sg w e1) (eint_of_word sg w e2))) s = ok true ->
  sem_scs s (sc_divmod sg w (eint_of_word sg w e1) (eint_of_word sg w e2)) ->
  ∃ v : word w,
  Let r := mk_sem_divmod sg o ve1' ve2' in ok (Vword r) = ok (Vword v).
Proof.
  rewrite /sem_scs /sc_divmod /=.
  move=> he1 he2 /subtypeEl [sz1 [? hle1]]; subst ety1.
  move=> ve1' hof1 /value_uinclE [sz1'] [w1] [] /Vword_inj [?]; subst sz1' => /= ? hu1; subst w1.
  move=> /subtypeEl [sz2 [? hle2]]; subst ety2.
  move=> ve2' hof2 /value_uinclE [sz2'] [w2] [] /Vword_inj [?]; subst sz2' => /= ? hu2; subst w2.  
  rewrite /sem_sc_err /sem_cond /eneqi /= /sem_sop2 /= of_val_to_val /=.
  rewrite /sem_sop1 /=.
  rewrite he2 /= /sem_sop1 /= hof2 /= of_val_to_val /=.
  rewrite /mk_sem_divmod; case: sg => /=; last first.
  + rewrite andbT orbF => h.
    case: eqP => /= ?; last by eauto.
    by subst ve2'.
  rewrite /eeqi /eand /enot /sem_sc_err /sem_cond /= /sem_sop2 /=.
  rewrite he1 he2 /= /sem_sop1 /= hof1 hof2 /=.
  repeat rewrite of_val_to_val /=.
  rewrite andbT => -[] /andP[]/ZeqbP h1 /andP h2.
  case: orP => /=; last by eauto.
  move=> [/eqP ? | /andP[] /eqP h3 /eqP h4].
  + by subst ve2'; elim h1 ; rewrite wsigned0.
  by subst ve2'; elim h2; rewrite h3 wsignedN1 !Z.eqb_refl.
Qed.  
 
Lemma arr_isdef s x len : vtype (gv x) = sarr len -> is_defined (evm s).[gv x].
Proof.
  move=> hty; have := Vm.getP (evm s) (gv x).
  by rewrite hty => /compat_valEl [? ->].
Qed.

Lemma wawa e es sc :
  sc_pexprs sc_pexpr (e :: es) = sc ->
  exists sce, sc_pexpr e = sce ∧
  exists (sces : seq safety_cond), sc_pexprs sc_pexpr es = (flatten sces) ∧
  sc = sce ++ (flatten sces).
Proof.
  rewrite /sc_pexprs => <- /=.
  exists (sc_pexpr e); split; by eauto.
Qed.

Lemma arr_catch_get_gvar {n} s x (t: WArray.array n) :
  vtype (gv x) = sarr n ->
  get_gvar (wc:=withcatch) true gd (evm s) x = ok (Varr t) ->
  get_gvar true gd (evm s) x = ok (Varr t).
Proof. by rewrite /get_gvar /get_var => /(arr_isdef s) ->. Qed.

(* Safety Lemma: pexpr *)
Let Pe e :=
  forall s v,
  sem_cond gd (eands (sc_pexpr e)) s = ok true ->
  sem_pexpr (wc:=withcatch) true gd s e = ok v ->
  sem_pexpr true gd s e = ok v.

Let Qe es :=
  forall s vs,
  sem_cond gd (eands (sc_pexprs sc_pexpr es)) s = ok true ->
  sem_pexprs (wc:=withcatch) true gd s es = ok vs ->
  sem_pexprs true gd s es = ok vs .

Lemma etypePe_aux : (forall e, Pe e) /\ (forall es, Qe es).
Proof.
  apply: pexprs_ind_pair; subst Pe Qe; split => //=; t_xrbindP => //.
  + by move=> e he es hes s vs /eandsE_cat[/he{}he] /hes{}hes v {}/he -> vs' /hes -> <-.
 
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
    t_xrbindP=> zi z {}/he he /to_intI ? w wcatch <-; subst; rewrite he hgvr /=.
    move: wcatch; rewrite /WArray.get /read /=.
    have -> /= := sc_is_aligned_ifP he hal.
    move: hbound; rewrite htx => /(sc_in_boundP_all r he) hbound.
    have {}hinit := sc_arr_initP he hgvr hinit hbound.
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
    t_xrbindP=> zi z {}/he he /to_intI ? w wcatch <-; subst; rewrite he hgvr /=.
    move: wcatch; rewrite /WArray.get /read /=.
    have helen : sem_pexpr true gd s (Pconst (arr_size sz len)) =
                   ok (to_val (t:=sint) (arr_size sz len)) by done.
    move: hbound; rewrite htx => /(sc_in_boundP he helen) []/ZleP h1 /ZleP h2.
    by rewrite /WArray.get_sub h1 h2 /= => [][->].
        
  (* Memory read *)
  + move=> al sz e he s v /eandsE_cat[/he{}he].
    move=> /eandsE_cat[hal hmem] w wv /he{}he.
    rewrite /read he => /= topow w2.
    move: hmem; rewrite /sem_cond /=.
    t_xrbindP => z w3 w3v; rewrite he => -[]?; subst.
    rewrite topow => /= -[]?; subst => <- [] + + <-.
    have -> /= : is_aligned_if al w3 sz.
    + move: hal; rewrite /sc_is_aligned_if_m /sem_cond; case: al => //=.
      by rewrite /sem_sop2 /sem_sop1 /is_align /= p_to_zE; t_xrbindP.
    elim: ziota => [|k ks hrec] /=; first by move=> _ [->].
    rewrite (get_read8 _ Unaligned) addE.
    move=> /andP[] /is_okP[w8 ->] /hrec{}hrec /=.
    case h: (mapM _ ks) hrec => //=.
    by move=> hrec [] ->.
    
  (* Unary operator *)
  + move=> op e he s v /eandsE_cat[/he{}he].
    move=> hop v1 /he{}he; rewrite he /=.
    rewrite /sem_sop1.
    move: hop.
    rewrite /sem_cond /sc_op1 /=.
    (*case: op => //=.
    move=> > _.
    case: (of_val sint v1) => //=.
    move=> ?. case: ifP => //=. *)
    admit.

  (* Binary operator *)
  + move=> op e1 he1 e2 he2 s v /eandsE_cat[/he1{}he1].
    move=> /eandsE_cat[/he2{}he2] hop v2 {}/he1 -> v3 {}/he2 -> <- /=.
    admit.
    
  (* N-ary opertors *)
  + move=> op es he s v /he{}he v2 {}/he.
    rewrite /sem_pexprs => -> <- /=.
    rewrite /sem_opN.
    admit.
    
  (* Conditional expression *)
  + move=> ty e he e1 he1 e2 he2 s v /eandsE_cat[/he{}he].
    move=> /eandsE_cat[/he1{}he1] /he2{}he2.
    by move=> v2 v3 {}/he -> /= -> v5 v6 {}/he1 -> /= -> v7 v8 {}/he2 -> /= -> <-.
    
  (* Big expression *)
  + move=> idx hidx op2 vi body hbody start hstart len hlen s v.
    move=> /eandsE_cat[/hidx{}hidx] /eandsE_cat[/hstart{}hstart].
    move=> /eandsE_cat[/hlen{}hlen] /eandsE_cons[] hop hbig.
    move=> zstart ? /hstart{}hstart /to_intI ?; subst; rewrite hstart /=.
    move=> zlen ? /hlen{}hlen /to_intI ?; subst; rewrite hlen /=.
    move=> vidx vtidx /hidx{}hidx htruidx; rewrite hidx /= htruidx /=.
    
    move: hbig; rewrite /sem_cond /= hstart hlen /=.
    rewrite /truncate_val of_val_to_val /=.
    t_xrbindP=> ? + /to_boolI ?; subst.

    elim: ziota {3}true => //= k ks hrec acc.
    t_xrbindP=> vw s2 -> /= vbody hsembody.
    rewrite /sem_sop2 of_val_to_val /=.

    t_xrbindP=> bbody /to_boolI ?? + z2 s3 ?; subst.

    move: hbody=> /(_ s3); rewrite /sem_cond hsembody=> /= hbody.
    move=> idk z4 /hbody.
    admit.
    
  (* Pis_var_init *)
  + by move=> e len he s v /he{}he z v2 {}/he -> /= -> <-. 

  (* Pis_arr_init *)
  + move=> vi e1 e2 he1 he2 s v /eandsE_cat[/he1{}he1] /he2{}he2.
    rewrite /on_arr_var; t_xrbindP => v2 -> /=.
    case: v2 => //=; t_xrbindP=> len r.
    by move=> z1 v3 {}/he1 -> /= -> z2 v4 {}/he2 -> /= -> <-.

  (* Pis_barr_init*)
  + move=> vi e1 e2 he1 he2 s v /eandsE_cat[/he1{}he1] /eandsE_cat[/he2{}he2].
    rewrite /on_arr_var /sc_barr_get eandsE_cat => -[hbound hinit].
    t_xrbindP => vt hvi; rewrite hvi /=.
    case: vt hvi => //=; t_xrbindP=> len r hgetv.
    have /subtypeEl /= varr := type_of_get_var hgetv.
    move=> z1 v1 /he1{}he1 /to_intI ?; subst.
    move=> z2 v2 /he2{}he2 /to_intI ?; subst.
    rewrite he1 he2 => bk + <- /=.
    set acc := true.
    have : forall z, (z \in ziota 0 z2) -> (0 <= z < z2)
        by move=> z /in_ziotaP.
    move: hinit; rewrite /sem_cond /sc_barr_init /= /on_arr_var /=.
    rewrite hgetv /= he1 he2 /= => -[].    
    elim: ziota acc => /= [acc _ _ [->]| k ks hrec acc] //.
    move=> /andP[hinit] /hrec{}hrec hrange.
    move: (hrange k (mem_head k ks)) => hr.
    move: hbound; rewrite varr=> hbound.
    have {}hbound := sc_in_sub_boundP r he1 he2 hr hbound.
    t_xrbindP=> b w8 hcatch ?; subst.
    move=> /(hrec (acc && (w8 == wrepr U8 (-1)))){}hrec.    
    move: hcatch; rewrite WArray.get8_read -get_read8 /= /WArray.get8.
    rewrite hinit hbound => /= -[->].
    by apply hrec=> z hz; apply hrange; rewrite in_cons hz orbT.
  
  (* Pis_mem_init*)
  + move=> e1 e2 he1 he2 s v /eandsE_cat[/he1{}he1] /he2{}he2.
    by move=> w1 v1 {}/he1 -> /= -> w2 v2 {}/he2 -> /= -> <-.
Admitted.

Lemma etypePe : forall e, Pe e.
Proof. by case etypePe_aux. Qed.

(*
(* Validity Lemma: pexpr *)
Let Pev e :=
  forall s ty, etype e = ok ty ->
  let sc := sc_e e in
  valid_scs s sc.

Let Qev es :=
  forall s tys, mapM etype es = ok tys ->
  let sc := flatten (map sc_e es) in
  valid_scs s sc.

Lemma etypePev_aux : (forall e, Pev e) /\ (forall es, Qev es).
Proof.
  apply: pexprs_ind_pair; subst Pev Qev; split => //=; t_xrbindP => //.

  (* z::z0 *)
  + by move=> e he es hes s ? te {}/he he tes {}/hes/=hes _; apply valid_scs_cat.
  (* Parr_init_elem *)
  + by move=> e n H > /H{}H ?.
  (* Gvar *)
  + by move=> x s ty /(gvtypeP s) [???].
    
  (* Array access *)
  + move=> al aa sz x e he s ty tx /(gvtypeP s) [htx' okx hx] te hte.
    have {}he := he s _ hte.
    move=> /andP[]/is_sarrP [len htx] /subtypeEl ??; subst tx te ty.
    apply valid_scs_cat => // {}he.
    have [? {}he /=] := etypePe hte he.
    rewrite /sc_arr_get; apply valid_scs_cat'; last apply valid_scs_cat'.
    + rewrite /sc_is_aligned_if; case: ifP => _ //=; split => //.
      by rewrite /sem_sc_err /= he.
    + rewrite /sc_in_bound htx /elei /emk_scale /emuli /eaddi /ezero /=.
      by case: ifP => _ /=; rewrite /sem_sc_err /= he /= /sem_sop2 /= !of_val_to_val /=.
    have /hx := gvar_init_arr s htx.
    rewrite /get_gvar /sc_arr_init; case: ifP => //= _.
    rewrite /sem_sc_err /= htx => -[vx] ->; rewrite /emk_scale /emuli /eaddi /=.
    by case: ifP => //= _; rewrite he /sem_sop2 /=.

  (* Subarray access *)
  + move=> aa sz len' x e he s ty tx /(gvtypeP s) [htx' okx hx] te hte.
    have {}he := he s _ hte.
    move=> /andP []/is_sarrP [len htx] /subtypeEl ??; subst tx te ty.
    apply valid_scs_cat => // {}he.
    have [? {}he /=] := etypePe hte he.
    rewrite /sc_in_bound htx /elei /emk_scale /emuli /eaddi /=.
    by case: ifP => _ /=; rewrite /sem_sc_err /= he /= /sem_sop2 /= !of_val_to_val.

  (* Memory read *)
  + move=> al sz x e he s ty te hte /andP [hsubx hsube] ?; have {}he := he s _ hte.
    have [hvx hx]:= vtypeP s x.
    apply valid_scs_cat => // {}/hx [vx hx].
    have [vx' hofx _]:= subtype_of_val vx hsubx.
    move/of_val_typeE: (hofx) => [wsx] [wx] [htox htrx].
    apply valid_scs_cat => //.
    move=> /(etypePe hte) [ve {}he].
    have [ve' hofe _]:= subtype_of_val ve hsube.
    move/of_val_typeE: (hofe) => [wse] [we] [htoe htre].
    apply valid_scs_cat' => /=.
    + rewrite /sc_is_aligned_if_m; case: ifP => //= _.
      1-2: rewrite /sem_sc_err /= /get_gvar /= hx he /= /sem_sop2 /sem_sop1 /= hofx hofe /=.
      by rewrite !of_val_to_val.
    by rewrite truncate_word_u.

  (* Unary operator *)
  + move=> op e he s ty ety; case heq: type_of_op1 => [tin tout].
    move=> hte; t_xrbindP => hsub ?; subst ty.
    by have {}he := he s _ hte; apply valid_scs_cat => // /(etypeP hte) [ve {}he].
    
  (* Binary operator *)
  + move=> op e1 he1 e2 he2 s ty ety1 hte1 ety2 hte2.
    case heq: type_of_op2 => [[tin1 tin2] tout].
    t_xrbindP => /andP[hsub1 hsub2] ?; subst ty.
    have [???]: [/\ tin1 = (type_of_op2 op).1.1
                 , tin2 = (type_of_op2 op).1.2
                 & tout = (type_of_op2 op).2] by rewrite heq.
    have {}he1 := he1 s _ hte1; apply valid_scs_cat => // /(etypePe hte1) [ve1 {}he1].
    have {}he2 := he2 s _ hte2; apply valid_scs_cat => // /(etypePe hte2) [ve2 {}he2].
    subst => {heq}.
    have [ve1' hve1' huincl1] := subtype_of_val ve1 hsub1.
    have [ve2' hve2' huincl2] := subtype_of_val ve2 hsub2.
    case: op hsub1 ve1' hve1' huincl1 hsub2 ve2' hve2' huincl2 => //.
    + case => //= sg w hsub1 ve1' hof1 hu1 hsub2 ve2' hof2 hu2; split.
      + by rewrite /sem_sc_err /= he2 /sem_sop1 /= hof2.
      + by case: sg => //= _; rewrite /sem_sc_err /= he1 he2 /sem_sop1 /= hof1 hof2.
    case => //= sg sz hsub1 ve1' hof1 hu1 hsub2 ve2' hof2 hu2; split => //.
    + by rewrite /sem_sc_err /= he2 /= /sem_sop1 /= hof2 /= /sem_sop2 /= !of_val_to_val /=.
    case: sg => //= _; rewrite /sem_sc_err /= he1 he2 /sem_sop1 /sem_sop2 /= hof1 hof2 /=.
    by repeat rewrite !of_val_to_val /=.
    
  (* N-ary opertors *)
  + by move=> op es hes s ty tys /hes.

  (* Conditional expression *)
  move=> ty e he e1 he1 e2 he2 s ty' te /he{}he te1 /he1{}he1 te2 /he2{}he2 _ _.
  by apply valid_scs_cat' => //; apply valid_scs_cat'.

  (* Big expression *)
  + move=> e he op x e1 he1 e2 he2 e3 he3 s ty te oke te1 oke1 te2 oke2 te3 oke3.
    case heq: type_of_op2 => [[tin1 tin2] tout].
    t_xrbindP=> /andP[hsubx /and5P[hsube2 hsube3 hsube1 hsube] hsubout] ?; subst.
    have {}he := he s _ oke; have {}he2 := he2 s _ oke2; have {}he3 := he3 s _ oke3.
    apply valid_scs_cat => // {}he2; have [ve2 {}he2] := etypePe oke2 he2.
    apply valid_scs_cat => // {}he3; have [ve3 {}he3] := etypePe oke3 he3.
    apply valid_scs_cat => // {}he; have [ve {}he] := etypePe oke he.

    have [ve2' hofe2 _]:= subtype_of_val ve2 hsube2.
    move/of_val_typeE: (hofe2) => htoe2.
    have [ve3' hofe3 _]:= subtype_of_val ve3 hsube3.
    move/of_val_typeE: (hofe3) => htoe3.
    have [ve' hofe _]:= subtype_of_val ve hsube.
    
    split => //= hop2; split => //.
    rewrite /sem_sc_err /is_ok /=.
    rewrite he2 he3 /= htoe2 htoe3 /=.
    admit. (* TODO *)

  (* Pis_arr_init *)
  + move=> x e1 e2 he1 he2 s ty te1 /he1{}he1 te2 /he2{}he2 _ _.
    by repeat apply valid_scs_cat'.

  (* Pis_barr_init *)
  + move=> x e1 e2 he1 he2 s ty te1 oke1 te2 oke2 /and3P[] /is_sarrP[len htx].
    case: te1 oke1 => //=; case: te2 oke2 => //= oke2 oke1 _ _ _.
    have {}he1 := he1 s _ oke1; have {}he2 := he2 s _ oke2.
    apply valid_scs_cat => // {}he1.
    apply valid_scs_cat => // {}he2.
    have [ve1 {}he1] := etypePe oke1 he1; have [ve2 {}he2] := etypePe oke2 he2.
    rewrite /sc_barr_get; apply valid_scs_cat'.
    + rewrite /sc_in_bound htx /elei /emk_scale /emuli /eaddi /ezero /=; split => //.
      by rewrite /sem_sc_err /= he1 he2 /= /sem_sop2 /=; repeat rewrite of_val_to_val /=.
    have [hval []] := vtypeP s x; first by have hsem := var_init_arr s htx.
    by rewrite htx /= /sem_sc_err /= => tx -> /=; rewrite he1 he2 /=.

  (* Pis_mem_init*)
  + move=> e1 e2 he1 he2 s ty te1 /he1{}he1 te2 /he2{}he2 _ _.
    by repeat apply valid_scs_cat'.
Admitted.

Lemma etypePev : forall e, Pev e.
Proof. by case etypePev_aux. Qed.
 *)

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

Section ForallAnd.
Variable T : Type.
Variables P Q : T -> bool.

Lemma forall_split :
  (forall x, P x && Q x) -> (forall x, P x) /\ (forall x, Q x).
Proof.
  move=> H.
  by split => x; move: (H x) => /andP[].
Qed.
End ForallAnd.

(* Safety Lemma: lval *)
Let Pl l :=
  forall s s' v,
  sem_cond gd (eands (sc_lval l)) s = ok true ->
  write_lval (wc:=withcatch) true gd l v s = ok s' ->
  write_lval true gd l v s = ok s'.

(*
Let Ql ls :=
  forall s s' vs scs,
  sc_lvals ls = ok scs ->
  sem_cond gd (eands scs) s = ok true ->
  List.Forall2 (fun l v => write_lval (wc:=withcatch) true gd l v s = ok s') ls vs ->
  List.Forall2 (fun l v => write_lval true gd l v s = ok s') ls vs.

 lval_ind_pair?
 *)

Lemma ltypePl : forall l, Pl l.
Proof.
  subst Pl => /=.
  move=> [vi tynone | x | al sz x e | al aa sz x e | aa sz pos x e ] s s' v //=.
  + (* Lmem *)
    t_xrbindP => /eandsE_cat[] /etypePe{}he /eandsE_cat[hal hmem] wpt vpt /he{}he.
    rewrite he => /to_wordI[sz2 [w2]] [? htr2]; subst.
    move=> w /to_wordI[sz3[w3]] [? htr3] me + ?; subst.
    rewrite /= htr2 htr3 /= /write.
    have -> /= : is_aligned_if al wpt sz.
      + move: hal; rewrite /sc_is_aligned_if_m /sem_cond; case: al => //=.
        rewrite he /= /sem_sop2 /sem_sop1 /= of_val_to_val /=.
        Transparent of_val. by rewrite /= htr2 /=.

    suff : [elaborate exists l, foldM
         (λ (k : Z) (m : mem),
            set m (add wpt k) (LE.wread8 w k)) 
         (emem s) (ziota 0 (wsize_size sz)) = ok l].
    + by move=> [l -> /=] [->].
        
    move: hmem; rewrite /sem_cond /=.
    rewrite he /= htr2 => /= -[].

    set m := (emem s).
    rewrite all_get_read8.
    elim: ziota m => [| k ks hrec m] /=; first by eauto.    
    move=> /andP[] /is_okP [gv okg] okgs.
    
    apply (getok_setok (LE.wread8 w k)) in okg.
    move: okg => [fmem hset] /=.
    have {}okgs := set_allgetok okgs hset.
    have {}hrec := hrec fmem okgs.
    by rewrite hset /=.
    
  + (* Laset *)
    rewrite /sc_arr_set => /eandsE_cat[] /etypePe{}he /eandsE_cat[hal hbound].
    rewrite /on_arr_var; t_xrbindP => v1 getx; rewrite getx /=.
    case: v1 getx => //= len r; t_xrbindP => /get_varI htx z v2 /he{}he.
    rewrite he => /= /to_intI ?; subst => w -> r2 + <- /=.

    rewrite /WArray.set /write /=.
    have -> /= := sc_is_aligned_ifP he hal.

    move: hbound; rewrite htx => /(sc_in_boundP_all r he) hbound.
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
    move=> /eandsE_cat[] /etypePe{}he hbound.
    rewrite /on_arr_var; t_xrbindP => v1 getx; rewrite getx /=.
    case: v1 getx => //= len r; t_xrbindP => /get_varI htx z v2 /he{}he.
    rewrite he => /= /to_intI ?; subst => w -> r2 + <- /=.

    rewrite /WArray.set_sub /=; rewrite htx in hbound.
    have [//|] := sc_in_boundP he _ hbound (len:=len) (aa:=aa) (ilen:=arr_size sz pos).
    move=> /ZleP -> /ZleP -> /=.
    rewrite /write_var /set_var /= htx eq_refl => -[<-] /=.
    by eauto.
Qed.


(*
(* Validity Lemma: lval *)
Let Plv l :=
  forall s ty, ltype l = ok ty ->
  let sc := sc_lval l in
  valid_scs s sc.

Lemma ltypePlv : forall l, Plv l.
Proof.
  rewrite /Plv => l s ty.
  case: l => [vinf sty | vi | al ws x e | al aa ws x e | aa ws len x e] //=;
               t_xrbindP => ety heok.
  + (* Lmem *)
    move=> /andP[hsubx hsube] ?.
    have [hvx hx]:= vtypeP s x.
    apply valid_scs_cat => // {}/hx [vx hx].
    have [vx' hofx _]:= subtype_of_val vx hsubx.
    move/of_val_typeE: (hofx) => [wsx] [wx] [htox htrx].
    have hinit := etypePev s heok.   
    apply valid_scs_cat; first by[].
    move=> /(etypePe heok) [ve {}he].
    have [ve' hofe _]:= subtype_of_val ve hsube.
    move/of_val_typeE: (hofe) => [wse] [we] [htoe htre].
    apply valid_scs_cat'.
    + rewrite /= /sc_is_aligned_if_m; case: al => //=.
      rewrite /sem_sc_err /= /get_gvar /= hx he /=.
      rewrite /sem_sop2 /sem_sop1 /= hofx hofe /=.
      by rewrite !of_val_to_val.
    rewrite /= /sem_sc_err /= /get_gvar /= hx he /=.
    rewrite /sem_sop2 /sem_sop1 /= hofx hofe /=.
    by rewrite truncate_word_u.

  + (* Laset *)
    move=> /andP[] /is_sarrP[len htx] hsube ?.
    have hinit := etypePev s heok.
    rewrite /sc_arr_set; apply valid_scs_cat; first by[].
    move=> /(etypePe heok) [ve {}he].
    have [ve' hofe _]:= subtype_of_val ve hsube.
    apply valid_scs_cat'.
    + rewrite /= /sc_is_aligned_if; case: al; case: aa => //=.
      rewrite /sem_sc_err /= /get_gvar he /=.
      rewrite /sem_sop2 /sem_sop1 /= hofe /=.
      by rewrite !of_val_to_val.
    rewrite /sc_in_bound; rewrite htx /=.
    rewrite /sem_sc_err /emk_scale /=.
    by case: aa;
    rewrite /= he /= /sem_sop2 /sem_sop1 /= hofe /= !of_val_to_val //.
  
  + (* Lasub *)
    move=> /andP[] /is_sarrP[len' htx] hsube ?.
    have hinit := etypePev s heok.   
    rewrite /sc_arr_set; apply valid_scs_cat; first by[].
    move=> /(etypePe heok) [ve {}he].
    have [ve' hofe _]:= subtype_of_val ve hsube.
    rewrite /sc_in_bound htx /= /sem_sc_err /= /emk_scale /=.
    by case: aa;
    rewrite /= he /= /sem_sop2 /sem_sop1 /= hofe /= !of_val_to_val //.
Qed.
*)
End SAFE_PEXPR.

(*
Section CTYPE.
Local Existing Instance nosubword.
#[local] Existing Instance allow_init.
Context
  `{asmop:asmOp}
  {syscall_state: Type}
  {ep: EstateParams syscall_state}
  {spp: SemPexprParams}
  (s: estate).
  
Section ctype_aux.
Variable itype : instr -> result unit unit.
Fixpoint ctype_aux (c : cmd) : result unit unit :=
  match c with
  | [::] => ok tt
  | i :: cs =>
    Let _ := itype i in
    Let _ := ctype_aux cs in
    ok tt
  end.
End ctype_aux.

Fixpoint itype (i : instr) : result unit unit :=
  match i with
  | MkI ii ir => irtype ir
  end
with irtype (ir : instr_r) : result unit unit :=
  match ir with
  | Cassgn x tag ty e =>
      Let tx := ltype x in
      Let t := etype e in
      Let _ := assert (subtype ty t) tt in
      Let _ := assert (subtype tx ty) tt in
      ok tt
  | Copn xs t op es =>
      Let _ := ltypes xs in (* TODO: lvals compatible with the return type of op *)
      Let _ := mapM etype es in
      Error tt (* Never safe *)
  | Csyscall xs o es =>
      Let _ := ltypes xs in
      Let _ := mapM etype es in
      Error tt (* Never safe *)
  | Cif e c1 c2 =>
      Let t := etype e in
      Let _ := assert (is_sbool t) tt in
      Let _ := ctype_aux itype c1 in
      Let _ := ctype_aux itype c2 in            
      ok tt
  | Cfor i (d, lo, hi) c =>
      let _ := vtype i in
      Let _ := etype lo in
      Let _ := etype hi in
      Let _ := ctype_aux itype c in
      ok tt
  | Cwhile a c e ei c' => (* non termination? *)
      Let t := etype e in
      Let _ := assert (is_sbool t) tt in
      Let _ := ctype_aux itype c in
      Let _ := ctype_aux itype c' in
      ok tt
  | Ccall xs fn es => (* TODO: check that fn is safe *)
      Let _ := ltypes xs in
      Let _ := mapM etype es in
      Error tt
  | Cassert ak ap e =>
      Let _ := etype e in
      ok tt
  end.

(* ----- Aux Lemmas ----- *)
Lemma ctype_aux_inversion i c :
  ctype_aux itype (i :: c) = ok tt ->
  itype i = ok tt
  /\ ctype_aux itype c = ok tt.
Proof.
  move=> //= H.
  case: (itype i) H => [Hi|] H; [|discriminate].
  case: (ctype_aux itype c) H => [Hc|] H; [|discriminate].
  split.
  move: H; case: Hi; by [].
  move: H; case: Hc; by [].
Qed.

(* Validity Lemma: cmd *)
Let Piv i :=
  forall s, itype i = ok tt ->
  let sc := sc_instr i in    (*mcd*)
  valid_scs s sc.            (*pexpr*)

Let Pcv c :=
  ctype c = ok tt ->
  let sc := sc_c c in
  valid_scs sc.

Lemma Pmkv ir ii: Prv ir -> Piv (MkI ii ir).
Proof.
  by move=> HPr.
Qed.

Lemma Pnilv : Pcv [::].
Proof.
  by [].
Qed.

Lemma Pconsv i c:  Piv i -> Pcv c -> Pcv (i::c).
Proof.
  rewrite /Pcv /Piv /ctype => Hiv Hcv Hok.
  have aux := ctype_aux_inversion Hok.
  case: aux => Hi Hc. move: (Hiv Hi) (Hcv Hc).
  apply valid_scs_cat'.
Qed.

Lemma Pasgnv l tag ty e : Prv (Cassgn l tag ty e).
Proof.
  subst Prv; rewrite /irtype.
  case (etype e) as [ety|] eqn: eok;
  case (ltype l) as [lty|] eqn: lok =>//=.
  have Hev := etypePv eok. have Hlv := ltypePlv lok.
  by move=> _; apply valid_scs_cat.
Qed.

Lemma Popnv xs t o es: Prv (Copn xs t o es).
Proof.
  by rewrite /irtype.
Qed.

Lemma Psyscallv xs o es: Prv (Csyscall xs o es).
Proof.
  by rewrite /irtype.
Qed.

Lemma Pifv e c1 c2: Pcv c1 -> Pcv c2 -> Prv (Cif e c1 c2).
Proof.
  rewrite /Pcv /Prv /ctype /irtype => Hc1 Hc2.
  case (etype e) as [ety|] eqn: eok =>//=;
  case ety eqn:eeq;
  case (ctype_aux itype c1) as [c1ty|] eqn:c1ok =>//=;
  case (ctype_aux itype c2) as [c2ty|] eqn:c2ok =>//=;
  try case c1ty eqn:c1eq; try case c2ty eqn:c2eq.
  have Hev := etypePv eok.
  move: (Hc1 Logic.eq_refl) (Hc2 Logic.eq_refl) => H1 H2.  
  by repeat (move=> _; apply valid_scs_cat).
  by rewrite c1ok c2ok.
  by rewrite c1ok.
  by rewrite c1ok.
Qed.

Lemma Pforv v dir lo hi c: Pcv c -> Prv (Cfor v (dir,lo,hi) c).
Proof.
  rewrite /Pcv /Prv /ctype /irtype => Hc.
  case (etype lo) as [loty|] eqn: look;
  case (etype hi) as [hity|] eqn: hiok;
  case (ctype_aux itype c) as [cty|] eqn:cok =>//=;
  try case cty eqn:ceq.
  have [hvx hx]:= vtypeP v;
  have Hlov := etypePv look; have Hhiv := etypePv hiok.
  move: (Hc Logic.eq_refl) => H.
  by repeat (move=> _; apply valid_scs_cat).
  by rewrite cok.
Qed.

Lemma Pwhilev a c e ei c': Pcv c -> Pcv c' -> Prv (Cwhile a c e ei c').
Proof.
  rewrite /Pcv /Prv /ctype /irtype =>  Hc Hc'.
  case (etype e) as [ety|] eqn: eok =>//=; case ety eqn:eeq;
  case (ctype_aux itype c) as [cty|] eqn:cok =>//=;
  case (ctype_aux itype c') as [c'ty|] eqn:c'ok =>//=;
  try case cty eqn:ceq; try case c'ty eqn:c'eq.
  have Hev:= etypePv eok.
  move: (Hc Logic.eq_refl) (Hc' Logic.eq_refl) => H1 H2.
  by repeat (move=> _; apply valid_scs_cat =>//=).
  by rewrite cok c'ok.
  by rewrite cok.
  by rewrite cok.
Qed.

Lemma Pcallv xs f es: Prv (Ccall xs f es).
Proof.
  rewrite /Prv /irtype.
  by case (mapM etype es) as [esty|] eqn: estyok;
  case (ltypes xs) as [lsty|] eqn: lstyok.
Qed.

Context
  {sCP: semCallParams}.
Variable ev : extra_val_t.

(* Safety Lemma: cmd *)
Let Pr ir :=
      forall ii, Pi (MkI ii ir).
   
Let Pi i :=
      itype i = ok tt ->
      let sc := sc_instr i in
      (sem_scs sc -> forall s, exists s', sem_I prog ev s i s').

Let Pc c :=
      ctype c = ok tt ->
      let sc := sc_c c in
      (sem_scs sc -> forall s, exists s', sem prog ev s c s').

Lemma Pmk ir ii: Pr ir -> Pi (MkI ii ir).
Proof.
  rewrite /Pr /Pi; move=> HPr Hitype s1 Hsemscs;
  specialize (HPr Hitype s1 Hsemscs) as [s2 Hs'];
  exists s2; by apply: EmkI.
Qed.

Lemma Pnil : Pc [::].
Proof.
  rewrite /Pc => Hctype Hsc s1; exists s1; by apply Eskip.
  Qed.

Lemma Pcons i c:  Pi i -> Pc c -> Pc (i::c).
Proof.
  rewrite /Pi /Pc. clear Pr Pi Pc. move=> HPi HPc Hctype Hsemscs s1.
  move: Hsemscs Hctype. rewrite /ctype.
  rewrite sem_scs_cat. move/andP => [Hsemsci Hsemscc].
  pose proof ctype_aux_inversion as aux. specialize (aux i c).
  move=> /aux [Hityok Hctyok].
  specialize (HPi Hityok Hsemsci s1) as [s2 H1].
  specialize (HPc Hctyok Hsemscc s2) as [s3 H2].
  exists s3. move: H1 H2; apply Eseq.
Qed.  
  
Lemma Pasgn l tag ty e: Pr (Cassgn l tag ty e).
Proof.
  rewrite /Pr. clear Pr Pi Pc.
  case (etype e) as [ety|] eqn:Hetyok.
  case: (ltype l) => [lty|] //=.
  case (assert (subtype ety ty) tt) => [asser|] //=. move=>_ {asser}.
  case (sc_l l). rewrite cat0s => H2.
  move=> s1. pose proof etypeP as HPaux.
  specialize (HPaux e ety Hetyok H2) as [semt_esty Hsem1].
  
  (* Should be able to solve like this:
  Exists (write_lval true gd lv v' s0). apply sem_Ind_mkI. sem_Ind_assgn.
  apply Eassgn. *)
Admitted.
  
Lemma Popn xs t o es: Pr (Copn xs t o es).
Proof.
  by subst Pr; rewrite /irtype;
  case (ltypes xs) as [lty|] eqn:ltyok;
  case (mapM etype es) as [esty|] eqn:estyok;
  try case lty eqn:ltyeq =>//=;
  try case esty eqn:esyeq =>//=.
Qed.

Lemma Psyscall xs o es: Pr (Csyscall xs o es).
Proof.
  by subst Pr; rewrite /irtype;
  case (ltypes xs) as [lty|] eqn:ltyok;
  case (mapM etype es) as [esty|] eqn:estyok;
  try case lty eqn:ltyeq =>//=;
  try case esty eqn:esyeq =>//=.
Qed.

Lemma Pif e c1 c2: Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
Proof.
  rewrite /Pc /Pr /ctype /sc_c. clear Pr Pi Pc.

  (* Induction on e. This line could be done later *)
  case (etype e) as [ety|] eqn:Hetyok => //=.

  (* Destruct H2 first *)
  move=> HPc1 HPc2 H1 + s1. (**)
  rewrite !sem_scs_cat;
  move/andP => [Hsemsce Hsem_aux];
               move/andP: Hsem_aux => [Hsemsc1 Hsemsc2].
  (* Use it on H1 *)
  move: H1. rewrite /assert; rewrite /is_sbool.
  rewrite Hetyok => //=.
  case ety eqn:etyeq => //=; rewrite <- etyeq in Hetyok.
  
  (* Getting Paux *)
  pose proof etypeP as HPaux.
  specialize (HPaux e ety Hetyok Hsemsce) as [v HPaux].
  
  (* TRYING: c1 *)
  case (ctype_aux itype c1) as [c1ty|] eqn:Hc1tyok.
  case c1ty eqn:c1tyis. subst (* Careful *).
  have okttrefl : ok tt = ok tt by [reflexivity]; specialize (okttrefl unit) (* Weird *). 
  specialize (HPc1 okttrefl Hsemsc1 s1) as [s2 HPc1].
  move=> _; exists s2.

  (* Final step of C1 *)
  move: HPaux HPc1.
  move: v; rewrite /sem_t => //=. move=> v; case: v.
  (* FAILS: gd and s are not the same. s should be s1.*)
  (* p_globs function to fix gd? *)

  (* TRYING: c2 *) (* TODO *)
  case (ctype_aux itype c2) as [c2ty|] eqn:Hc2tyok.
  case c2ty eqn:c2tyis; subst.  
Admitted.

Lemma Pfor v dir lo hi c: Pc c -> Pr (Cfor v (dir,lo,hi) c).
Proof.
Admitted.

Lemma Pwhile a c e ei c': Pc c -> Pc c' -> Pr (Cwhile a c e ei c').
Proof.
Admitted.

Lemma Pcall xs f es: Pr (Ccall xs f es).
Proof.

End CTYPE.
 *)

End GLOB_DECLS.
