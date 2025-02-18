Require Import compiler_util psem psem_facts.
Require Import wint_int.
Import Utf8.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.

Section PROOF.

#[local] Existing Instance progUnit.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

#[local] Existing Instance sCP_unit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Variable (p:uprog) (ev:extra_val_t).

Notation gd := (p_globs p).

#[local]Open Scope vm_scope.

Section M.

Context (m: var -> option (signedness * var)).
Context (FV : Sv.t).

Definition wf_m :=
 forall x,
    match m x with
    | None => true
    | Some (s, xi) =>
      [/\ is_sword (vtype x), vtype xi = sint &
          forall y, x <> y -> in_FV_var FV y ->
             match m y with
             | None => xi <> y
             | Some (_, yi) => xi <> yi
             end]
    end.

Hypothesis (hwf_m : wf_m).

Definition val_to_int (s:option signedness) v :=
  match v with
  | Vword _ w =>
    match s with
    | None => v
    | Some sg => Vint (int_of_word sg w)
    end
  | Vundef (sword _) _ =>
    match s with
    | None => v
    | Some sg => undef_i
    end
  | _  => v
  end.

Definition eqvm (vm vmi : Vm.t) :=
  forall x, in_FV_var FV x -> vmi.[wi2i_var m x] = val_to_int (sign_of_var m x) vm.[x].

Definition eqst (s si : estate) :=
  [/\ escs s = escs si, emem s = emem si & eqvm (evm s) (evm si)].

Lemma is_defined_val_to_int sg v : is_defined (val_to_int sg v) = is_defined v.
Proof.
  case: v => //=.
  + by case: sg.
  by move=> [] // >; case: sg.
Qed.

Lemma val_to_int_None v : val_to_int None v = v.
Proof. by case: v => //= -[]. Qed.

Lemma is_wi1P o :
  match is_wi1 o with
  | Some(s, oi) => o = Owi1 s oi
  | None =>
     let t := etype_of_op1 o in
     sign_of_etype t.1 = None /\ sign_of_etype t.2 = None
  end.
Proof. by case: o => // -[]. Qed.

Lemma is_wi2P o :
  match is_wi2 o with
  | Some(s, oi) => ∃ sz, o = Owi2 s sz oi
  | None =>
     let t := etype_of_op2 o in
     [/\ sign_of_etype t.1.1 = None
       , sign_of_etype t.1.2 = None
       & sign_of_etype t.2 = None]
  end.
Proof.
  case: o => //;
  match goal with
  | |- signedness -> _ => move=> ?
  | |- _ => idtac
  end; case => //= ?;
  eexists; reflexivity.
Qed.

Lemma int_of_word_wrepr sg sz z :
  in_wint_range sg sz z = ok tt ->
  int_of_word sg (wrepr sz z) = z.
Proof.
  case: sg => /assertP /andP[] /ZleP ? /ZleP; rewrite /wmax_unsigned => ?.
  + exact: wsigned_repr.
  apply wunsigned_repr_small; Lia.lia.
Qed.

Lemma esubtype_sign_of t1 t2 : esubtype t1 t2 -> sign_of_etype t2 = sign_of_etype t1.
Proof. by case: t1 t2 => [||l1|[[]|] sz1] [||l2|[[]|] sz2]. Qed.

Lemma sign_of_etype_expr e : sign_of_etype (etype_of_expr m e) = sign_of_expr m e.
Proof. done. Qed.

Lemma sign_of_to_etype_None ty : sign_of_etype (to_etype None ty) = None.
Proof. by case: ty. Qed.

Lemma sign_of_etype_var x : sign_of_etype (etype_of_var m x) = sign_of_var m x.
Proof.
  rewrite /etype_of_var /sign_of_var.
  have := hwf_m x; case: m => /= [ | _]; last by apply sign_of_to_etype_None.
  by move=> [sg xi [] + _ _]; case: vtype.
Qed.

Lemma sign_of_etype_gvar x : sign_of_etype (etype_of_gvar m x) = sign_of_gvar m x.
Proof.
  rewrite /etype_of_gvar /sign_of_gvar; case: ifP => _.
  + by apply sign_of_etype_var.
  by apply sign_of_to_etype_None.
Qed.

Lemma to_stypeK sg t : to_stype (to_etype sg t) = t.
Proof. by case: t. Qed.

Lemma get_var_type_of vm (x : var) (v : value) :
  get_var true vm x = ok v → type_of_val v = to_stype (etype_of_var m x).
Proof.
  rewrite /get_var /etype_of_var; t_xrbindP => /= hdef <-.
  have := Vm.getP vm x; rewrite /compat_val hdef /= => /eqP ->.
  by rewrite to_stypeK.
Qed.

Lemma get_gvar_type_of vm (x : gvar) (v : value) :
  get_gvar true gd vm x = ok v → type_of_val v = to_stype (etype_of_gvar m x).
Proof.
  rewrite /get_gvar /etype_of_gvar /sign_of_gvar; case: ifP => _.
  + by apply get_var_type_of.
  by move=> /type_of_get_global <-; rewrite to_stypeK.
Qed.

Lemma sem_pexpr_type_of s e v :
  sem_pexpr true gd s e = ok v ->
  type_of_val v = to_stype (etype_of_expr m e).
Proof.
  case: e => //=; t_xrbindP.
  1-3: by move=> > <-.
  + by move=> ?; apply get_gvar_type_of.
  1-2: by move=> >; apply: on_arr_gvarP; t_xrbindP => *; subst.
  + by move=> *; subst.
  + move=> o; rewrite /sem_sop1; t_xrbindP => *; subst.
    by rewrite type_of_to_val; clear; case: o => // [ [] | sg []].
  + move=> o; rewrite /sem_sop2; t_xrbindP => *; subst.
    rewrite type_of_to_val; clear.
    by case: o => //;
    match goal with
    | |- signedness -> wsize -> _ => move=> ??
    | |- signedness -> _ => move=> ?
    | _ => idtac
    end; case.
  + by rewrite /sem_opN; t_xrbindP => *; subst; rewrite to_stypeK type_of_to_val.
  move=> > _ _ > _ htr1 > _ htr2 <-.
  rewrite to_stypeK; case: ifP => _; eauto using truncate_val_has_type.
Qed.

Lemma wrepr_int_of_word sz sg (w:word sz) :
  wrepr sz (int_of_word sg w) = w.
Proof. by case: sg => /=; rewrite ?wrepr_signed ? wrepr_unsigned. Qed.

Section E.

Context (s si: estate) (heqs : eqst s si).

Let P e :=
  forall ei, wi2i_e m FV e = ok ei ->
  forall v,
    sem_pexpr true gd s e = ok v ->
    sem_pexpr true gd si ei = ok (val_to_int (sign_of_expr m e) v).

Let Q es :=
  forall eis, mapM (wi2i_e m FV) es = ok eis ->
  forall vs,
    sem_pexprs true gd s es = ok vs ->
    sem_pexprs true gd si eis = ok (map2 (fun e v => val_to_int (sign_of_expr m e) v) es vs).

Lemma wi2i_varP (x: var) v :
   in_FV_var FV x ->
   get_var true (evm s) x = ok v ->
   get_var true (evm si) (wi2i_var m x) = ok (val_to_int (sign_of_var m x) v).
Proof.
  move=> hin; case heqs => _ _ /(_ x hin); rewrite /wi2i_var /sign_of_var.
  case hm : m (hwf_m x) => [ [sg xi] | ]; last first.
  + by rewrite !val_to_int_None /get_var => _ ->.
  move=> [] hty htyi _ hto.
  move=> /get_varP [/= -> hdb hcomp]; rewrite /get_var /=.
  by rewrite hto is_defined_val_to_int hdb.
Qed.

Lemma wi2i_variP x xi v:
  wi2i_vari m FV x = ok xi ->
  get_var true (evm s) x = ok v ->
  get_var true (evm si) xi = ok (val_to_int (sign_of_var m x) v).
Proof. rewrite /wi2i_vari; t_xrbindP => + <-; apply wi2i_varP. Qed.

Lemma wi2i_gvarP x xi v :
  wi2i_gvar m FV x = ok xi ->
  get_gvar true gd (evm s) x = ok v ->
  get_gvar true gd (evm si) xi = ok (val_to_int (sign_of_gvar m x) v).
Proof.
  rewrite /wi2i_gvar /get_gvar /sign_of_gvar; case: ifP.
  + by move=> /= _; t_xrbindP => ? + <- /=; apply wi2i_variP.
  by move=> h [<-]; rewrite h val_to_int_None.
Qed.

Lemma wi2i_gvar_nw x xi v :
  ~is_sword (vtype (gv x)) ->
  wi2i_gvar m FV x = ok xi ->
  get_gvar true gd (evm s) x = ok v ->
  get_gvar true gd (evm si) xi = ok v.
Proof.
  move=> hty hto hget; have := wi2i_gvarP hto hget.
  have -> : sign_of_gvar m x = None; last by rewrite val_to_int_None.
  rewrite /sign_of_gvar  /sign_of_var; case: ifP => _ //.
  by case: m (hwf_m (gv x)) => // -[sg ?] []?; elim hty.
Qed.

Lemma esubtype_to_word sg sz ty v w :
  esubtype (twint sg sz) ty ->
  type_of_val v = to_stype ty->
  to_word sz v = ok w ->
  v = Vword w.
Proof.
  rewrite /=; case: ty => // -[] // _ _ /andP [/eqP <- /eqP <-] /=.
  move=> /type_of_valI [-> | [w' ->]] //=.
  by rewrite truncate_word_u => -[->].
Qed.

Lemma wi2i_eP_ : (forall e, P e) /\ (forall es, Q es).
Proof.
  apply: pexprs_ind_pair; subst P Q; split => //=; t_xrbindP.
  + by move=> _ <- _ _ /=.
  + move=> e he es hes ?? /he{}he ? /hes{}hes <- ?? /he{}he ? /hes{}hes <- /=.
    by rewrite he /= hes.
  1-3: by move=> ?? <- ? <-.
  + move=> x ei xi + <- v /=.
    have -> : sign_of_expr m x = sign_of_gvar m x; last by apply wi2i_gvarP.
    by rewrite /sign_of_expr /= sign_of_etype_gvar.
  + move=> al aa sz x e he _ xi hxi ei /he{}he <- v.
    apply: on_arr_gvarP => len t htyx hx.
    t_xrbindP => i ve /he {}he /to_intI ? w hget ?; subst ve v.
    by rewrite /= /on_arr_var (wi2i_gvar_nw _ hxi hx) ?htyx //= he //= hget.
  + move=> aa sz len x e he _ xi hxi ei /he{}he <- v.
    apply: on_arr_gvarP => len' t htyx hx.
    t_xrbindP => i ve /he {}he /to_intI ? w hget ?; subst ve v.
    by rewrite /= /on_arr_var (wi2i_gvar_nw _ hxi hx) ?htyx //= he //= hget.
  + move=> al sz x e he ? /andP [/eqP hmx /eqP hte] xi hxi ei /he{}he <- v.
    move=> wx vx gx hptrx we ve /he{}he hptre w hr <- /=.
    rewrite /= (wi2i_variP hxi gx) /sign_of_var hmx /= val_to_int_None.
    rewrite hptrx /= he hte val_to_int_None /= hptre /=.
    by case: heqs => _ <- _; rewrite hr.
  + move=> o e hrec _ hte ei /hrec{}hrec <- v ve he.
    rewrite /wi2i_op1_e; have hse := esubtype_sign_of hte.
    have htve := sem_pexpr_type_of he; apply hrec in he => {hrec}.
    case: is_wi1 (is_wi1P o).
    + move=> [sg [sz|sz|sz|sz|szo szi|sz]] ?; subst o => /=; rewrite /= in hse, hte.
      + rewrite he /sign_of_expr /= hse /sem_sop1 /=; t_xrbindP.
        move=> ? /to_intI -> ?.
        rewrite /wint_of_int; t_xrbindP => hrange <- <- /=.
        by rewrite int_of_word_wrepr.
      + rewrite he /sign_of_expr /= hse /sem_sop1 /=; t_xrbindP.
        move => w /to_wordI [?[?] [? htr ?]]; subst.
        move: htve; rewrite /sign_of_expr => /=.
        case: (sg) hte hse;
          case: etype_of_expr => // -[[] | ] //= ? /eqP ? _ [?]; subst;
          by move: htr; rewrite truncate_word_u => -[->].
      + move: he; rewrite /sign_of_expr hse.
        case: etype_of_expr hte htve hse => //= -[_ | ] // _ /andP[/eqP <- /eqP <-].
        move=> hty _ -> /=.
        rewrite /sem_sop1 /=; t_xrbindP.
        move=> w hw <-.
        have [ ? | [w' ?]] := type_of_valI hty; subst ve => //=.
        move: hw => /=; rewrite truncate_word_u => -[->].
        by rewrite wrepr_int_of_word.
      + rewrite he /sign_of_expr hse /=.
        rewrite val_to_int_None /sem_sop1 /=; t_xrbindP.
        by move=> w hw <-; rewrite hw /=.
      + case:ifP => hsz;
          rewrite /= he /sign_of_expr hse /sem_sop1 /=; t_xrbindP;
          case: (etype_of_expr m e) hte hse htve => //=;
          move=> [sg' | ] // sz' /andP[] /eqP ? /eqP ? _; subst sg' sz';
          move=> /type_of_valI [-> // | [w ->]] /= w';
          rewrite truncate_word_u => -[?] ?; subst w' v => /=.
        + rewrite /sem_word_extend; case: sg => /=.
          + rewrite /sign_extend wsigned_repr //.
            by move: (wsigned_range_m hsz) (wsigned_range w); Lia.lia.
          rewrite /zero_extend wunsigned_repr_small //.
          by move: (wbase_m hsz) (wunsigned_range w); Lia.lia.
        by case: sg => /=; rewrite truncate_word_u /= truncate_word_u /=
           ?wrepr_signed ?wrepr_unsigned.
      rewrite he /sign_of_expr hse /=.
      rewrite /sem_sop1 /=; t_xrbindP.
      case: (etype_of_expr m e) hte hse htve => //=.
      move=> [sg' | ] // sz' /andP[] /eqP ? /eqP ? _; subst sg' sz'.
      move=> /type_of_valI [-> // | [w ->]] /= w'.
      rewrite truncate_word_u => -[<-] w1.
      rewrite /wint_of_int; t_xrbindP => + <- <- /=.
      by move=> h; rewrite int_of_word_wrepr.
    rewrite /= he /sign_of_expr hse => -[-> ->].
    by rewrite !val_to_int_None.
  + move=> o e1 hrec1 e2 hrec2 ei /andP [hte1 hte2].
    move=> ei1 /hrec1{}hrec1 ei2 /hrec2{}hrec2 <- v v1 he1 v2 he2.
    have htve1 := sem_pexpr_type_of he1.
    have htve2 := sem_pexpr_type_of he2.
    have hse1 := esubtype_sign_of hte1.
    have hse2 := esubtype_sign_of hte2.
    have hei1 := hrec1 _ he1; have hei2 := hrec2 _ he2 => {hrec1 hrec2}.
    rewrite /wi2i_op2_e /wi2i_op2.
    case: is_wi2 (is_wi2P o).
    + case => sg [] [] sz ?; subst o;
      rewrite /= hei1 hei2 /= /sem_sop2 /= /mk_sem_wiop2 /wint_of_int; t_xrbindP.
      1-3: by move=> w1 hw1 w2 hw2 w hinr <- <-;
        have ? := esubtype_to_word hte1 htve1 hw1;
        have ? := esubtype_to_word hte2 htve2 hw2; subst v1 v2 => /=;
        rewrite /sign_of_expr hse1 hse2 /= int_of_word_wrepr.
      + move=> w1 hw1 w2 hw2 w; rewrite /mk_sem_divmod.
        case: eqP => //= hw2_0; case: ifPn => // /and3P.
        move=> h [?] ?; subst w v.
        have ? := esubtype_to_word hte1 htve1 hw1.
        have ? := esubtype_to_word hte2 htve2 hw2; subst v1 v2 => /=;
        rewrite /sign_of_expr hse1 hse2 /=.
        move=> {hte2 hte1 hse1 hse2 hei1 hei2 htve1 htve2 he1 he2 hw1 hw2}.
        case: sg h => /=; rewrite /wdiv /wdivi => h.
        + rewrite wsigned_repr //.
          have ? : wsigned w2 <> 0%Z.
          + by move=> heq; apply hw2_0; rewrite -(wrepr_signed w2) heq wrepr0.
          apply: (Z_quot_bound (half_modulues_pos sz) (wsigned_range w1) (wsigned_range w2)) => //.
          move=> [h1 h2]; apply h; split; apply/eqP => //.
          by rewrite -(wrepr_signed w2) h2.
        rewrite wunsigned_repr_small //.
        have ? := wunsigned_range w1; have ? := wunsigned_range w2.
        have ? : wunsigned w2 <> 0%Z.
        + by move=> heq; apply hw2_0; rewrite -(wrepr_unsigned w2) heq wrepr0.
        split; first by apply Z.div_pos; Lia.lia.
        apply Z.div_lt_upper_bound; Lia.nia.
      + move=> w1 hw1 w2 hw2 w; rewrite /mk_sem_divmod.
        case: eqP => //= hw2_0; case: ifPn => // /and3P.
        move=> h [?] ?; subst w v.
        have ? := esubtype_to_word hte1 htve1 hw1.
        have ? := esubtype_to_word hte2 htve2 hw2; subst v1 v2 => /=;
        rewrite /sign_of_expr hse1 hse2 /=.
        move=> {hte2 hte1 hse1 hse2 hei1 hei2 htve1 htve2 he1 he2 hw1 hw2}.
        case: sg h => /=; rewrite /wmod /wmodi => h.
        + rewrite wsigned_repr //.
          have /(Z_rem_bound (wsigned w1)) : (wsigned w2 <> 0)%Z.
          + by move=> heq; apply hw2_0; rewrite -(wrepr_signed w2) heq wrepr0.
          move: (wsigned_range w1) (wsigned_range w2).
          rewrite /wmin_signed /wmax_signed; Lia.lia.
        rewrite wunsigned_repr_small //.
        have ? : wunsigned w2 <> 0%Z.
        + by move=> heq; apply hw2_0; rewrite -(wrepr_unsigned w2) heq wrepr0.
        move: (wunsigned_range w1) (wunsigned_range w2) (Z.mod_pos_bound (wunsigned w1) (wunsigned w2)).
        Lia.lia.
      1-2:
        by move=> w1 hw1 w2 hw2 w; rewrite /mk_sem_wishift /wint_of_int; t_xrbindP;
         move=> hinr <- <-;
         have ? := esubtype_to_word hte1 htve1 hw1;
         have ? := esubtype_to_word hte2 htve2 hw2; subst v1 v2 => /=;
         rewrite /sign_of_expr hse1 hse2 /= int_of_word_wrepr.
      1-6:
        by move=> w1 hw1 w2 hw2 <-;
         have ? := esubtype_to_word hte1 htve1 hw1;
         have ? := esubtype_to_word hte2 htve2 hw2; subst v1 v2 => /=;
         rewrite /sign_of_expr hse1 hse2 /=.
    rewrite /= hei1 hei2 /= /sign_of_expr /= hse1 hse2 => -[-> -> ->].
    by rewrite !val_to_int_None.
  + move=> o es hes ei hall esi /hes{}hes <- /= v vs hsem hvs.
    have hsz := size_mapM hsem.
    have {hes hsem} := hes _ hsem; rewrite /sem_pexprs => -> /=.
    have -> : map2 (λ (e : pexpr) (v0 : value), val_to_int (sign_of_expr m e) v0) es vs = vs.
    + move=> {hvs}; elim: es vs hall hsz => [ | e es hrec] [ | v' vs] //=.
      by move=> /andP[]/eqP -> /hrec h [] /h ->; rewrite val_to_int_None.
    by rewrite hvs /sign_of_expr /= sign_of_to_etype_None val_to_int_None.
  move=> t e he e1 he1 e2 he2 ei_ /andP[] hs1 hs2.
  move=> ei /he{}he ei1 /he1{}he1 ei2 /he2{}he2 <-.
  move=> vr b v hv hb v1' v1 hv1 htr1 v2' v2 hv2 htr2 <-.
  have htve := sem_pexpr_type_of hv.
  have htve1 := sem_pexpr_type_of hv1.
  have htve2 := sem_pexpr_type_of hv2.
  have hse1 := esubtype_sign_of hs1.
  have hse2 := esubtype_sign_of hs2.
  have hei := he _ hv; have hei1 := he1 _ hv1; have hei2 := he2 _ hv2.
  move=> {he he1 he2} /=.
  rewrite hei hei1 hei2 (to_boolI hb) /=.
  rewrite /sign_of_expr hse1 hse2 /wi2i_type.
  case: eqP => hsig.
  + by rewrite hsig !val_to_int_None htr1 htr2.
  have : exists ws sg, [/\ t = sword ws , etype_of_expr m e1 = ETword _ (Some sg) ws &
                                          etype_of_expr m e2 = ETword _ (Some sg) ws ].
  + case: (etype_of_expr m e1) hsig hs1 hs2 => //=;
      try by rewrite sign_of_to_etype_None.
    move=> [sg |] ws; last by rewrite sign_of_to_etype_None.
    case: (t) => //= _ _ /andP [_ /eqP ->].
    case: (etype_of_expr m e2) => // -[] // _ _ /andP[] /eqP <- /eqP <-.
    by exists ws, sg.
  move=> [ws [sg [? heq1 heq2]]]; subst t; rewrite heq1 /=.
  move: htve1 htve2; rewrite heq1 heq2 /=.
  move=> /type_of_valI [? | [w1 ?]]; subst v1 => //.
  move=> /type_of_valI [? | [w2 ?]]; subst v2 => //.
  move: htr1 htr2; rewrite /truncate_val /= !truncate_word_u /=.
  by move=> [] ? [] ?; subst v1' v2'; case: (b).
Qed.

Lemma wi2i_eP e : P e.
Proof. by case wi2i_eP_. Qed.

Lemma wi2i_esP es : Q es.
Proof. by case wi2i_eP_. Qed.

End E.

Lemma sign_to_etype_type_of sg sg' v :
  sign_of_etype (to_etype sg (type_of_val v)) = Some sg' ->
  sg = Some sg' /\
  exists ws, v = undef_w \/ exists (w:word ws), v = Vword w.
Proof.
  have := (@type_of_valI v _ erefl); case: type_of_val => //=.
  move=> ws h; case: sg => // ? [->]; eauto.
Qed.


Lemma is_swordP ty : is_sword ty -> exists ws, ty = sword ws.
Proof. case: ty => //; eauto. Qed.

Lemma wi2i_lvarP_None (x : var_i) s s' si v :
  eqst s si ->
  in_FV_var FV x -> m x = None ->
  write_var true x v s = ok s' ->
  exists2 si', write_var true x v si = ok si' & eqst s' si'.
Proof.
  move=> [?? hvm] hin hmx /write_varP [-> hdb htr].
  exists (with_vm si (evm si).[x <- v]); first by apply/write_varP.
  split => // z hinz.
  case: (v_var x =P z) => [ ? | /eqP hne].
  + by subst z; rewrite /wi2i_var /sign_of_var hmx val_to_int_None !Vm.setP_eq.
  rewrite !Vm.setP_neq //; first by apply hvm.
  rewrite /wi2i_var; case : (m z) (hwf_m z) => [[sg zi] | ] // [_ _ h].
  apply /eqP => ?;  subst zi.
  have:= h x _ hin; rewrite hmx; apply => //.
  by apply/eqP; rewrite eq_sym.
Qed.

Lemma wi2i_lvarP x xi ety s s' si v :
  eqst s si ->
  wi2i_lvar m FV (to_etype (sign_of_etype ety) (type_of_val v)) x = ok xi ->
  write_var true x v s = ok s' ->
  exists2 si' : estate,
      write_var true xi (val_to_int (sign_of_etype (to_etype (sign_of_etype ety) (type_of_val v))) v) si = ok si' &
      eqst s' si'.
Proof.
  rewrite /wi2i_lvar /wi2i_vari; t_xrbindP => heqs hsub hin ? hw; subst xi.
  move: hsub; rewrite /wi2i_vari /wi2i_var /etype_of_var /sign_of_var.
  case heqm: m (hwf_m x) => [[sg xi]| ] /=.
  + move=> [/is_swordP [sw hxty] htxi hdiff] hsub.
    have := (esubtype_sign_of hsub); rewrite hxty /=.
    move/write_varP: hw => [-> hdb htr].
    move=> /(sign_to_etype_type_of) [heq [ws [? | [w ?]]]]; subst.
    + by move: hdb; rewrite /DB.
    move: hsub; rewrite /esubtype hxty heq => /andP[_ /eqP?]; subst sw.
    rewrite /val_to_int /=.
    exists (with_vm si (evm si).[xi <- int_of_word sg w]).
    + by apply/write_varP; split => //=; rewrite htxi.
    case: heqs => ?? hvm.
    split => //= z hz.
    rewrite (Vm.setP _ x); case: eqP => heqx.
    + subst z; rewrite /wi2i_var heqm Vm.setP_eq.
      by rewrite hxty /= cmp_le_refl htxi /sign_of_var heqm.
    rewrite Vm.setP_neq; first by apply hvm.
    by apply/eqP; have := hdiff _ heqx hz; rewrite /wi2i_var; case: m => [[]|].
  move=> _ hsub.
  have := (esubtype_sign_of hsub); rewrite sign_of_to_etype_None => ->.
  by rewrite val_to_int_None; apply: wi2i_lvarP_None hw.
Qed.

Lemma wi2i_lvP ety lv lvi s si s' v:
  eqst s si ->
  let ety := to_etype (sign_of_etype ety) (type_of_val v) in
  wi2i_lv m FV ety lv = ok lvi ->
  write_lval true gd lv v s = ok s' ->
  exists2 si',  write_lval true gd lvi (val_to_int (sign_of_etype ety) v) si = ok si' & eqst s' si'.
Proof.
  move=> heqs; case: lv => /=.
  + move=> i ty [<-] /write_noneP [-> htr hdb]; exists si => //=.
    rewrite /write_none.
    case heq: sign_of_etype => [sg | ] /=.
    + have [_ [ws [ ? | [w ?]]]] := sign_to_etype_type_of heq; subst v.
      + by move: hdb; rewrite /DB.
      by rewrite /val_to_int.
    by rewrite val_to_int_None htr hdb.
  + by move=> x; t_xrbindP => xi /= + <-; apply: wi2i_lvarP.
  + t_xrbindP => a ws x e /and4P [hinx /eqP hmx /eqP hse /eqP hsty].
    move=> ei /(wi2i_eP heqs) he <- wx vx /(wi2i_varP heqs hinx).
    rewrite /sign_of_var /wi2i_var hmx val_to_int_None=> hx htox we ve /he{}he htoe ? htov m' hw <-.
    case heqs => ? hmem ?.
    exists (with_mem si m') => //.
    by rewrite /write_lval hx he /= htox /= hsty hse !val_to_int_None htoe /= htov /= -hmem hw.
  + t_xrbindP => a aa ws x e /and3P[hinx /eqP hse /eqP hsety].
    move=> ei /(wi2i_eP heqs) he <-; apply: on_arr_varP.
    move=> len t htx /(wi2i_varP heqs hinx).
    have hmx : m x = None.
    + by have := hwf_m x; case: m => // -[sg ?] []; rewrite htx.
    rewrite /sign_of_var /wi2i_var hmx val_to_int_None=> hx.
    t_xrbindP => we ve /he{}he htoe ? htov m' hset.
    move=> /(wi2i_lvarP_None heqs hinx hmx) [si' hw heqs']; exists si' => //.
    rewrite /write_lval hx /= he hse hsety !val_to_int_None /=.
    by rewrite htoe /= htov /= hset /= hw.
  t_xrbindP => a aa ws x e /and3P[hinx /eqP hse /eqP hsty].
  move=> ei /(wi2i_eP heqs) he <-; apply: on_arr_varP.
  move=> len t htx /(wi2i_varP heqs hinx).
  have hmx : m x = None.
  + by have := hwf_m x; case: m => // -[sg ?] []; rewrite htx.
  rewrite /sign_of_var /wi2i_var hmx val_to_int_None=> hx.
  t_xrbindP => we ve /he{}he htoe ? htov m' hset.
  move=> /(wi2i_lvarP_None heqs hinx hmx) [si' hw heqs']; exists si' => //.
  by rewrite /write_lval hx /= he hse hsty !val_to_int_None /= htoe htov /= hset /= hw.
Qed.

Lemma wi2i_lvsP E ety lvs lvis s si s' vs:
  eqst s si ->
  mapM2 E (wi2i_lv m FV) ety lvs = ok lvis ->
  write_lvals true gd s lvs vs = ok s' ->
  all2 (fun ety v => ety == (to_etype (sign_of_etype ety) (type_of_val v))) ety vs ->
  exists2 si',
    write_lvals true gd si lvis (map2 (fun ety v => val_to_int (sign_of_etype ety) v) ety vs) = ok si' &
    eqst s' si'.
Proof.
  elim: ety lvs vs lvis s si => [|ety etys hrec] [|lv lvs] //= [|v vs] // ? s si heqs; t_xrbindP.
  + by move=> <- <- _; exists si.
  move=> lvi hlvi lvis hlvis <- s1 hw hws /andP[ /eqP heq hall] /=.
  rewrite heq in hlvi.
  have := wi2i_lvP heqs hlvi hw.
  rewrite -heq => -[si1 -> heqs1 /=].
  have [si' -> heqs2 /=] := hrec _ _ _ _ _ heqs1 hlvis hws hall; eauto.
Qed.

Context (p_funcsi : ufun_decls)
        (sigs : funname → option (seq (extended_type positive) * seq (extended_type positive)))
        (hsig : forall fn fd, get_fundef (p_funcs p) fn = Some fd ->
                  sigs fn = Some
                    (map2 (fun (x:var_i) ty => to_etype (sign_of_var m x) ty) fd.(f_params) fd.(f_tyin),
                     map2 (fun (x:var_i) ty => to_etype (sign_of_var m x) ty) fd.(f_res) fd.(f_tyout)))
        (hp' : forall fn fd, get_fundef (p_funcs p) fn = Some fd ->
               exists2 fdi, wi2i_fun m FV sigs fn fd = ok fdi & get_fundef p_funcsi fn = Some fdi).

Let pi : uprog := {| p_funcs := p_funcsi; p_globs := gd; p_extra := p_extra p |}.

Let Pi_r s (i:instr_r) s' :=
  forall ii, wi2i_ir m FV sigs i = ok ii ->
  forall si, eqst s si ->
  exists2 si', sem_i pi ev si ii si' & eqst s' si'.

Let Pi s (i:instr) s' :=
  forall ii, wi2i_i m FV sigs i = ok ii ->
  forall si, eqst s si ->
  exists2 si', sem_I pi ev si ii si' & eqst s' si'.

Let Pc s (c:cmd) s' :=
  forall ci, mapM (wi2i_i m FV sigs) c = ok ci ->
  forall si, eqst s si ->
  exists2 si', sem pi ev si ci si' & eqst s' si'.

Let Pfor (i:var_i) vs s c s' :=
  in_FV_var FV i ->
  forall ci, mapM (wi2i_i m FV sigs) c = ok ci ->
  forall si, eqst s si ->
  exists2 si', sem_for pi ev i vs si ci si' & eqst s' si'.

Let Pfun scs1 m1 fn vargs scs2 m2 vres :=
  forall fsig, sigs fn = Some fsig ->
  all2 (fun ety v => esubtype ety (to_etype (sign_of_etype ety) (type_of_val v))) fsig.1 vargs ->
  let vargsi := map2 (fun ety v => val_to_int (sign_of_etype ety) v) fsig.1 vargs  in
  let vresi  := map2 (fun ety v => val_to_int (sign_of_etype ety) v) fsig.2 vres in
  sem_call pi ev scs1 m1 fn vargsi scs2 m2 vresi /\
  all2 (fun ety v => ety == (to_etype (sign_of_etype ety) (type_of_val v))) fsig.2 vres.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof. by move=> s ? [<-] si; exists si => //; constructor. Qed.

Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ hi _ hc ? /=; t_xrbindP.
  move=> ii /hi{}hi ci /hc{}hc <- si1 /hi [si2 h1] /hc [si3 h2 heqs2].
  exists si3 => //; apply: Eseq h1 h2.
Qed.

Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Proof.
  move=> i_i i s1 s2 _ hi ? /=; t_xrbindP => ii /add_iinfoP /hi{}hi <- si /hi [si' ??].
  exists si' => //; constructor.
Qed.

Lemma esubtype_truncate v v' ty ety :
  let sg := sign_of_etype ety in
  type_of_val v = to_stype ety ->
  esubtype (to_etype sg ty) ety ->
  truncate_val ty v = ok v' ->
  truncate_val (wi2i_type sg ty) (val_to_int sg v) = ok (val_to_int (sign_of_etype (to_etype sg ty)) v').
Proof.
  move=> /= hty.
  case heq: sign_of_etype => [sg | ]; last by rewrite /wi2i_type eqxx sign_of_to_etype_None !val_to_int_None.
  case: ety {hty} heq (type_of_valI hty) => // -[_|] //= ws [->] h.
  case: ty => //= _ /andP[_ /eqP->] /=.
  case: h => [-> | [w ->]] //.
  by rewrite /truncate_val /= truncate_word_u /= => -[<-].
Qed.

Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s1 s2 x t ty e v v' he htr hw ii /=.
  t_xrbindP => hsub xi hxi ei hei <- si heqs.
  have hsem := wi2i_eP heqs hei he.
  have hty := sem_pexpr_type_of he.
  have ? := truncate_val_has_type htr. subst ty.
  have [si' hw' ?] := wi2i_lvP heqs hxi hw.
  exists si' => //; econstructor; eauto; apply: esubtype_truncate hty hsub htr.
Qed.

Lemma all_None_val_to_int s1 es ve :
  sem_pexprs true gd s1 es = ok ve ->
  all (λ e : pexpr, sign_of_expr m e == None) es ->
  (map2 (λ (e : pexpr) (v : value), val_to_int (sign_of_expr m e) v) es ve) = ve.
Proof.
  move=> /size_mapM.
  elim: es ve => [| e es hes] [| ve ves] //= [] hsz /andP [/eqP -> /(hes _ hsz)] ->.
  by rewrite val_to_int_None.
Qed.

Lemma all2_esubtype_None vs :
  all2
    (λ ety v, ety == to_etype (sign_of_etype ety) (type_of_val v))
      [seq to_etype None ty | ty <- (List.map type_of_val vs)]
      vs.
Proof. by elim: vs => //= v vs ->; rewrite sign_of_to_etype_None eqxx. Qed.

Lemma map2_None_val_to_int vs:
  map2 (λ (ety : extended_type positive) (v : value), val_to_int (sign_of_etype ety) v)
       [seq to_etype None i | i <- List.map type_of_val vs] vs = vs.
Proof. by elim: vs => //= v vs ->; rewrite sign_of_to_etype_None val_to_int_None. Qed.

Local Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move => s1 s2 t o xs es; rewrite /sem_sopn; t_xrbindP => vr ve hes hex hws ii /=.
  t_xrbindP => hall eis heis xis hxis <- si heqs.
  have := wi2i_esP heqs heis hes.
  have -> := all_None_val_to_int hes hall.
  move=> hsem.
  have := wi2i_lvsP heqs hxis hws.
  rewrite -(sopn_toutP hex).
  move=> /(_ (all2_esubtype_None _)); rewrite map2_None_val_to_int => -[si' hws' ?].
  exists si' => //.
  econstructor; eauto.
  by rewrite /sem_sopn hsem /= hex /= hws'.
Qed.

Lemma exec_syscall_toutP scs1 scs2 m1 m2 o vs vs' :
  exec_syscall scs1 m1 o vs = ok (scs2, m2, vs') →
  List.map type_of_val vs' =  scs_tout (syscall_sig_u o).
Proof.
  case: o => len /=.
  rewrite /exec_getrandom_u; case: vs => // v [] //; t_xrbindP.
  by move=> ?? _ ? _ <- /= _ _ <-.
Qed.

Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
Proof.
  move=> s1 scs m1 s2 o xs es ves vs hes hex hws ii /=.
  t_xrbindP => hall eis heis xis hxis <- si heqs.
  have := wi2i_esP heqs heis hes.
  have -> := all_None_val_to_int hes hall.
  move=> hsem.
  pose s1' := with_scs (with_mem s1 m1) scs.
  pose si1' := with_scs (with_mem si m1) scs.
  have heqs1 : eqst s1' si1' by case: heqs.
  have := wi2i_lvsP heqs1 hxis hws.
  rewrite -(exec_syscall_toutP hex).
  move=> /(_ (all2_esubtype_None _)); rewrite map2_None_val_to_int => -[si' hws' ?].
  exists si' => //.
  econstructor; eauto.
  by case: heqs => <- <-.
Qed.

Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 he _ hc ii /=; t_xrbindP.
  move=> ei hei ci1 hci1 ci2 hci2 <- si heqs.
  have /= {}hei := wi2i_eP heqs hei he.
  have [si' h ?] := hc _ hci1 _ heqs.
  by exists si' => //; apply: Eif_true h.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 he _ hc ii /=; t_xrbindP.
  move=> ei hei ci1 hci1 ci2 hci2 <- si heqs.
  have /= {}hei := wi2i_eP heqs hei he.
  have [si' h ?] := hc _ hci2 _ heqs.
  by exists si' => //; apply: Eif_false h.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Proof.
  move=> s1 s2 s3 s4 a c e i_i c' _ hc he _ hc' _ hwh ii hwhi.
  move: (hwhi) => /=; t_xrbindP.
  move=> ei hei ci hci ci' hci' ? si heqs; subst ii.
  have [si2 hc1 heqs2]:= hc _ hci _ heqs.
  have /= {}hei := wi2i_eP heqs2 hei he.
  have [si3 hc2 heqs3] := hc' _ hci' _ heqs2.
  have [si4 hwh' ?] := hwh _ hwhi _ heqs3.
  by exists si4 => //; apply: Ewhile_true hc2 hwh'.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Proof.
  move=> s1 s2 a c e i_i c' _ hc he ii hwhi si heqs.
  move: (hwhi) => /=; t_xrbindP.
  move=> ei hei ci hci ci' hci' ?; subst ii.
  have [si2 hc1 heqs2]:= hc _ hci _ heqs.
  have /= {}hei := wi2i_eP heqs2 hei he.
  by exists si2 => //; apply: Ewhile_false.
Qed.

Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Proof.
  move=> s1 s2 i d lo hi c vlo vhi hlo hhi _ hfor ii /=; t_xrbindP.
  move=> hin loi hloi hii hhii ci hci <- si heqs.
  have /= {}hlo:= wi2i_eP heqs hloi hlo.
  have /= {}hhi:= wi2i_eP heqs hhii hhi.
  have [si' h ?] := hfor hin _ hci _ heqs.
  exists si' => //; econstructor; eauto.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof. move=> s i c _ ci _ si heqs; exists si => //; apply EForDone. Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
Proof.
  move=> s1 s1' s2 s3 i w ws c hw _ hc _ hfor hin ci hci si heqs.
  have hmi : m i = None.
  + case: m (hwf_m i) => // -[sg ii].
    move/write_varP: hw => [] _ _ /vm_truncate_valE [->] _ [] //.
  have [si1 {}hw {}heqs]:= wi2i_lvarP_None heqs hin hmi hw.
  have [si2 {}hc {}heqs]:= hc _ hci _ heqs.
  have [si3 ??]:= hfor hin _ hci _ heqs.
  exists si3 => //; econstructor; eauto.
Qed.

Lemma esubtype_to_etype_eq ety ety' :
  esubtype ety ety' ->
  ety' = to_etype (sign_of_etype ety) (to_stype ety').
Proof.
  by case: ety ety' => [||len|[sg|] ws] [||len'|[sg'|] ws'] //= /andP[/eqP <- /eqP <-].
Qed.

Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
Proof.
  move=> s1 scs2 m2 s2 xs fn args vargs vs hes _ hf hws ii /=; rewrite /get_sig; t_xrbindP.
  move=> fsig; case hgetsig : sigs => [fsig'| ] // [?]; subst fsig'.
  move=> hsub xis hxis eis heis <- si heqs.
  have hes' := wi2i_esP heqs heis hes.
  have /= := hf _ hgetsig.
  have -> : map2 (λ ety v, val_to_int (sign_of_etype ety) v) fsig.1 vargs  =
            map2 (λ e v, val_to_int (sign_of_expr m e) v) args vargs.
  + move=> {hf hes' heis hws hxis}.
    elim: fsig.1 args vargs hsub hes=> [|ety tin hrec] [|e es] //=.
    move=> vargs' /andP[] hsub hall; t_xrbindP => va hva vargs hvargs ?; subst vargs' => /=.
    by rewrite (hrec _ _ hall hvargs) -(esubtype_sign_of hsub).
  move=> [|hsem hsubr].
  + move=> {hf hes' heis hws hxis}.
    elim: fsig.1 args vargs hsub hes => [|ety tin hrec] [|e es] //=.
    + by move=> _ _ [<-].
    move=> vargs' /andP[] hsub hall; t_xrbindP => va hva vargs hvargs ?; subst vargs' => /=.
    by rewrite (sem_pexpr_type_of hva) (hrec _ _ hall hvargs) -(esubtype_to_etype_eq hsub) hsub.
  have heqs2 : eqst (with_scs (with_mem s1 m2) scs2) (with_scs (with_mem si m2) scs2) by case heqs.
  have [si' {}hws ?]:= wi2i_lvsP heqs2 hxis hws hsubr.
  exists si' => //; econstructor; eauto.
  by case: heqs => <- <-.
Qed.

Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
Proof.
  move=> scs1 m1 scs2 m2 fn [fi ftin fparams fbody ftout fres fextra].
  move=> vargs vargs' s0 s1 s2 vres vres' hfun htra [hi] hw _ hc hres hfull hscs hfi.
  rewrite /= in htra hi hw hc hres hfull hfi; subst s0 m2.
  move=> fsig; have [fdi + hfuni] := hp' hfun.
  rewrite /wi2i_fun => /add_funnameP; t_xrbindP.
  rewrite /get_sig (hsig hfun) /= => ? [?]; subst => /=.
  set etyin := map2 _ fparams ftin.
  set etyout := map2 _ fres ftout.
  set ftini := map _ etyin.
  set ftouti := map _ etyout.
  set vargsi' := (map2 (λ ety v, val_to_int (sign_of_etype ety) v) fsig.1 vargs').
  set vargsi := (map2 (λ ety v, val_to_int (sign_of_etype ety) v) fsig.1 vargs).
  set vresi' := (map2 (λ ety v, val_to_int (sign_of_etype ety) v) fsig.2 vres').
  set vresi := (map2 (λ ety v, val_to_int (sign_of_etype ety) v) fsig.2 vres).
  move=> fparamsi hparamsi ci hci fresi hresi ? [?] hsub; subst fdi fsig.
  have : mapM2 ErrType dc_truncate_val ftini vargsi' = ok vargsi /\
         forall s si, eqst s si ->
           write_vars true fparams vargs s = ok s1 ->
           exists2 si1,
             write_vars true fparamsi vargsi si = ok si1 &
             eqst s1 si1.
  + move: htra hsub hparamsi.
    rewrite /ftini /vargsi /vargsi' /ftini /etyin.
    move=> {hw hfuni vresi vresi' vargsi vargsi' hfun ftini etyin hresi}.
    elim: ftin vargs' fparams fparamsi vargs => [|ty tys hrec] [|va vas] [| a params] //= .
    + by move=> _ _ [<-] _ [<-]; split => // s si ? [<-]; exists si.
    t_xrbindP.
    move=> _ _ tva hva tvas hvas <- /andP[hsub hall] ai hai paramsi hparamsi <-.
    rewrite {2}/dc_truncate_val /= to_stypeK.
    have /= := esubtype_truncate _ _ hva.
    move /(_ (to_etype (sign_of_etype (to_etype (sign_of_var m a) ty)) (type_of_val va))).
    rewrite to_stypeK => /(_ erefl).
    have heq : to_etype (sign_of_etype (to_etype (sign_of_var m a) ty)) ty =
               to_etype (sign_of_var m a) ty.
    + by case ty => //= ws; case: sign_of_var.
    have -> := esubtype_sign_of hsub => ->; last by rewrite heq.
    rewrite /=; have [-> hwrec /=] := hrec _ _ _ _ hvas hall hparamsi.
    split; first by rewrite heq.
    t_xrbindP=> s si heqs s' hw hws.
    have := wi2i_lvarP heqs _ hw; rewrite (truncate_val_has_type hva).
    rewrite -sign_of_etype_var in hai => /(_ _ _ hai).
    rewrite sign_of_etype_var.
    by move=> [si' -> heqs'] /=; apply: hwrec heqs' hws.
  have heqs : eqst {| escs := scs1; emem := m1; evm := Vm.init |} {| escs := scs1; emem := m1; evm := Vm.init |}.
  + split => //= z hin.
    rewrite !Vm.initP /wi2i_var /sign_of_var.
    case: m (hwf_m z) => [[sg zi] | ] //=; last by rewrite val_to_int_None.
    by move=> [] /is_swordP [ws ->] -> _ /=; apply undef_x_vundef.
  move=> [hvargsi /(_ _ _ heqs hw) [si1 {}hw heqs1]].
  have [si2 hsemc heqs2] := hc _ hci _ heqs1.
  have [???] : [/\ get_var_is true (evm si2) fresi = ok vresi
                 , mapM2 ErrType dc_truncate_val ftouti vresi = ok vresi'
                 & all2 (λ ety v, ety == to_etype (sign_of_etype ety) (type_of_val v)) etyout vres'].
  + move: hres hfull hresi.
    rewrite /vresi /vresi' /ftouti /etyout.
    move=> {vresi' vresi ftouti etyout hfuni hfun vargsi vargsi' hsub hvargsi hw heqs}.
    elim: fres vres fresi ftout vres' => [|r rs hrec] /=.
    + move=> ? ? ftout ? [<-] + [<-].
      by case: ftout => //= -[<-].
    t_xrbindP => vres fresi ftout vres' v hr vs hrs <-.
    case: ftout => //= ty tys; t_xrbindP.
    move=> tv htv tvs htvs <- ri hsub hri ris hris <- /=.
    have -> := wi2i_variP heqs2 hri hr.
    have [-> -> -> /=]:= hrec _ _ _ _ hrs htvs hris.
    rewrite -(esubtype_sign_of hsub) sign_of_etype_var.
    have -> := truncate_val_has_type htv; rewrite eqxx; split => //.
    have /= := esubtype_truncate _ _ htv.
    rewrite -sign_of_etype_var in hsub.
    move=> /(_ _ (get_var_type_of hr) hsub).
    by rewrite -(esubtype_sign_of hsub) sign_of_etype_var to_stypeK /dc_truncate_val /= => -> /=.
  by case: heqs2 => *; split => //; econstructor; eauto.
Qed.

Definition wi2w_callP_aux :=
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

End M.

Section FINAL.

Context (info : var → option (signedness * var)).

Lemma build_infoP FV m :
  build_info info FV = ok m ->
  wf_m m FV /\ forall x, Sv.In x FV -> m x = info x.
Proof.
  rewrite /build_info; t_xrbindP => -[FV' m'] /= + <-.
  set f := (f in foldM f _ _).
  have :
    forall xs (xs':seq var) FV1 FV2 m1 m2,
      Sv.Subset FV FV1 →
      (forall x, x \in xs → Sv.In x FV) →
      (forall x, Sv.In x FV → (x \in xs') || (x \in xs)) →
      (forall x, x \in xs' → Mvar.get m1 x = info x) →
      (forall x xi, Mvar.get m1 x = Some xi -> x \in xs' /\ Sv.In xi.2 FV1) →
      wf_m (Mvar.get m1) FV →
      foldM f (FV1, m1) xs = ok (FV2, m2) →
      wf_m (Mvar.get m2) FV ∧ ∀ x : Sv.elt, Sv.In x FV → Mvar.get m2 x = info x.
  + elim => [| x xs hrec] xs' FV1 FV2 m1 m2 hsub hin hor hget hget' hwf /=.
    + by move=> [_ <-]; split => // x /hor; rewrite orbC => /hget.
    t_xrbindP => -[FV1' m1']; rewrite {1}/f.
    case heq: info => [[sg xi] | ]; last first.
    + move=> [<- <-] /(hrec (x::xs')) [] //.
      + by move=> z hz; apply hin; rewrite in_cons hz orbT.
      + by move=> z /hor; rewrite !in_cons; case: eqP.
      + move=> z; rewrite in_cons => /orP [/eqP |] ?; last by apply hget.
        subst z; case h : Mvar.get => [ xi| //].
        by rewrite -h; apply hget; case: (hget' _ _ h).
      by move=> z xi /hget' []; rewrite in_cons => ->; rewrite orbT.
    case hw: is_word_type => [ws|] //=; t_xrbindP => /andP[/eqP htxi /Sv_memP hxi].
    have htx := is_word_typeP hw.
    move=> <- <- /(hrec (x::xs')) [] //.
    + by SvD.fsetdec.
    + by move=> z hz; apply hin; rewrite in_cons hz orbT.
    + by move=> z /hor; rewrite !in_cons; case: eqP.
    + move=> z; rewrite in_cons Mvar.setP eq_sym.
      case: eqP => /=; first by move=> <-; rewrite heq.
      by move=> _; apply hget.
    + move=> z sz; rewrite Mvar.setP; case: eqP.
      + by move=> <- [<-]; rewrite in_cons eqxx; split => //=; SvD.fsetdec.
      by rewrite in_cons => _ /hget' [] ->; rewrite orbT; split => //; SvD.fsetdec.
    move=> z; rewrite Mvar.setP; case: eqP => [<- | hne].
    + rewrite htx; split => //.
      move=> y hxy hiny.
      rewrite Mvar.setP_neq; last by apply/eqP.
      case: Mvar.get (hget' y).
      + by move=> [sy yi] /(_ _ erefl) /= [_ hinyi] heqy; apply hxi; rewrite heqy.
      move=> _ heqy;apply hxi; rewrite heqy.
      move/Sv_memP: hiny; SvD.fsetdec.
    have := hwf z.
    case heqz: Mvar.get => [[sgz zi] | ] => //.
    move=> [?? h]; split => // y hzy hiny.
    rewrite Mvar.setP; case: eqP => hxy; last by apply h.
    by have [/= _ hinzi]:= hget' _ _ heqz; SvD.fsetdec.
  move=> h {}/h -/(_ [::]) [] //.
  + by move=> ? /Sv_elemsP.
  by move=> ? /Sv_elemsP ->.
Qed.

Lemma wi2w_callP p' :
  wi2i_prog info p = ok p' ->
  forall fn fd, get_fundef (p_funcs p) fn = Some fd ->
  forall scs m vargs scs' m' vres,
    let fsig := (build_sig info (fn, fd)).2 in
    all2 (λ ety v, esubtype ety (to_etype (sign_of_etype ety) (type_of_val v))) fsig.1 vargs ->
    let vargsi := map2 (λ ety v, val_to_int (sign_of_etype ety) v) fsig.1 vargs in
    let vresi  := map2 (λ ety v, val_to_int (sign_of_etype ety) v) fsig.2 vres in
    sem_call p ev scs m fn vargs scs' m' vres ->
    sem_call p' ev scs m fn vargsi scs' m' vresi.
Proof.
  rewrite /wi2i_prog; t_xrbindP.
  move=> M /build_infoP [hwf_m hMeq].
  move=> p_funcsi heqp'.
  have hp' := get_map_cfprog_name_gen heqp'.
  move=> <- fn fd hfn scs m vargs scs' m' vres hargs hsem.
  have hsigs : ∀ fn fd,
    get_fundef (p_funcs p) fn = Some fd →
    get_fundef [seq build_sig info i | i <- p_funcs p] fn =
       Some
          (map2 (λ (x : var_i) (ty : stype), to_etype (sign_of_var M x) ty) (f_params fd) (f_tyin fd),
           map2 (λ (x : var_i) (ty : stype), to_etype (sign_of_var M x) ty) (f_res fd) (f_tyout fd)).
  + move=> fn' fd' hfn'.
    rewrite /get_fundef assoc_mapE; last by move=> ? [].
    rewrite -/(get_fundef (p_funcs p) fn') hfn' /= /build_sig.
    case: fd' hfn' => /= finfo ftyin fparams fbody ftyout fres fextra hfn'.
    have heq : forall xs ty,
      (forall x, x \in map v_var xs -> Sv.In x (vars_p (p_funcs p))) ->
      map2 (λ (x : var_i) (ty : stype), to_etype (sign_of_var info x) ty) xs ty =
      map2 (λ (x : var_i) (ty : stype), to_etype (sign_of_var M x) ty) xs ty.
    + elim => [|x xs hrec] [|t ts] => //= hin.
      rewrite hrec.
      + by rewrite /sign_of_var hMeq //; apply hin; rewrite in_cons eqxx.
      by move=> z h; apply hin; rewrite in_cons h orbT.
    have /(_ _ _ _ hfn') := [elaborate vars_pP].
    rewrite /vars_fd /=.
    have vars_lP: forall l, Sv.Equal (vars_l l) (sv_of_list v_var l).
    + by elim => //= ?? ->; rewrite sv_of_list_cons.
    rewrite !vars_lP => hsub.
    by rewrite !heq // => z /sv_of_listP; SvD.fsetdec.
  have hsig : get_fundef [seq build_sig info i | i <- p_funcs p] fn = Some (build_sig info (fn, fd)).2.
  + rewrite /get_fundef assoc_mapE; last by move=> ? [].
    by rewrite -/(get_fundef (p_funcs p) fn) hfn.
  by have /= [] := wi2w_callP_aux hwf_m hsigs hp' hsem hsig hargs.
Qed.

End FINAL.
End PROOF.
