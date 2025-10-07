From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg word_ssrZ.
Require Import compiler_util psem psem_facts.
Require Import wint_int safety_shared_proof.
Import Utf8.

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
#[local] Existing Instance withassert.
Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

(* ------------------------------------------------- *)

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

Definition eqvm (_:unit) (vmi vm : Vm.t) :=
  forall x, in_FV_var FV x -> vmi.[wi2i_var m x] = val_to_int (sign_of_var m x) vm.[x].

Definition eqst := st_rel eqvm.

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
  | Some(s, sz, oi) => o = Owi2 s sz oi
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
  end; case => //=.
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
  + move=> > _ _ > _ htr1 > _ htr2 <-.
    rewrite to_stypeK; case: ifP => _; eauto using truncate_val_has_type.
  + move => ? o > _ _ > _ _ acc ? _ /truncate_val_has_type.
    elim : ziota acc.
    + by move => //= ? h [] <-; rewrite h e_type_of_op2.
    move => > hi acc /=; t_xrbindP => ? > ???.
    rewrite /sem_sop2;t_rbindP => [[<-]].
    apply: hi.
    rewrite type_of_to_val; clear.
    by case: o => //;
       match goal with
       | |- signedness -> wsize -> _ => move=> ??
       | |- signedness -> _ => move=> ?
       | _ => idtac
       end; case.
  all: by move=> > *; subst.
Qed.

Lemma wrepr_int_of_word sz sg (w:word sz) :
  wrepr sz (int_of_word sg w) = w.
Proof. by case: sg => /=; rewrite ?wrepr_signed ? wrepr_unsigned. Qed.

Lemma sem_op2_type_of o v v1 v2 :
  sem_sop2 o v1 v2 = ok v ->
  type_of_val v = (type_of_op2 o).2.
Proof.
  rewrite /sem_sop2; t_xrbindP => //= ? _ ? _ ? _ <-.
  by rewrite type_of_to_val.
Qed.

Lemma wi2i_lvarP_None d (x : var_i) si si' s v :
  eqst d si s ->
  in_FV_var FV x -> m x = None ->
  write_var true x v si = ok si' ->
  exists2 s', write_var true x v s = ok s' & eqst d si' s'.
Proof.
  move=> [?? hvm] hin hmx /write_varP [-> hdb htr].
  exists (with_vm s (evm s).[x <- v]); first by apply/write_varP.
  split => // z hinz.
  case: (v_var x =P z) => [ ? | /eqP hne].
  + by subst z; rewrite /wi2i_var /sign_of_var hmx val_to_int_None !Vm.setP_eq.
  rewrite !Vm.setP_neq //; first by apply hvm.
  rewrite /wi2i_var; case : (m z) (hwf_m z) => [[sg zi] | ] // [_ _ h].
  apply /eqP => ?;  subst zi.
  have:= h x _ hin; rewrite hmx; apply => //.
  by apply/eqP; rewrite eq_sym.
Qed.

Section E.

Let P e :=
  forall ei, wi2i_e m FV e = ok ei ->
  forall v si s, eqst tt si s ->
    sem_cond gd (eands ei.1) si = ok true ->
    sem_pexpr true gd si ei.2 = ok v ->
    exists2 v', sem_pexpr true gd s e = ok v'
              & v = val_to_int (sign_of_expr m e) v'.

Let Q es :=
  forall eis, wi2i_es (wi2i_e m FV) es = ok eis ->
  forall vs si s, eqst tt si s ->
    sem_cond gd (eands eis.1) si = ok true ->
    sem_pexprs true gd si eis.2 = ok vs ->
    exists2 vs', sem_pexprs true gd s es = ok vs'
               & vs = map2 (fun e v => val_to_int (sign_of_expr m e) v) es vs'.

Lemma wi2i_varP (x: var) v si s :
  eqst tt si s ->
  in_FV_var FV x ->
  get_var true (evm si) (wi2i_var m x) = ok v ->
  exists2 v', get_var true (evm s) x = ok v'
            & v = val_to_int (sign_of_var m x) v'.
Proof.
  move=> heqs hin; case heqs => _ _ /(_ x hin); rewrite /wi2i_var /sign_of_var.
  case hm : m (hwf_m x) => [ [sg xi] | ]; last first.
  + by rewrite !val_to_int_None /get_var => _ ->; exists v => //=; rewrite val_to_int_None.
  move=> [] hty htyi _ hto.
  move=> /get_varP [/= -> hdb hcomp]; rewrite /get_var /=.
  rewrite hto is_defined_val_to_int in hdb |- *; rewrite hdb /=.
  by exists (evm s).[x].
Qed.

Lemma wi2i_variP x xi v si s :
  eqst tt si s ->
  wi2i_vari m FV x = ok xi ->
  get_var true (evm si) xi = ok v ->
  exists2 v', get_var true (evm s) x = ok v'
            & v = val_to_int (sign_of_var m x) v'.
Proof. by move => heqs; rewrite /wi2i_vari; t_xrbindP => + <-; apply wi2i_varP. Qed.

Lemma wi2i_vari_nw (x:var_i) xi v si s :
  eqst tt si s ->
  ~is_sword (vtype x) ->
  wi2i_vari m FV x = ok xi ->
  get_var true (evm si) xi = ok v ->
  get_var true (evm s) x = ok v.
Proof.
  move=> heqs hty hto hget; have [v' -> ->] := wi2i_variP heqs hto hget.
  have -> : sign_of_var m x = None; last by rewrite val_to_int_None.
  rewrite /sign_of_var.
  by case: m (hwf_m x) => // -[sg ?] []?; elim hty.
Qed.

Lemma wi2i_gvarP x xi v si s :
  eqst tt si s ->
  wi2i_gvar m FV x = ok xi ->
  get_gvar true gd (evm si) xi = ok v ->
  exists2 v', get_gvar true gd (evm s) x = ok v'
            & v = val_to_int (sign_of_gvar m x) v'.
Proof.
  move=> heqs; rewrite /wi2i_gvar /get_gvar /sign_of_gvar; case: ifP.
  + by move=> /= _; t_xrbindP => ? + <- /=; apply wi2i_variP.
  by move=> h [<-]; rewrite h => ->; exists v => //; rewrite val_to_int_None.
Qed.

Lemma wi2i_gvar_nw x xi v si s :
  eqst tt si s ->
  ~is_sword (vtype (gv x)) ->
  wi2i_gvar m FV x = ok xi ->
  get_gvar true gd (evm si) xi = ok v ->
  get_gvar true gd (evm s) x = ok v.
Proof.
  move=> heqs hty hto hget; have [v' -> ->] := wi2i_gvarP heqs hto hget.
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

Lemma wi2i_var_type x :
  in_FV_var FV x → vtype (wi2i_var m x) ≠ sint → vtype x = vtype (wi2i_var m x).
Proof.
  by rewrite /wi2i_var; have := hwf_m x; case: (m x) => // -[sg x'] [_ ->].
Qed.

Lemma wi2i_vari_type x xi:
  wi2i_vari m FV x = ok xi → vtype xi ≠ sint → vtype x = vtype xi.
Proof. by rewrite /wi2i_vari; t_xrbindP => hin <- /=; apply wi2i_var_type. Qed.

Lemma wi2i_gvar_type x xi:
  wi2i_gvar m FV x = ok xi -> vtype (gv xi) <> sint -> vtype (gv x) = vtype (gv xi).
Proof.
  rewrite /wi2i_gvar; case: ifP.
  + by t_xrbindP => hloc z + <- /=; apply wi2i_vari_type.
  by move=> _ [<-].
Qed.

Lemma subtype_twint sg sz t : esubtype (twint sg sz) t -> t = twint sg sz.
Proof. by case: t => //= -[] // ??/andP[/eqP -> /eqP ->]. Qed.

Lemma esubtype_of_val et t v1 v1':
  esubtype (to_etype (sign_of_etype et) t) et ->
  of_val (wi2i_type (sign_of_etype et) t) (val_to_int (sign_of_etype et) v1) = ok v1' ->
  type_of_val v1 = to_stype et ->
  exists2 v, of_val t v1 = ok v & to_val v1' = val_to_int (sign_of_etype et) (to_val v).
Proof.
  move=> hsub htr htyof.
  have hse := esubtype_sign_of hsub.
  move: v1' htr. rewrite /sign_of_expr hse /wi2i_type.
  case: eqP => hsig.
  + by rewrite hsig val_to_int_None => v1' ->; exists v1' => //; rewrite val_to_int_None.
  have [ws [sg [heq1 ?]]] : exists ws sg, t = sword ws /\ et = ETword _ (Some sg) ws.
  + case: (et) hsig hsub => //=; try by rewrite sign_of_to_etype_None.
    move=> [sg |] ws; last by rewrite sign_of_to_etype_None.
    case: (t) => //= _ _ /andP [_ /eqP ->].
    by exists ws, sg.
  subst t et => /=.
  have [? | [w ?]] := type_of_valI htyof; subst v1 => //=.
  rewrite truncate_word_u => v1' -[<-] /=.
  by eexists; first reflexivity.
Qed.

Lemma esubtype_truncate_val et t v1 v1':
  esubtype (to_etype (sign_of_etype et) t) et ->
  truncate_val (wi2i_type (sign_of_etype et) t) (val_to_int (sign_of_etype et) v1) = ok v1' ->
  type_of_val v1 = to_stype et ->
  exists2 v, truncate_val t v1 = ok v & v1' = val_to_int (sign_of_etype et) v.
Proof.
  rewrite /truncate_val; t_xrbindP => hsub v1_ hof <- htyof.
  have [v -> /= ->] := esubtype_of_val hsub hof htyof; eauto.
Qed.

Lemma wi2i_type_of_op2 o :
  let et := etype_of_op2 o in
  let t := type_of_op2 (wi2i_op2 o) in
  [/\ t.1.1 = wi2i_type (sign_of_etype et.1.1) (to_stype et.1.1)
    , t.1.2 = wi2i_type (sign_of_etype et.1.2) (to_stype et.1.2)
    & t.2 = wi2i_type (sign_of_etype et.2) (to_stype et.2)].
Proof.
  have l1 : ∀ o, type_of_opk o = wi2i_type (sign_of_etype (etype_of_opk o)) (to_stype (etype_of_opk o)).
  + by case.
  case: o => //= s w [] //=.
Qed.

Lemma to_etype_to_stype et : to_etype (sign_of_etype et) (to_stype et) = et.
Proof. by case: et => // -[]. Qed.

Lemma e_type_of_op2' o :
  let et := etype_of_op2 o in
  let t := type_of_op2 o in
  [/\ t.1.1 = to_stype et.1.1
    , t.1.2 = to_stype et.1.2
    & t.2   = to_stype et.2].
Proof. by rewrite /= (e_type_of_op2 o) /=. Qed.

Lemma esubtype_refl et : esubtype et et.
Proof. by case: et => //= -[] // >; rewrite !eqxx. Qed.

Lemma wi2i_op2P si s t1 t2 o e1 e2 v1 v2 v :
  eqst tt si s →
  esubtype (etype_of_op2 o).1.1 t1 →
  esubtype (etype_of_op2 o).1.2 t2 →
  match to_stype t1 with
  | sbool => ∃ b : bool, v1 = Vbool b
  | sint => ∃ i0 : Z, v1 = Vint i0
  | sarr len => ∃ a : WArray.array len, v1 = Varr a
  | sword ws => ∃ w : word ws, v1 = Vword w
  end →
  match to_stype t2 with
  | sbool => ∃ b : bool, v2 = Vbool b
  | sint => ∃ i0 : Z, v2 = Vint i0
  | sarr len => ∃ a : WArray.array len, v2 = Varr a
  | sword ws => ∃ w : word ws, v2 = Vword w
  end →
  sem_pexpr true gd si e1 = ok (val_to_int (sign_of_etype t1) v1) →
  sem_pexpr true gd si e2 = ok (val_to_int (sign_of_etype t2) v2) →
  sem_cond gd (eands (sc_op2 o e1 e2)) si = ok true →
  sem_sop2 (wi2i_op2 o) (val_to_int (sign_of_etype t1) v1) (val_to_int (sign_of_etype t2) v2) =  ok v →
  exists2 v' : value,
     sem_sop2 o v1 v2 = ok v' & v = val_to_int (sign_of_etype (etype_of_op2 o).2) v'.
Proof.
  move=> heqs hsub1 hsub2 hv1 hv2 he1 he2.
  rewrite /sc_op2 /wi2i_op2 (esubtype_sign_of hsub1) (esubtype_sign_of hsub2) .
  case: is_wi2 (is_wi2P o) => [[[sg sz] wio] | ]; last first.
  + case: etype_of_op2 => -[t1' t2' tout] /= [-> -> ->] _.
    by rewrite !val_to_int_None => ->; exists v => //; rewrite val_to_int_None.
  move=> ?; subst o; rewrite /sc_wiop2.
Opaque esubtype.
  case: wio hsub1 hsub2 => /= /subtype_twint hsub1 /subtype_twint hsub2; subst t1 t2;
    move: hv1 hv2 he1 he2 => /= -[w1 ?] [w2 ?]; subst v1 v2 => /= he1 he2.
  1-3:
    rewrite eandsE_1 /sem_sop2 /sc_wi_range_op2 /= => hsc [<-];
    rewrite !truncate_word_u /= /mk_sem_wiop2 (sc_wi_range_of_int _ hsc) /=;
    [ eexists; first reflexivity;
      by rewrite /= (sc_int_of_word_wrepr _ hsc) //= he1 he2
    | by rewrite he1 he2].
  + rewrite /sem_sop2 /= => hsc [<-]; rewrite !truncate_word_u /=.
    have {}hsc:= sem_sc_divmod he1 he2 hsc; rewrite /mk_sem_divmod hsc /= => {he1 he2}.
    move/negbT:hsc; rewrite negb_or => /andP [/eqP hw2 hnand].
    eexists; first reflexivity.
    rewrite /=; case: sg hnand => /= /negP hnand.
    + rewrite wsigned_repr //.
      have ? : wsigned w2 <> 0%Z.
      + by move=> heq; apply hw2; rewrite -(wrepr_signed w2) heq wrepr0.
      apply: (Z_quot_bound (half_modulus_pos sz) (wsigned_range w1) (wsigned_range w2)) => //.
      move=> [h1 h2]; apply/hnand/andP;split; apply/eqP => //.
      by rewrite -(wrepr_signed w2) h2.
    rewrite wunsigned_repr_small //.
    have ? := wunsigned_range w1; have ? := wunsigned_range w2.
    have ? : wunsigned w2 <> 0%Z.
    + by move=> heq; apply hw2; rewrite -(wrepr_unsigned w2) heq wrepr0.
    split; first by apply Z.div_pos; Lia.lia.
    apply Z.div_lt_upper_bound; Lia.nia.
  + rewrite /sem_sop2 /= => hsc [<-]; rewrite !truncate_word_u /=.
    have {}hsc:= sem_sc_divmod he1 he2 hsc; rewrite /mk_sem_divmod hsc /= => {he1 he2}.
    move/negbT:hsc; rewrite negb_or => /andP [/eqP hw2 hnand].
    eexists; first reflexivity.
    rewrite /=; case: sg hnand => /= /negP hnand.
    + rewrite wsigned_repr //.
      have /(Z_rem_bound (wsigned w1)) : (wsigned w2 <> 0)%Z.
      + by move=> heq; apply hw2; rewrite -(wrepr_signed w2) heq wrepr0.
      move: (wsigned_range w1) (wsigned_range w2).
      by rewrite /wmin_signed /wmax_signed; Lia.lia.
    rewrite wunsigned_repr_small //.
    have ? : wunsigned w2 <> 0%Z.
    + by move=> heq; apply hw2; rewrite -(wrepr_unsigned w2) heq wrepr0.
    move: (wunsigned_range w1) (wunsigned_range w2) (Z.mod_pos_bound (wunsigned w1) (wunsigned w2)).
    Lia.lia.
  + rewrite eandsE_1 /sem_sop2 /= => hsc [<-];
    rewrite !truncate_word_u /= /mk_sem_wishift (sc_wi_range_of_int _ hsc) /=;
    [ eexists; first reflexivity;
      by rewrite /= (sc_int_of_word_wrepr _ hsc) //= he1 he2
    | by rewrite he1 he2 ].
  + move=> _; rewrite /sem_sop2 /= => -[?]; subst v.
    rewrite !truncate_word_u /= /mk_sem_wishift /wint_of_int.
    have hin := in_wint_range_zasr sg w1 w2.
    rewrite hin /=; eexists; first reflexivity.
    by rewrite /= int_of_word_wrepr.
  all: by move=> _; rewrite /sem_sop2 /= !truncate_word_u /= => -[<-];
    eexists; first reflexivity; rewrite val_to_int_None.
Qed.

Lemma wi2i_eP_ : (forall e, P e) /\ (forall es, Q es).
Proof.
  apply: pexprs_ind_pair; rewrite /P /Q; split => //=; t_xrbindP.
  + by move=> ? [<-] /= ? si s heqs _ [<-]; eauto.
  + move=> e he es hes ?; rewrite /wi2i_es /=; t_xrbindP.
    move=> ? ei /he{}he eis heis <- <- /= vs si s heqs.
    move=> /eandsE_cat [hei1 heis1]; t_xrbindP => ? hei2 ? heis2 <-.
    have [v' -> -> /=] := he _ _ _ heqs hei1 hei2.
    have {}heis: wi2i_es (wi2i_e m FV) es = ok (flatten (unzip1 eis), unzip2 eis).
    + by rewrite /wi2i_es heis.
    have [vs' -> -> /=]:= hes _ heis _ _ _ heqs heis1 heis2.
    by eexists; first reflexivity.
  1-3: by move=> ?? <- ??? heqs /= _ [<-]; eexists; first reflexivity.
  + move=> x ei xi + <- v /= si s heqs _.
    have -> : sign_of_expr m x = sign_of_gvar m x; last by apply wi2i_gvarP.
    by rewrite /sign_of_expr /= sign_of_etype_gvar.
  + move=> al aa sz x e he _ /eqP htye xi hxi ei /he{}he <- v si s heqs /= hsc.
    apply: on_arr_gvarP => len t htyx hx.
    t_xrbindP => i ve /he {}he /to_intI ? w hget ?; subst ve v.
    rewrite /= /on_arr_var (wi2i_gvar_nw heqs _ hxi hx) /=; last first.
    + by rewrite (wi2i_gvar_type hxi) htyx.
    have [v' -> /=]:= he _ heqs hsc.
    rewrite htye val_to_int_None => <- /=.
    by rewrite hget /=; eexists; first reflexivity.
  + move=> aa sz len x e he _ /eqP htye xi hxi ei /he{}he <- v si s heqs /= hsc.
    apply: on_arr_gvarP => len' t htyx hx.
    t_xrbindP => i ve /he {}he /to_intI ? w hget ?; subst ve v.
    rewrite /= /on_arr_var (wi2i_gvar_nw heqs _ hxi hx) /=; last first.
    + by rewrite (wi2i_gvar_type hxi) htyx.
    have [v' -> /=]:= he _ heqs hsc.
    rewrite htye val_to_int_None => <- /=.
    by rewrite hget /=; eexists; first reflexivity.
  + move=> al sz e he ? /eqP hte ei /he{}he <- v si s heqs /= hsc; t_xrbindP.
    move=> we ve /he{}he hptre w hr <- /=.
    have [v' ->]:= he _ heqs hsc.
    rewrite hte val_to_int_None => <- /=; rewrite hptre /=.
    by case: heqs => _ <- _; rewrite hr /=; eexists; first reflexivity.
  + move=> o e hrec _ hte ei /hrec{}hrec <- v si s heqs /= /eandsE_cat [hei1 hsco] hei2.
    have hse := esubtype_sign_of hte.
    move: hsco hei2; rewrite /sc_op1 /wi2i_op1_e.
    case: is_wi1 (is_wi1P o); last first.
    + move=> hoty _ /=; t_xrbindP => ve hei2.
      have [v' he] := hrec _ _ _ heqs hei1 hei2.
      have htve := sem_pexpr_type_of he.
      rewrite he => -> /=; rewrite /sign_of_expr hse.
      case heq: etype_of_op1 hoty => [ty1 ty2] /= [hty1 hty2].
      rewrite heq /= hty1 hty2 val_to_int_None => ->.
      by exists v => //; rewrite val_to_int_None.

    move=> [sg [sz|sz|sz|sz|szo szi|sz]] ?; subst o => /=; rewrite /= in hse, hte.
    + rewrite eandsE_1 => hsc hei2.
      have [v' he heq] := hrec _ _ _ heqs hei1 hei2; subst v.
      move: hei2; rewrite he /= /sign_of_expr /= hse /sem_sop1 /= val_to_int_None.
      case: etype_of_expr hte (sem_pexpr_type_of he)=> //= _.
      move=> /(sem_pexpr_tovI he) [i ?]; subst v' => /= hei.
      rewrite (sc_wi_range_of_int hei hsc) /=; eexists; first reflexivity.
      by rewrite /= (sc_int_of_word_wrepr hei hsc).
    + move=> _ /(hrec _ _ _ heqs hei1) [v' he ?]; subst v.
      rewrite he /sign_of_expr /= hse /sem_sop1 /=.
      have := sem_pexpr_type_of he.
      case: etype_of_expr hse hte => //= -[] //??[->]/andP[_ /eqP<-].
      move=> /(sem_pexpr_tovI he) [w' ->] /=; rewrite truncate_word_u /=.
      eexists; first reflexivity.
      by rewrite val_to_int_None.
    + move=> _; rewrite /sem_sop1 /=; t_xrbindP.
      move=> vi /(hrec _ _ _ heqs hei1) [v' he ?]; subst vi; rewrite he /=.
      have /(sem_pexpr_tovI he) := sem_pexpr_type_of he; rewrite /sign_of_expr.
      case: etype_of_expr hse hte => //= -[] // ?? [->]/andP[_ /eqP<-] [w ?]; subst v' => /=.
      move=> _ [<-] ?; rewrite wint_of_int_of_word => -[<-] <-; rewrite truncate_word_u /=.
      eexists; first reflexivity.
      by rewrite val_to_int_None.
    + move=> _; rewrite /sem_sop1 /=; t_xrbindP.
      move=> vi /(hrec _ _ _ heqs hei1) [v' he ?]; subst vi; rewrite he /=.
      have /(sem_pexpr_tovI he) := sem_pexpr_type_of he; rewrite /sign_of_expr.
      case: etype_of_expr hse hte => //= -[] // ?? hle [w ?] w'; subst v'.
      rewrite val_to_int_None /= => -> <- /=.
      by eexists; first reflexivity.
    + move=> _; case:ifP => hsz.
      + move=> /(hrec _ _ _ heqs hei1) [v' he ?]; subst v; rewrite he /=.
        rewrite /sem_sop1 /sign_of_expr /=.
        have /(sem_pexpr_tovI he) := sem_pexpr_type_of he; rewrite /sign_of_expr.
        case: etype_of_expr hse hte => //= -[] // ?? [->]/andP[_ /eqP<-] [w ?]; subst v' => /=.
        rewrite truncate_word_u /=; eexists; first reflexivity.
        rewrite /= /sem_word_extend; case: sg => /=.
        + rewrite /sign_extend wsigned_repr //.
          by move: (wsigned_range_m hsz) (wsigned_range w); Lia.lia.
        rewrite /zero_extend wunsigned_repr_small //.
        by move: (wbase_m hsz) (wunsigned_range w); Lia.lia.
      rewrite /= /sem_sop1 /=; t_xrbindP.
      move=> v0 ? v1 /(hrec _ _ _ heqs hei1) [v' he ?]; subst v1.
      have /(sem_pexpr_tovI he) := sem_pexpr_type_of he; rewrite /sign_of_expr.
      case: etype_of_expr hse hte => //= -[] // ?? [->]/andP[_ /eqP<-] [w ?]; subst v' => /=.
      move=> _ [<-] <-; rewrite he /= truncate_word_u /=.
      move=> w3 hw3 w4 hw4 hto w5 hto' ?; subst v.
      eexists; first reflexivity.
      case: sg w3 hw3 w4 hw4 hto hto'=> /=; rewrite truncate_word_u => w3 [?] w4 [?] ?; subst w3 w4 v0;
      rewrite /= truncate_word_u => -[<-].
      + by rewrite wrepr_signed.
      by rewrite wrepr_unsigned.
    move=> hsc; rewrite /sem_sop1 /=; t_xrbindP => vei hei2.
    have [v' he ?] := hrec _ _ _ heqs hei1 hei2; subst vei.
    rewrite he /=.
    have /(sem_pexpr_tovI he) := sem_pexpr_type_of he; rewrite /sign_of_expr.
    move: hei2; rewrite /sign_of_expr.
    case: etype_of_expr hse hte => //= -[] // ?? [->]/andP[_ /eqP<-] hei2 [w ?]; subst v' => /=.
    move=> _ [<-] <- /=; rewrite truncate_word_u /=.
    case: sg hei2 hsc => /=; rewrite eandsE_1 => hei2.
    + rewrite (eneqiP (i2:= wmin_signed sz) hei2) // => -[/eqP h].
      rewrite /wint_of_int /= /in_wint_range /=.
      have -> /= : in_sint_range sz (- wsigned w).
      + rewrite /in_sint_range; have := wsigned_range w.
        move: h; rewrite /wmin_signed /wmax_signed => ??.
        by apply/andP;split; apply/ZleP; Lia.lia.
      eexists; first reflexivity.
      by rewrite /= wrepr_opp wrepr_signed wsigned_opp.
    rewrite (eeqiP (i2:= 0%Z) hei2) // => -[/eqP ->] /=.
    by eexists; first reflexivity.

  + move=> o e1 hrec1 e2 hrec2 ei /andP [hte1 hte2].
    move=> ei1 hei1 ei2 hei2 <- /= v si i heqs.
    rewrite !eandsE_cat => -[hei11] [hei21] hsc; t_xrbindP.
    move=> v1 hei12 v2 hei22.
    have [v1' he1 ?]:= hrec1 _ hei1 _ _ _ heqs hei11 hei12.
    have [v2' he2 ?]:= hrec2 _ hei2 _ _ _ heqs hei21 hei22.
    rewrite he1 he2 /=; subst v1 v2.
    apply: (wi2i_op2P heqs) hsc => //.
    + by have /(sem_pexpr_tovI he1) := sem_pexpr_type_of he1.
    by have /(sem_pexpr_tovI he2) := sem_pexpr_type_of he2.

  + move=> o es hes ei hall esi hesi <- /= v si s heqs hsc; t_xrbindP.
    move=> vs hsem hvs.
    have [vs'] := hes _ hesi _ _ _ heqs hsc hsem; rewrite /sem_pexprs => {}hsem.
    have hsz := size_mapM hsem; rewrite hsem => hvs' /=.
    have : map2 (λ (e : pexpr) (v0 : value), val_to_int (sign_of_expr m e) v0) es vs' = vs'.
    + move=> {hvs' hsem hesi hes}; elim: es vs' hall hsz => [ | e es hrec] [ | v' vs'] //=.
      by move=> /andP[]/eqP -> /hrec h [] /h ->; rewrite val_to_int_None.
    move=> <-; rewrite -hvs' hvs /=; eexists; first reflexivity.
    by rewrite /sign_of_expr /= sign_of_to_etype_None val_to_int_None.

  + move=> t e he e1 he1 e2 he2 ei_ /andP[] hs1 hs2.
    move=> ei /he{}he ei1 /he1{}he1 ei2 /he2{}he2 <- vr si s heqs /=.
    rewrite !eandsE_cat => -[hei1] [hei11 hei21]; t_xrbindP.
    move=> b v hv hb v1' v1 hv1 htr1 v2' v2 hv2 htr2 <-.
    have [v' {}he ?] := he _ _ _ heqs hei1 hv.
    have [v1_ {}he1 ?] := he1 _ _ _ heqs hei11 hv1.
    have [v2_ {}he2 ?] := he2 _ _ _ heqs hei21 hv2.
    subst v v1 v2; rewrite he he1 he2 /=.
    have [w1 -> ?] := esubtype_truncate_val hs1 htr1 (sem_pexpr_type_of he1).
    have hse1 := esubtype_sign_of hs1.
    have hse2 := esubtype_sign_of hs2.
    rewrite /sign_of_expr hse1 -hse2 in hs2, htr2.
    have [w2 -> ? /=] := esubtype_truncate_val hs2 htr2 (sem_pexpr_type_of he2).
    have ? : v' = Vbool b.
    + have := to_boolI hb; case: (v') => //=.
      + by move=> >; case sign_of_expr.
      by move=> [] // >; case sign_of_expr.
    subst v' => /=; eexists; first reflexivity.
    by rewrite /sign_of_expr /=; subst v1' v2'; rewrite {1}hse1 hse2; case: (b).

  + move=> idx hidx op x body hbody start hstart len hlen ei /and5P [hsub1 hsub2 hsub3 /eqP heqx /andP[] /eqP heq1 /eqP heq2] hnwio.
    move=> idxi /hidx{}hidx bodyi/hbody{}hbody starti/hstart{}hstart leni/hlen{}hlen xi hxi.
    move=> <- v si s heqs; rewrite !eandsE_cat => -[] hscid [] hscstart [] hsclen hscbody /=; t_xrbindP.
    move=> stz vstz hstz hto1 lz vlz hlz hto2 vi vi' hvi' htr hfold.
    have [vstz' hstz' ?] := hstart _ _ _ heqs hscstart hstz.
    have [vlz' hlz' ?] := hlen _ _ _ heqs hsclen hlz.
    have [vi1 hvi1 ?] := hidx _ _ _ heqs hscid hvi'.
    subst vstz vlz vi'; rewrite hstz' hlz' hvi1 /=.
    move: hto1 hto2; rewrite /sign_of_expr heq1 heq2 /=.
    rewrite !val_to_int_None => /to_intI ? /to_intI ?; subst vstz' vlz' => /=.
    have [heq11 heq12 heq_2] := wi2i_type_of_op2 op.
    rewrite heq_2 /sign_of_expr -(esubtype_sign_of hsub1) in htr.
    have := esubtype_truncate_val _ htr.
    rewrite {1}(esubtype_sign_of hsub1) to_etype_to_stype.
    move=> /(_ hsub1 (sem_pexpr_type_of hvi1)).
    have [heq11_ heq12_ heq_2']:= e_type_of_op2' op.
    rewrite -heq_2' (esubtype_sign_of hsub1) => -[w1 -> ?] /=; subst vi.
    have [hin ? hmx] : [/\ in_FV_var FV x, x = xi & m x = None].
    + move: (hwf_m x) hxi; rewrite /wi2i_vari /wi2i_var; t_xrbindP.
      by rewrite heqx; case: (m x) => [ [??][] | _ ? <-] //; split => //; case: (x).
    subst xi.
    have [ht1 ht2 hto hop_]:
         [/\ sign_of_etype (etype_of_op2 op).1.1 = None, sign_of_etype (etype_of_op2 op).1.2 = None
           , sign_of_etype (etype_of_op2 op).2 = None & wi2i_op2 op = op].
    + by move: hnwio; rewrite /wi2i_op2; case: is_wi2 (is_wi2P op) => // -[].
    rewrite hto val_to_int_None hop_ in hfold.
    move=> {htr}; elim: (ziota _ _) w1 (sc_allE heqx hstz hlz hscbody) hfold => [ | j js hrec] w1 /=.
    + by move=> _ [<-]; exists w1 => //; rewrite hto val_to_int_None.
    move=> /List.Forall_cons_iff []; t_xrbindP => si1 hw hsc hall.
    rewrite hw => ? _ [<-] vbod hbod hop hfold.
    have [s1 -> heqs1 /=]:= wi2i_lvarP_None heqs hin hmx hw.
    have [vbod' hvbod' ?]:= hbody _ _ _ heqs1 hsc hbod; subst vbod.
    rewrite hvbod' /=.
    move: hop; rewrite /sign_of_expr (esubtype_sign_of hsub3) ht2 !val_to_int_None => -> /=.
    apply (hrec _ hall hfold).
  + move=> x _ xi hx <- /= vi si s heqs _ [<-]; rewrite /sign_of_expr /=.
    move: hx; rewrite /wi2i_vari; t_xrbindP => hin <-.
    case: heqs => _ _ /(_ _ hin) ->.
    eexists; first reflexivity.
    by rewrite is_defined_val_to_int val_to_int_None.
  move=> e1 e2 he1 he2 sce_ /andP[/eqP hte1 /eqP hte2] sce1 hsce1 sce2 hsce2 <- v si s heqs /=.
  move=> /eandsE_cat [hsce11 hsce21]; t_xrbindP.
  move=> w vi1 hsce12 hto1 i vi2 hsce22 hto2 <-.
  have [v1]:= he1 _ hsce1 _ _ _ heqs hsce11 hsce12.
  have [v2]:= he2 _ hsce2 _ _ _ heqs hsce21 hsce22.
  rewrite /sign_of_expr hte1 hte2 !val_to_int_None => -> /= ? -> /= ?; subst vi1 vi2.
  rewrite hto1 hto2 /=.
  eexists; first reflexivity; rewrite val_to_int_None.
  by case: heqs => _ <-.
Qed.

Lemma wi2i_eP e : P e.
Proof. by case wi2i_eP_. Qed.

Lemma wi2i_esP es : Q es.
Proof. by case wi2i_eP_. Qed.

Lemma wi2i_condP b e ei :
  wi2i_e m FV e = ok ei ->
  forall si s, eqst tt si s ->
    sem_cond gd (eands ei.1) si = ok true ->
    sem_cond gd ei.2 si = ok b ->
    sem_cond gd e s = ok b.
Proof.
  move=> hei si s heqs hei1; rewrite /sem_cond; t_xrbindP => v hei2 /to_boolI ?; subst v.
  have [v' -> ]:= wi2i_eP hei heqs hei1 hei2.
  rewrite /val_to_int; case: v' => //.
  + by move=> ? <-.
  + by case: sign_of_expr.
  by case => //; case: sign_of_expr.
Qed.

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

Lemma wi2i_lvarP x xi ety si si' s v :
  eqst tt si s ->
  wi2i_lvar m FV (to_etype (sign_of_etype ety) (type_of_val v)) x = ok xi ->
  write_var true xi (val_to_int (sign_of_etype (to_etype (sign_of_etype ety) (type_of_val v))) v) si = ok si' ->
  exists2 s' : estate,
      write_var true x v s = ok s' &
      eqst tt si' s'.
Proof.
  rewrite /wi2i_lvar /wi2i_vari; t_xrbindP => heqs hsub hin ?; subst xi.
  move: hsub; rewrite /wi2i_vari /wi2i_var /etype_of_var /sign_of_var.
  case heqm: m (hwf_m x) => [[sg xi]| ] /=.
  + move=> [/is_swordP [sw hxty] htxi hdiff] hsub.
    have := (esubtype_sign_of hsub); rewrite hxty /=.
    move=> hsig; rewrite hsig.
    move=> /write_varP [-> hdb htr].
    have [heq [ws [? | [w ?]]]] := sign_to_etype_type_of hsig; subst.
    + by move: hdb; rewrite /DB.
    move: hsub; rewrite /esubtype hxty heq => /andP[_ /eqP?]; subst sw.
    rewrite /val_to_int /=.
    exists (with_vm s (evm s).[x <- Vword w]).
    + by apply/write_varP; split => //=; rewrite hxty.
    case: heqs => ?? hvm.
    split => //= z hz.
    rewrite (Vm.setP _ x); case: eqP => heqx.
    + subst z; rewrite /wi2i_var heqm Vm.setP_eq.
      by rewrite hxty /= cmp_le_refl htxi /sign_of_var heqm.
    rewrite Vm.setP_neq; first by apply hvm.
    by apply/eqP; have := hdiff _ heqx hz; rewrite /wi2i_var; case: m => [[]|].
  move=> _ hsub.
  have := (esubtype_sign_of hsub); rewrite sign_of_to_etype_None => ->.
  by rewrite val_to_int_None; apply: wi2i_lvarP_None.
Qed.

Lemma wi2i_lvP ety lv lvi si si' s v:
  eqst tt si s ->
  let ety := to_etype (sign_of_etype ety) (type_of_val v) in
  wi2i_lv m FV ety lv = ok lvi ->
  sem_cond gd (eands lvi.1) si = ok true ->
  write_lval true gd lvi.2 (val_to_int (sign_of_etype ety) v) si = ok si' ->
  exists2 s', write_lval true gd lv v s = ok s' & eqst tt si' s'.
Proof.
  move=> heqs; case: lv => /=.
  + move=> i ty; t_xrbindP.
    move=> hsub <- /= hsc /write_noneP [-> htr hdb]; exists s => //=.
    rewrite /write_none.
    case heq: sign_of_etype htr hdb => [sg | ] /=.
    + have [_ [ws [ ? | [w ?]]]] := sign_to_etype_type_of heq; subst v.
      + by rewrite /DB.
      rewrite /= => _ _.
      rewrite heq in hsub.
      move: heq hsub => /=; case: sign_of_etype => // _ [->].
      by case: ty => //= ? /andP [] _ /eqP ->; rewrite cmp_le_refl.
    by rewrite val_to_int_None => -> ->.
  + by move=> x; t_xrbindP => xi /= + <- /= _; apply: wi2i_lvarP.
  + t_xrbindP => a ws vi e /andP [/eqP hse /eqP hsty].
    move=> ei hei <- /= hsc; t_xrbindP.
    move=> we ve hseme htoe ? htov m' hw <-.
    have [ve' -> /= ? ]:= wi2i_eP hei heqs hsc hseme; subst ve.
    move: htoe htov; rewrite hse hsty !val_to_int_None => -> /= -> /=.
    case heqs => ? hmem ?.
    by exists (with_mem s m') => //; rewrite -hmem hw.
  + t_xrbindP => a aa ws x e /and3P[hinx /eqP hse /eqP hsety].
    move=> ei hei <- /= hsc; apply: on_arr_varP; t_xrbindP.
    move=> len t htx hget i vi hseme /to_intI ?; rewrite hsety val_to_int_None => ? -> /=; subst vi.
    move=> t' hset hw.
    have := wi2i_varP heqs hinx.
    have hmx : m x = None.
    + by have := hwf_m x; case: m => // -[sg ?] []; rewrite htx.
    rewrite /sign_of_var /wi2i_var hmx => /(_ _ hget) [vt] -> /=.
    rewrite val_to_int_None => <- /=.
    have [i'] := wi2i_eP hei heqs hsc hseme.
    rewrite hse val_to_int_None => -> <- /=; rewrite hset /=.
    by apply (wi2i_lvarP_None heqs hinx hmx hw).

  t_xrbindP => a aa ws x e /and3P[hinx /eqP hse /eqP hsty].
  move=> ei hei <- /= hsc; apply: on_arr_varP; t_xrbindP.
  move=> len t htx hget i vi hseme /to_intI ?; subst vi.
  rewrite hsty val_to_int_None => ? hto ? hsub hw.
  have := wi2i_varP heqs hinx.
  have hmx : m x = None.
  + by have := hwf_m x; case: m => // -[sg ?] []; rewrite htx.
  rewrite /sign_of_var /wi2i_var hmx => /(_ _ hget) [?] /=.
  rewrite val_to_int_None => -> /= <-.
  have [i'] := wi2i_eP hei heqs hsc hseme.
  rewrite hse val_to_int_None => -> <- /=.
  rewrite hto /= hsub.
  by apply (wi2i_lvarP_None heqs hinx hmx hw).
Qed.

Lemma wi2i_lvsP msg ety lvs lvis si0 si si' s vs okmem:
  wi2i_lvs m FV msg okmem ety lvs = ok lvis ->
  sem_cond gd (eands lvis.1) si0 = ok true ->
  (evm si0 = evm si) ->
  (okmem -> emem si0 = emem si) ->
  eqst tt si s ->
  write_lvals true gd si lvis.2 (map2 (fun ety v => val_to_int (sign_of_etype ety) v) ety vs) = ok si' ->
  all2 (fun ety v => ety == (to_etype (sign_of_etype ety) (type_of_val v))) ety vs ->
  exists2 s',
    write_lvals true gd s lvs vs = ok s' &
    eqst tt si' s'.
Proof.
  rewrite /wi2i_lvs; t_xrbindP.
  move=> lvsi' hlv hcheck <- /= {lvis} hcond hvm.
  have : evm si0 =[\Sv.empty] evm si by rewrite hvm.
  move=> {hvm}.
  elim: ety lvs vs lvsi' okmem Sv.empty si s hlv hcheck hcond =>
    [|ety etys hrec] [|lv lvs] //= [|v vs] //= ? okmem W si s; t_xrbindP.
  + by move=> <- _ _ _ _ ? /= [<-] _; exists s.
  move=> lvi hlvi lvis hlvis <- /= /and3P [hmemok hdisj hcheck]; t_xrbindP.
  rewrite eandsE_cat => -[hsc hscs] hvm hokm heqs si1 hw hws /andP[ /eqP heq hall] /=.
  rewrite heq in hlvi, hw.
  rewrite (check_scP _ s hmemok hdisj hvm hokm) in hsc.
  have [s1 -> /= heqs2 ]:= wi2i_lvP heqs hlvi hsc hw.
  apply: (hrec _ _ _ _ _ _ _ hlvis hcheck) heqs2 hws hall => //.
  + rewrite vrv_recE.
    apply (eq_exT (vm2:= evm si)).
    + by apply: eq_exI hvm; SvD.fsetdec.
    by apply: eq_exI (vrvP hw); SvD.fsetdec.
  by move=> /andP [/hokm -> hlv]; apply: lv_write_memP hw.
Qed.

Lemma wi2i_esP_none es sce scs :
  all (λ e : pexpr, sign_of_expr m e == None) es →
  wi2i_es (wi2i_e m FV) es = ok sce →
  wrequiv (λ si s : estate, eqst tt si s ∧ sem_cond gd (eands (sce.1 ++ scs)) si = ok true)
    ((sem_pexprs true gd)^~ sce.2) ((sem_pexprs true gd)^~ es) eq.
Proof.
  move=> hnone hsce si s vsi [heqs /eandsE_cat[hsce1 hscx1]] hsce2.
  have [vs' hes ->] := wi2i_esP hsce heqs hsce1 hsce2.
  exists vs' => //.
  have {hes hsce} h := size_mapM hes.
  elim: es vs' h hnone => [| e es hes] [| ve ves] //= [] hsz /andP [/eqP -> /hes ->] //.
  by rewrite val_to_int_None.
Qed.

Lemma wi2i_lvsP_none msg vs tys xs scx scs :
  map type_of_val vs = tys →
  wi2i_lvs m FV msg true [seq to_etype None i | i <- tys] xs = ok scx →
  wrequiv (λ si s : estate, eqst tt si s ∧ sem_cond gd (eands (scs ++ scx.1)) si = ok true)
    (λ s1 : estate, write_lvals true gd s1 scx.2 vs) (λ s2 : estate, write_lvals true gd s2 xs vs)
    (eqst tt).
Proof.
  move=> heq hscx si s si' [heqs /eandsE_cat [hsce1 hscx1]] hw.
  apply: (wi2i_lvsP hscx hscx1 _ _ heqs) => //.
  + have -> //: map2 (λ ety v, val_to_int (sign_of_etype ety) v) [seq to_etype None i | i <- tys] vs = vs.
    have : size vs = size tys.
    + by rewrite -heq size_map.
    elim : (vs) (tys) => [ | ?? hrec] [|??] //= [/hrec ->].
    by rewrite sign_of_to_etype_None val_to_int_None.
  by rewrite -heq; elim : (vs) => [ | ?? hrec] //=; rewrite hrec sign_of_to_etype_None eqxx.
Qed.

Context (p_funcsi : ufun_decls)
        (sigs : funname → option (seq (extended_type positive) * seq (extended_type positive)))
        (hsig : forall fn fd, get_fundef (p_funcs p) fn = Some fd ->
                  sigs fn = Some
                    (map2 (fun (x:var_i) ty => to_etype (sign_of_var m x) ty) fd.(f_params) fd.(f_tyin),
                     map2 (fun (x:var_i) ty => to_etype (sign_of_var m x) ty) fd.(f_res) fd.(f_tyout)))
        (hp' : forall fn fdi, get_fundef p_funcsi fn = Some fdi ->
               exists2 fd, wi2i_fun m FV sigs fn fd = ok fdi & get_fundef (p_funcs p) fn = Some fd).

Let pi : uprog := {| p_funcs := p_funcsi; p_globs := gd; p_extra := p_extra p |}.

Definition vs_pre fsig (vargsi vargs: values) :=
  [/\ all2 (fun ety v => esubtype ety (to_etype (sign_of_etype ety) (type_of_val v))) fsig vargs
    & vargsi = map2 (fun ety v => val_to_int (sign_of_etype ety) v) fsig vargs].

Definition vs_post fsig (vargsi vargs: values) :=
  [/\ all2 (fun ety v => ety == (to_etype (sign_of_etype ety) (type_of_val v))) fsig vargs
    & vargsi = map2 (fun ety v => val_to_int (sign_of_etype ety) v) fsig vargs].

Definition wi2i_spec :=
  {| rpreF_ := λ fn1 fn2 fs1 fs2,
       fn1 = fn2 /\ exists2 fsig, sigs fn1 = Some fsig & fs_rel (vs_pre fsig.1) fs1 fs2
   ; rpostF_ := λ fn1 fn2 fs1 fs2 fr1 fr2,
       exists2 fsig, sigs fn1 = Some fsig &
               fs_rel (vs_post fsig.2) fr1 fr2
  |}.

Let Pi_r ir :=
  forall ii sci, wi2i_ir m FV sigs ir = ok sci ->
  wequiv_rec pi p ev ev wi2i_spec
    (fun si s => eqst tt si s /\ sem_cond (p_globs pi) (eands sci.1) si = ok true)
    [::MkI ii sci.2] [::MkI ii ir] (eqst tt).

Let Pi i :=
  forall ci, wi2i_i m FV sigs i = ok ci ->
  wequiv_rec pi p ev ev wi2i_spec (eqst tt) ci [::i] (eqst tt).

Let Pc c :=
  forall ci, wi2i_c (wi2i_i m FV sigs) c = ok ci ->
  wequiv_rec pi p ev ev wi2i_spec (eqst tt) ci c (eqst tt).

Lemma esubtype_truncate_vals xs tys vs vis' :
  let etys := map2 (λ (x:var_i) ty, to_etype (sign_of_var m x) ty) xs tys in
  size xs = size tys →
  all2 (λ ety v, esubtype ety (to_etype (sign_of_etype ety) (type_of_val v))) etys vs →
  mapM2 ErrType truncate_val
      (map (λ ety, wi2i_type (sign_of_etype ety) (to_stype ety)) etys)
      (map2 (λ ety v, val_to_int (sign_of_etype ety) v) etys vs) = ok vis' →
  exists2 vs',
    mapM2 ErrType truncate_val tys vs = ok vs' &
    vis' = map2 (λ ety v, val_to_int (sign_of_etype ety) v) etys vs' /\
    tys = map type_of_val vs'.
Proof.
  rewrite /=.
  elim: tys vs xs vis' => [|ty tys hrec] [|v vs] [| x xs] //= .
  + by move=> ? _ _ [<-]; eauto.
  move=> vis'_ [hsize] /andP[] hsub hsubs; t_xrbindP => vi' htr vis' htrs <-.
  have [hsign htoe1 hto2]:
    [/\ sign_of_etype (to_etype (sign_of_var m x) ty) =
        sign_of_etype (to_etype (sign_of_var m x) (type_of_val v))
      , to_etype (sign_of_etype (to_etype (sign_of_var m x) (type_of_val v))) ty = to_etype (sign_of_var m x) ty
      & to_etype (sign_of_etype (to_etype (sign_of_var m x) ty)) (type_of_val v) =
          to_etype (sign_of_var m x) (type_of_val v)].
  + case: (sign_of_var m x) hsub => [sg | ]; last first.
    + by rewrite !sign_of_to_etype_None.
    by case: (ty) (type_of_val v) => [||len1|ws1] [||len2|ws2].
  have := esubtype_truncate_val (et := to_etype (sign_of_var m x) (type_of_val v)) (t:=ty) (v1:= v) (v1':= vi').
  rewrite !to_stypeK in htr |- *.
  rewrite htoe1 -hsign; rewrite hto2 in hsub.
  move=> /(_ hsub htr erefl) [v' h1 ->] /=; rewrite h1.
  have <- := truncate_val_has_type h1.
  have [vs' -> [-> /= ->] ] := hrec _ _ _ hsize hsubs htrs.
  by eexists; first reflexivity.
Qed.

Lemma wi2i_write_vars msg xs ixs ixsi vs :
  let tys := map type_of_val vs in
  let etys := map2 (λ (x : var_i) ty, to_etype (sign_of_var m x) ty) xs tys in
  let vparitr := map2 (λ ety v, val_to_int (sign_of_etype ety) v) etys vs in
  size xs = size tys →
  mapM2 (E.ierror_s msg) (wi2i_lvar m FV) etys ixs = ok ixsi →
  forall si s si',
  eqst tt si s →
  write_vars true ixsi vparitr si = ok si' →
  exists2 s', write_vars true ixs vs s = ok s' & eqst tt si' s'.
Proof.
  rewrite /=.
  elim: vs xs ixs ixsi => [|v vs hrec] //= [| x xs] //= [|ix ixs] ixsi_ //=.
  + by move=> _ [<-] si s si' heqs [<-]; exists s.
  move=> [hsize]; t_xrbindP.
  move=> ixi hixi ixis hixis <- si s si' heqs /=; t_xrbindP.
  move=> si1 hw hws.
  have heq : forall ty,
     to_etype (sign_of_etype (to_etype (sign_of_var m x) ty)) ty =
     to_etype (sign_of_var m x) ty.
  + by case => //= ws; case: sign_of_var.
  rewrite -heq in hixi, hw.
  have [s1 -> /= heqs1]:= wi2i_lvarP heqs hixi hw.
  have [s' -> ?] := hrec _ _ _ hsize hixis _ _ _ heqs1 hws.
  by exists s'.
Qed.

Lemma eqst_init scs1 scs2 mem1 mem2 :
  scs1 = scs2 -> mem1 = mem2 ->
  eqst tt {| escs := scs1; emem := mem1; evm := Vm.init |}
          {| escs := scs2; emem := mem2; evm := Vm.init |}.
Proof.
  move=> -> ->; split => //= z hin.
  rewrite !Vm.initP /wi2i_var /sign_of_var.
  case: m (hwf_m z) => [[sg zi] | ] //=; last by rewrite val_to_int_None.
  by move=> [] /is_swordP [ws ->] -> _ /=; apply undef_x_vundef.
Qed.

Lemma wi2i_a_andP a_s ai_s si s' t :
  eqst tt si s' →
  mapM (wi2i_a_and m FV) a_s = ok ai_s →
  mapM (sem_assert gd si) ai_s = ok t →
  mapM (sem_assert gd s') a_s >> ok tt = ok tt.
Proof.
  move=> heqs; elim: a_s ai_s t => /= [|a a_s hrec] ai_s_ t.
  + by move=> [<-].
  t_xrbindP => ai hai ai_s hai_s <- /=; t_xrbindP => hsemai ? /(hrec _ _ hai_s); t_xrbindP.
  move=> ? -> _ _ /=.
  move: hai hsemai; rewrite /sem_assert /wi2i_a_and; t_xrbindP.
  move=> sca he <- _ [] //=.
  rewrite -cats1 eandsE_cat eandsE_1 => -[] hsc ha2 _ _.
  by rewrite (wi2i_condP he heqs hsc ha2).
Qed.

Lemma wi2i_sem_pre fn fsig fsi fs:
  sigs fn = Some fsig →
  fs_rel (vs_pre fsig.1) fsi fs →
  sem_pre pi fn fsi = ok tt → sem_pre p fn fs = ok tt.
Proof.
  move=> hfsig [hscs hmem [hsub hval]]; rewrite /sem_pre /=.
  case hfdi : get_fundef => [fdi | //].
  have [[fi fc ftyi fpar fbod ftyo fres fex] + hfd] := hp' hfdi.
  have /= := hsig hfd.
  rewrite hfsig => -[?]; subst fsig.
  rewrite hfd /wi2i_fun /= /get_sig hfsig /= => /add_funnameP {hfd}; t_xrbindP.
  move=> fc' hfc' /andP [/eqP hsizei /eqP hsizeo] _ _ _ _ _ _ <- /=.
  case: fc hfc' => [fc | //]; t_xrbindP => fci + <-.
  rewrite /wi2i_ci; t_xrbindP => fpre' hfpre fpre_range hfpre_range. 
  move=> fpost' hfpost fpost_range hfpost_range fipar hfipar hires hfires <-.
  move=> vparitr hvpari si hw ? hassert _; rewrite hval in hvpari.
  have [vs' -> [? htys]] := esubtype_truncate_vals hsizei hsub hvpari => /=; subst vparitr ftyi.
  have [s' -> heqs /=]:= wi2i_write_vars hsizei hfipar (eqst_init hscs hmem) hw.
  move: hassert; rewrite /= mapM_cat; t_xrbindP => ? hassert _ _ _.
  apply: wi2i_a_andP heqs hfpre hassert.
Qed.

(* FIXME: MOVE THIS to utils*)
Lemma all2I (A B : Type) (f1 f2 : A -> B -> bool) l1 l2:
  (forall a b, f1 a b -> f2 a b) ->
  all2 f1 l1 l2 -> all2 f2 l1 l2.
Proof. by move=> hf; elim: l1 l2 => [|a l1 hrec] [|b l2] //= /andP[/hf -> /hrec]. Qed.

Lemma wi2i_sem_post fn fsig vsi vs fri fr:
  sigs fn = Some fsig →
  vs_pre fsig.1 vsi vs →
  fs_rel (vs_post fsig.2) fri fr →
  sem_post pi fn vsi fri = ok tt → sem_post p fn vs fr = ok tt.
Proof.
  move=> hfsig [hsub1 hval1] [hscs hmem [heq2 hval2]]; rewrite /sem_post /=.
  case hfdi : get_fundef => [fdi | //].
  have [[fi fc ftyi fpar fbod ftyo fres fex] + hfd] := hp' hfdi.
  have /= := hsig hfd.
  rewrite hfsig => -[?]; subst fsig.
  rewrite hfd /wi2i_fun /= /get_sig hfsig /= => /add_funnameP {hfd}; t_xrbindP.
  move=> fc' hfc' /andP [/eqP hsizei /eqP hsizeo] _ _ _ _ _ _ <- /=.
  case: fc hfc' => [fc | //]; t_xrbindP => fci + <-.
  rewrite /wi2i_ci; t_xrbindP => fpre' hfpre fpre_range hfpre_range fpost' hfpost fpost_range hfpost_range fipar hfipar hires hfires <-.
  move=> vparitr hvpari si_ hw1 si hw2 ? hassert _.
  rewrite hval1 in hvpari.
  have [vs' -> [? htys]] := esubtype_truncate_vals hsizei hsub1 hvpari => /=; subst vparitr ftyi.
  have h : forall ety v, ety == (to_etype (sign_of_etype ety) (type_of_val v)) ->
                         esubtype ety (to_etype (sign_of_etype ety) (type_of_val v)).
  + by move=> > /eqP {1}->; apply esubtype_refl.
  have hsub2 := all2I h heq2.
  have [s' -> heqs' /=]:= wi2i_write_vars hsizei hfipar (eqst_init hscs hmem) hw1.
  have [hftyo hsize] : ftyo = map type_of_val (fvals fr) /\ size fres = size [seq type_of_val i | i <- fvals fr].
  + elim : (fres) (ftyo) (fvals fr) hsizeo heq2 => [|x xs hrec] [|ty tys] //= [|vr vrs] //=.
    move=> [/hrec{}hrec] /andP []/eqP h1 /hrec [] -> ->.
    by rewrite -(to_stypeK (sign_of_var m x) ty) h1 to_stypeK.
  rewrite /= hftyo in hfires.
  rewrite hval2 /= hftyo in hw2.
  have [s -> heqs /=] := wi2i_write_vars hsize hfires heqs' hw2.
  move: hassert; rewrite /= mapM_cat; t_xrbindP => ? hassert _ _ _.
  apply: wi2i_a_andP heqs hfpost hassert.
Qed.

Lemma wi2i_get_var_is msg xs tys xis vis vis' si s :
  let etys := map2 (λ (x : var_i) ty, to_etype (sign_of_var m x) ty) xs tys in
  let f_tyout := map (λ ety, wi2i_type (sign_of_etype ety) (to_stype ety)) etys in
  eqst tt si s →
  size xs = size tys →
  mapM2 msg (fun ety x => assert (esubtype ety (etype_of_var m x)) (E.ierror_lv x) >> wi2i_vari m FV x)
    etys xs = ok xis →
  get_var_is (~~ direct_call) (evm si) xis = ok vis →
  mapM2 ErrType dc_truncate_val f_tyout vis = ok vis' →
  exists vs vs',
    [/\ get_var_is (~~ direct_call) (evm s) xs = ok vs
      , mapM2 ErrType dc_truncate_val tys vs = ok vs'
      , vis' =  map2 (λ ety v, val_to_int (sign_of_etype ety) v) etys vs'
      & all2 (λ ety v, ety == (to_etype (sign_of_etype ety) (type_of_val v))) etys vs'].
Proof.
  move=> /= heqs; rewrite /get_var_is /=.
  elim: xs tys xis vis vis' => [|x xs hrec] [| ty tys] xis_ vis_ vis'_ //=.
  + by move=> _ [<-] [<-] [<-]; exists [::], [::].
  move=> [hsize]; t_xrbindP => xi hsub hxi xis hxis <- /=.
  t_xrbindP => vi hvi vis hvis <-; t_xrbindP.
  move=> vi' htr vis' htrs <-.
  have [v hv ? /=]:= wi2i_variP heqs hxi hvi; rewrite hv; subst vi.
  have /(_ ty vi') := esubtype_truncate_val _ _ (get_var_type_of hv).
  rewrite to_stypeK -(esubtype_sign_of hsub) sign_of_etype_var in htr.
  rewrite sign_of_etype_var => /(_ hsub htr) [v' htr' ?]; subst vi'.
  have [vs [vs' [-> htrs' ? hsubs /=]]] := hrec _ _ _ _ hsize hxis hvis htrs; subst vis'.
  exists (v :: vs), (v' :: vs'); split => //.
  + by rewrite /dc_truncate_val htr' /= htrs'.
  + by rewrite -(esubtype_sign_of hsub) sign_of_etype_var.
  by rewrite (truncate_val_has_type htr') -(esubtype_sign_of hsub) sign_of_etype_var eqxx.
Qed.

(* FIXME: TODO move this in psem *)
Lemma sem_cond_with_scs gd e s scs:
  sem_cond gd e s = sem_cond gd e (with_scs s scs).
Proof. by rewrite /sem_cond -sem_pexpr_with_scs. Qed.

(* FIXME: TODO move this in psem *)
Lemma eandP_inv gd e1 e2 s b : 
  sem_cond gd (eand e1 e2) s = ok b -> 
  (Let b1 := sem_cond gd e1 s in
   Let b2 := sem_cond gd e2 s in
   ok (b1 && b2)) = ok b. 
Proof.
  rewrite /eand /sem_cond /= /sem_sop2 /=; t_xrbindP.
  by move=> > -> /= > -> /= > -> > -> <- [<-].
Qed.

Lemma eandP gd e1 e2 s b1 b2 : 
  sem_cond gd e1 s = ok b1 ->
  sem_cond gd e2 s = ok b2 -> 
  sem_cond gd (eand e1 e2) s = ok (b1 && b2). 
Proof.
  rewrite /eand /sem_cond /= /sem_sop2 /=; t_xrbindP.
  by move=> > -> /= > -> > -> /= ->.
Qed.
  
Lemma eands_consP_inv gd e1 e2 s b : 
  sem_cond gd (eands (e1 :: e2)) s = ok b ->
  (Let b1 := sem_cond gd e1 s in
   Let b2 := sem_cond gd (eands e2) s in
   ok (b1 && b2)) = ok b.
Proof.
  case: e2.
  + by move=> ->; rewrite eandsE_nil /= andbT.
  by move=> e2 es2 /eandP_inv.
Qed.

Lemma eands_consP gd e1 e2 s b1 b2 : 
  sem_cond gd e1 s = ok b1 ->
  sem_cond gd (eands e2) s = ok b2 ->
  sem_cond gd (eands (e1 :: e2)) s = ok (b1 && b2). 
Proof.
  case: e2.
  + by rewrite eandsE_nil eandsE_1 => -> [<-]; rewrite andbT.
  move=> e2 es2 /=; apply eandP.
Qed.

Lemma eands_catP_inv gd e1 e2 s b : 
  sem_cond gd (eands (e1 ++ e2)) s = ok b -> 
  (Let b1 := sem_cond gd (eands e1) s in
   Let b2 := sem_cond gd (eands e2) s in
   ok (b1 && b2)) = ok b.
Proof.
  elim: e1 b => [| e1 es1 hrec] b_.
  + by rewrite /= => ->.
  rewrite cat_cons => /eands_consP_inv.
  t_xrbindP => b1 hb1 ? /hrec; t_xrbindP => bs1 hbs1 bs2 hbs2 <- <-.
  by rewrite (eands_consP hb1 hbs1) /= hbs2 /= andbA.  
Qed.

Lemma eands_catP gd e1 e2 s b1 b2 : 
  sem_cond gd (eands e1) s = ok b1 -> 
  sem_cond gd (eands e2) s = ok b2 -> 
  sem_cond gd (eands (e1 ++ e2)) s = ok (b1 && b2).
Proof.
  elim: e1 b1 => [|e1 es1 hrec] b1.
  + by rewrite eandsE_nil /= => -[<-] ->.
  rewrite cat_cons => /eands_consP_inv.
  t_xrbindP => ? he1 ? hes1 <- he2; rewrite -andbA.
  by apply eands_consP => //; apply hrec.
Qed.
(* END FIXME *)

Lemma wi2i_callP_aux fn : wiequiv_f pi p ev ev (rpreF (eS:= wi2i_spec)) fn fn (rpostF (eS:=wi2i_spec)).
Proof.
  apply wequiv_fun_ind_wa => hrec {fn}.
  move=> fn _ fsi fs [<- [fsig hfsig hrel]] fdi hgeti.
  have [fd hfdi hget] := hp' hgeti.
  exists fd => // {hgeti}.
  move=> hpre; split.
  + by apply: wi2i_sem_pre hfsig hrel hpre.
  move=> si hinit.
  case: hrel => hscs hmem [hsub1 hval1].
  have /= {hget} := hsig hget.
  rewrite hfsig => -[?]; subst fsig.
  case: fd hfsig hval1 hsub1 hfdi => fi fc ftyi fpar fbod ftyo fres fex;
  rewrite /= /wi2i_fun /get_sig => hfsig.
  rewrite hfsig => /= hval1 hsub1 /add_funnameP; t_xrbindP.
  move=> fc' hfc' /andP [/eqP hsizei /eqP hsizeo] ipar hipar ci hci ires hires ?; subst fdi.
  set fd := {| f_contra := fc |}. set fdi:= {|f_contra := fc'|} => /=.
  move: hinit; rewrite /initialize_funcall /=; t_xrbindP => vis htr hw.
  rewrite hval1 in htr.
  have [vs' -> [? htys]] := esubtype_truncate_vals hsizei hsub1 htr; subst vis ftyi.
  have [s /= -> heqs /=] := wi2i_write_vars hsizei hipar (eqst_init hscs hmem) hw.
  exists s => //; exists (eqst tt), (eqst tt); split => //; last first.
  + move=> fr1 fr2 [_ [<-]] /=.
    rewrite hval1 => hfs.
    by apply (wi2i_sem_post hfsig).
  + move=> si1 s1 fr1 heqs1; rewrite /finalize_funcall.
    t_xrbindP => vresi hvresi vresi' {}htr ?; subst fr1.
    have [vs1 [vs1' [-> /= -> /= ??]]]:= wi2i_get_var_is heqs1 hsizeo hires hvresi htr; subst vresi'.
    eexists; first reflexivity.
    eexists; first reflexivity.
    by case: heqs1 => <- <- _.
  clear s heqs fd fdi hires hipar hsizeo hfsig hval1 hsub1 hfc' hsizei htr hw vs' fc hmem hscs ires
        ipar fc' fex fres ftyo fpar fi si hpre fsi fs fn.
  apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => // {ci fbod hci}; subst Pi_r Pi Pc => /=.
  + move=> i ii hi ci_; t_xrbindP => sci /add_iinfoP /(hi ii) {}hi <-.
    rewrite -(cat0s [:: MkI _ _]) -cats1.
    apply wequiv_cat with (λ si s : estate, eqst tt si s ∧ sem_cond (p_globs pi) (eands sci.1) si = ok true).
    + by apply safe_assertP.
    by apply hi.
  + by move=> ci [<-]; apply wequiv_nil.
  + move=> i c hi hc ci_; rewrite /wi2i_c /=; t_xrbindP.
    move=> _ ci /hi{}hi cci hcci <- <-.
    rewrite /= -cat1s; apply wequiv_cat with (eqst tt) => //.
    by apply hc; rewrite /wi2i_c hcci.
  + t_xrbindP => x tg ty e ii sci hsub scx hscx sce hsce <- /=.
    apply wequiv_assgn_core.
    move=> si s si' [heqs /eandsE_cat [hsce1 hscx1]]; rewrite /sem_assgn; t_xrbindP.
    move=> vei hvei vei' htri hwi.
    have [v hv ?] := wi2i_eP hsce heqs hsce1 hvei; subst vei; rewrite hv /=.
    have [v' htr' ?]:= esubtype_truncate_val hsub htri (sem_pexpr_type_of hv); rewrite htr' /=; subst vei'.
    apply: (wi2i_lvP (ety := etype_of_expr m e) (v:=v') heqs _ hscx1).
    + by rewrite (truncate_val_has_type htr').
    by rewrite (truncate_val_has_type htr') -(esubtype_sign_of hsub).
  + admit. (*  t_xrbindP => xs tg o es ii sci hnone sce hsce scx hscx <-.
    apply wequiv_opn with eq (fun vs1 vs2 => vs1 = vs2 /\ map type_of_val vs1 = sopn_tout o).
    + by apply wi2i_esP_none.
    + move=> s1 s2 _ vs ? vs' <- hex; exists vs' => //.
      by rewrite -(sopn_toutP hex).
    by move=> vs _ [<- htyof]; apply: wi2i_lvsP_none hscx. *)
  + t_xrbindP => xs o es ii sci hnone sce hsce scx hscx <- /=.
    apply wkequivP' => si0 s0.
    apply wequiv_syscall with
     eq (fun fs1 fs2 => [/\ fs1 = fs2, emem si0 = fmem fs1
                          & map type_of_val fs1.(fvals) = (scs_tout (syscall_sig_u o))]).
    + apply wrequiv_weaken with
        (fun si s => eqst tt si s ∧ sem_cond gd (eands (sce.1 ++ scx.1)) si = ok true) eq => //.
      + by move=> ?? [].
      by apply wi2i_esP_none.
    + rewrite /mk_fstate => s1 s2 [[<- _]] [[<- <- _] _] fs ? fvs' <- hex; exists fvs' => //.
      by have /= [] := syscall_u_toutP hex.
    move=> fs1 _ [<- hmem htyof] si s si' [[??] hpre]; rewrite /upd_estate; subst si0 s0.
    have /(_ sce.1) := (wi2i_lvsP_none htyof hscx); apply.
    rewrite -hmem with_mem_same.
    by case: hpre => -[_ ? ? hsc]; split => //; rewrite -sem_cond_with_scs.
  + move=> a ii sci; rewrite /wi2i_a_and; t_xrbindP.
    move=> ? [sc ai] ha <- <- /=.
    apply wequiv_assert => //.
    move=> _; split => //.
    move=> si s [heqs _].
    rewrite -cats1 eandsE_cat eandsE_1 => -[] hsc hai.
    by rewrite (wi2i_condP ha heqs hsc hai).
  + move=> e c1 c2 hc1 hc2 ii sci_; t_xrbindP => sce hsce ci1 /hc1{}hc1 ci2 /hc2{}hc2 <- /=.
    apply wequiv_if.
    + by move=> ??? [heqs hsc1] hsc; have := (wi2i_condP hsce heqs hsc1 hsc); eauto.
    move=> b; apply wequiv_weaken with (eqst tt) (eqst tt) => //; first by move=> ??[].
    by case: b.
  + move=> x dir lo hi c hc ii sci_; t_xrbindP.
    move=> /and4P [hfv /eqP htx /eqP htlo /eqP hthi] sclo hsclo schi hschi ci /hc{}hc <- /=.
    apply wequiv_for_eq with (eqst tt) => //.
    + by move=> > [].
    + move=> si s vis [heqs /eandsE_cat [hsclo1 hschi1] /=]; t_xrbindP.
      move=> vilo hvilo ? vihi hvihi <- <-.
      have [vlo hvlo ->] := wi2i_eP hsclo heqs hsclo1 hvilo.
      have [vhi hvhi ->] := wi2i_eP hschi heqs hschi1 hvihi.
      by rewrite /= hvlo hvhi /sign_of_expr /= htlo hthi /= !val_to_int_None; eauto.
    move=> i si s si' heqs hw.
    have [ |s' -> ?]:=  wi2i_lvarP_None heqs hfv _ hw; last by eauto.
    by move: (hwf_m x); case: (m x) => // -[??] []; rewrite htx.
  + move=> al c e ii' c' hc hc' ii sci_; t_xrbindP.
    move=> sce hsce ci /hc{}hc ci' /hc'{}hc' <- /=.
    apply wequiv_weaken with (eqst tt) (λ si s, eqst tt si s ∧ sem_cond (p_globs pi) (eands sce.1) si = ok true).
    1-2: by move=> > [].
    apply wequiv_while.
    + by move=> ??? [heqs hsc1] hsc; have := (wi2i_condP hsce heqs hsc1 hsc); eauto.
    + by rewrite -(cats0 c); apply wequiv_cat with (eqst tt) => //; apply: safe_assertP.
    by apply wequiv_weaken with (eqst tt) (eqst tt) => // > [].
  move=> xs f es ii sci_; t_xrbindP.
  move=> fsig hgetsig hsub sce hsce scx hscx <- /=.
  move: hgetsig; rewrite /get_sig; case heq : sigs => [a|] // [?]; subst a.
  apply wequiv_call_wa with (rpreF (eS:= wi2i_spec)) (rpostF (eS:=wi2i_spec)) (vs_pre fsig.1).
  + move=> si s vis [heqs /eandsE_cat [hsce1 _]] hsce2.
    have [vs hes ->] := wi2i_esP hsce heqs hsce1 hsce2; rewrite /vs_pre hes; exists vs => //.
    clear hsce.
    elim: fsig.1 es vs hsub hes => [|ety tin hrec1] [|e es] //=; t_xrbindP.
    + by move=> _ _ <-.
    move=> vs_ /andP [hsub hsubs] v hv vs hvs <-.
    have [-> ->] := hrec1 _ _ hsubs hvs; rewrite andbT.
    by rewrite (sem_pexpr_type_of hv) -(esubtype_sign_of hsub) to_etype_to_stype.
  + by move=> si s vis vs [[???] _] hvs; apply (wi2i_sem_pre heq).
  + by move=> si s vis vs [[???] _] ?; split => //; exists fsig.
  + by move=> fsi fs fri fr [_ [x]] + + [x']; rewrite heq => -[<-] [?? +] [<-]; apply wi2i_sem_post.
  + by apply hrec.
  move=> fsi fs fri fr [_ [x]] ++ [x']; rewrite heq => -[<-] [_ _ hpre] [<-] [?? [hall hfvals]].
  move=> si s si' [[_ _ hvm] /eandsE_cat [_ hscx1]]; rewrite /upd_estate hfvals in hall |- * => hw.
  by apply: (wi2i_lvsP hscx hscx1 _ _ _ hw).
Admitted.

End M.

Section FINAL.

Lemma build_infoP (info : var → option (signedness * var)) FV m :
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

Lemma wi2w_callP (get_info : _uprog → Sv.t * (var → option (signedness * var))) pi :
  wi2i_prog get_info p = ok pi ->
  forall fn fd, get_fundef (p_funcs p) fn = Some fd ->
  let info := (get_info p).2 in
  let fsig := (build_sig info (fn, fd)).2 in
  wiequiv_f pi p ev ev
     (λ _ _ fs1 fs2, fs_rel (vs_pre fsig.1) fs1 fs2)
     fn fn
     (λ _ _ _ _ fr1 fr2, fs_rel (vs_post fsig.2) fr1 fr2).
Proof.
  rewrite /wi2i_prog. 
  case: get_info => FV info; t_xrbindP.
  move=> M /build_infoP [hwf_m hMeq] /Sv.subset_spec hFVsub.
  move=> p_funcsi heqp' <-.
  have hp' := get_map_cfprog_name_gen' heqp'.
  move=> fn fd hfn.
  have hsigs : ∀ fn fd,
    get_fundef (p_funcs p) fn = Some fd →
    get_fundef [seq build_sig info i | i <- p_funcs p] fn =
       Some
          (map2 (λ (x : var_i) (ty : stype), to_etype (sign_of_var M x) ty) (f_params fd) (f_tyin fd),
           map2 (λ (x : var_i) (ty : stype), to_etype (sign_of_var M x) ty) (f_res fd) (f_tyout fd)).
  + move=> fn' fd' hfn'.
    rewrite /get_fundef assoc_mapE; last by move=> ? [].
    rewrite -/(get_fundef (p_funcs p) fn') hfn' /= /build_sig /=.
    case: fd' hfn' => /= finfo fci ftyin fparams fbody ftyout fres fextra hfn'.
    have heq : forall xs ty,
      (forall x, x \in map v_var xs -> Sv.In x FV) ->
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
  have /(_ fn) := wi2i_callP_aux hwf_m hsigs hp'.
  apply: wkequiv_io_weaken => //.
  + by move=> fsi fs ?;split => //; eexists; first apply hsig.
  by move=> fsi fs fri fr _ [?]; rewrite hsig => -[<-].
Qed.

End FINAL.
End PROOF.
