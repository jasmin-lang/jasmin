From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import xseq.
Require Import warray_ word sem_type.
Require Import values.
Import Utf8.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Lemma is_undef_t_cword s : is_undef_t (cword s) -> s = U8.
Proof. by case: s. Qed.

Lemma is_undef_t_not_carr t : is_undef_t t -> is_not_carr t.
Proof. by case: t. Qed.

Lemma undef_tK t : undef_t (undef_t t) = undef_t t.
Proof. by case: t. Qed.

Lemma compat_ctype_undef_t b t1 t2 : compat_ctype b t1 t2 -> undef_t t1 = undef_t t2.
Proof. by move=> /compat_ctype_subctype h; rewrite -subctype_undef_tP (subctype_trans _ h). Qed.

Lemma Varr_inj n n' t t' (e: @Varr n t = @Varr n' t') :
  exists en: n = n', eq_rect n (λ s, WArray.array s) t n' en = t'.
Proof.
  case: e => ?; subst n'; exists erefl.
  exact: (Eqdep_dec.inj_pair2_eq_dec _ Z.eq_dec).
Qed.

Corollary Varr_inj1 n t t' : @Varr n t = @Varr n t' -> t = t'.
Proof.
  by move=> /Varr_inj [en ]; rewrite (Eqdep_dec.UIP_dec Z.eq_dec en erefl).
Qed.

Lemma Vword_inj sz sz' w w' (e: @Vword sz w = @Vword sz' w') :
  exists e : sz = sz', eq_rect sz (λ s, (word s)) w sz' e = w'.
Proof. by case: e => ?; subst sz' => [[<-]]; exists erefl. Qed.

Lemma ok_word_inj E sz sz' w w' :
  ok (@Vword sz w) = Ok E (@Vword sz' w') →
  ∃ e : sz = sz', eq_rect sz word w sz' e = w'.
Proof. by move => h; have /Vword_inj := ok_inj h. Qed.

Lemma undef_x_vundef t h : Vundef t h =
  match t with
  | cbool => undef_b
  | cint => undef_i
  | cword ws => undef_w
  | _ => Vundef t h
  end.
Proof.
  by case: t h => [||//|_ /[dup] /is_undef_t_cword ->] ?;
    f_equal; exact: Eqdep_dec.UIP_refl_bool.
Qed.

Lemma Vundef_eq t1 t2 i1 i2 :
  t1 = t2 ->
  Vundef t1 i1 = Vundef t2 i2.
Proof. by move=> ?; subst t2; rewrite (Eqdep_dec.UIP_dec Bool.bool_dec i1 i2). Qed.

Lemma is_undef_undef_t t :
  is_undef_t t ->
  undef_t t = t.
Proof. by move=> /or3P [] /eqP ->. Qed.

Lemma undef_addr_eq t1 t2 (i : is_undef_t t2) :
  undef_t t1 = t2 ->
  undef_addr t1 = Vundef t2 i.
Proof. by move=> ?; subst t2; case: t1 i => //= *; apply Vundef_eq. Qed.

Lemma type_of_valI v t :
  type_of_val v = t ->
  match t with
  | cbool => v = undef_b \/ exists b: bool, v = b
  | cint => v = undef_i \/ exists i: Z, v = i
  | carr len => exists a, v = @Varr len a
  | cword ws => v = undef_w \/ exists w, v = @Vword ws w
  end.
Proof.
  by move=> <-; case: v; last case; move=> > //=; eauto; rewrite undef_x_vundef; eauto.
Qed.

Lemma is_wordI v : is_word v → subctype (cword U8) (type_of_val v).
Proof. by case: v => // [> | [] > //] _; exact: wsize_le_U8. Qed.

Lemma values_uincl_trans {va vb vc} :
  values_uincl va vb → values_uincl vb vc → values_uincl va vc.
Proof. apply (Forall2_trans (la := va) (lb := vb) (lc := vc) value_uincl_trans). Qed.

Lemma check_ty_val_uincl v1 x v2 :
  check_ty_val x v1 → value_uincl v1 v2 → check_ty_val x v2.
Proof.
  rewrite /check_ty_val => h /value_uincl_subctype.
  by apply: subctype_trans.
Qed.

Lemma type_of_undef t : type_of_val (undef_addr t) = undef_t t.
Proof. by case: t. Qed.

Lemma is_defined_undef_addr ty :
  is_defined (undef_addr ty) -> exists len, ty = carr len.
Proof. case: ty => //=; eauto. Qed.

Lemma subctype_value_uincl_undef t v :
  subctype (undef_t t) (type_of_val v) ->
  value_uincl (undef_addr t) v.
Proof. by case: t => //= p /eqP /(@sym_eq ctype) /type_of_valI [a ->]; apply WArray.uincl_empty. Qed.

Lemma value_uincl_undef t v :
  undef_t t = undef_t (type_of_val v) ->
  value_uincl (undef_addr t) v.
Proof. move=> /subctype_undef_tP; apply subctype_value_uincl_undef. Qed.

Lemma value_uincl_undef_t t1 t2 :
  undef_t t1 = undef_t t2 ->
  value_uincl (undef_addr t1) (undef_addr t2).
Proof. by move=> h; apply value_uincl_undef; rewrite type_of_undef h undef_tK. Qed.

Lemma Array_set_uincl n1 n2
   (a1 a1': WArray.array n1) (a2 : WArray.array n2) wz al aa i (v:word wz):
  value_uincl (Varr a1) (Varr a2) ->
  WArray.set a1 al aa i v = ok a1' ->
  exists2 a2', WArray.set a2 al aa i v = ok a2' &
    value_uincl (Varr a1) (Varr a2).
Proof. move=> /= hu hs; have [?[]]:= WArray.uincl_set hu hs; eauto. Qed.

Lemma to_bool_undef v : to_bool v = undef_error -> v = undef_b.
Proof. by case: v => //= - [] // e; rewrite (Eqdep_dec.UIP_refl_bool _ e). Qed.

Lemma to_int_undef v : to_int v = undef_error -> v = undef_i.
Proof. by case: v => //= -[] // e; rewrite (Eqdep_dec.UIP_refl_bool _ e). Qed.

Lemma to_arr_undef p v : to_arr p v <> undef_error.
Proof. by case: v => //= ??; rewrite /WArray.cast; case: ifP. Qed.

Lemma to_wordI' sz v w : to_word sz v = ok w -> exists sz' (w': word sz'),
  [/\ (sz <= sz')%CMP, v = Vword w' & w = zero_extend sz w'].
Proof.
  move=> /to_wordI[sz' [w' [? /truncate_wordP[??]]]]; eexists _, _.
  by constructor; eauto.
Qed.

Lemma to_word_undef s v :
  to_word s v = undef_error -> v = undef_w.
Proof.
  by case: v => //= [> /truncate_word_errP |] [] // ??; rewrite undef_x_vundef.
Qed.

Lemma of_val_subctype t v sv : of_val t v = ok sv -> subctype t (type_of_val v).
Proof.
  case: t sv => > /of_val_typeE; try by move=> ->.
  by case=> ? [? [-> /truncate_wordP[]]].
Qed.

Lemma of_value_uincl ty v v' vt :
  value_uincl v v' -> of_val ty v = ok vt ->
  match v' with
  | Varr len a => exists (h: ty = carr len), WArray.uincl (eq_rect _ _ vt _ h) a
  | _ => of_val ty v' = ok vt
  end.
Proof.
  case: v => > /value_uinclE + /of_valE //;
   try (by move=> -> [? ]; subst=> /= ->).
  + by move=> [t2 ->] h [?]; subst => /= ->; exists erefl.
  move=> [sz2 [w2 [-> h]]] [ws' [? [w' []]]]; subst => /= h1 ->.
  exact: word_uincl_truncate h1.
Qed.

Lemma to_val_inj t (v1 v2: sem_t t) : to_val v1 = to_val v2 -> v1 = v2.
Proof. by case: t v1 v2 => /= > => [[]|[]| /Varr_inj1 |[]]. Qed.

Lemma of_val_to_val t (v : sem_t t) : of_val t (to_val v) = ok v.
Proof.
  case: t v => //=.
  + by move=> len a; rewrite WArray.castK.
  by move=> ws w; rewrite truncate_word_u.
Qed.

Lemma to_valI t (x: sem_t t) v : to_val x = v ->
  match v with
  | Vbool b => exists h: t = cbool, eq_rect _ _ x _ h = b
  | Vint i => exists h: t = cint, eq_rect _ _ x _ h = i
  | Varr len a => exists h: t = carr len, eq_rect _ _ x _ h = a
  | Vword ws w => exists h: t = cword ws, eq_rect _ _ x _ h = w
  | Vundef _ _ => False
  end.
Proof. by case: t x => /= > <-; exists erefl. Qed.

Lemma type_of_to_val t (s: sem_t t) : type_of_val (to_val s) = t.
Proof. by case: t s. Qed.

Lemma type_of_oto_val t (s: sem_ot t) : type_of_val (oto_val s) = t.
Proof. by case: t s => //= -[]. Qed.

Lemma val_uincl_alt t1 t2 : @val_uincl t1 t2 =
  match t1, t2 return sem_t t1 -> sem_t t2 -> Prop with
  | carr _, carr _ => WArray.uincl
  | cword s1, cword s2 => @word_uincl s1 s2
  | t1', t2' => if boolP (t1' == t2') is AltTrue h
    then eq_rect _ (fun x => sem_t t1' -> sem_t x -> Prop) eq _ (eqP h)
    else fun _ _ => False
  end.
Proof.
  have ctype_eq_dec := Bool.reflect_dec _ _ (ctype_eqb_OK _ _).
  by case: t1; case: t2 => >; rewrite /val_uincl //=;
    case: {-}_/ boolP => // h >;
    rewrite (Eqdep_dec.UIP_dec ctype_eq_dec (eqP h)).
Qed.

Lemma val_uinclEl t1 t2 v1 v2 :
  val_uincl v1 v2 ->
  match t1 return sem_t t1 -> sem_t t2 -> Prop with
  | carr len => fun v1 v2 => exists (h: t2 = carr len),
    WArray.uincl v1 (eq_rect _ _ v2 _ h)
  | cword ws => fun v1 v2 => exists ws' (h: t2 = cword ws'),
    word_uincl v1 (eq_rect _ _ v2 _ h)
  | t => fun v1 v2 => exists h: t2 = t, v1 = eq_rect _ _ v2 _ h
  end v1 v2.
Proof.
  case: t1 v1 => /=; case: t2 v2 => //=; try (exists erefl; done);
   rewrite /val_uincl /=.
  + by move=> > /[dup] /WArray.uincl_len ? ?; subst; exists erefl.
  by eexists; exists erefl.
Qed.

Lemma val_uinclE t1 t2 v1 v2 :
  val_uincl v1 v2 ->
  match t2 return sem_t t1 -> sem_t t2 -> Prop with
  | carr len => fun v1 v2 => exists (h: t1 = carr len),
    WArray.uincl (eq_rect _ _ v1 _ h) v2
  | cword ws => fun v1 v2 => exists ws' (h: t1 = cword ws'),
    word_uincl (eq_rect _ _ v1 _ h) v2
  | t => fun v1 v2 => exists h: t1 = t, v2 = eq_rect _ _ v1 _ h
  end v1 v2.
Proof.
  case: t1 v1 => /=; case: t2 v2 => //=; try (exists erefl; done);
    rewrite /val_uincl /=.
  + by move=> > /[dup] /WArray.uincl_len ? ?; subst; exists erefl.
  by eexists; exists erefl.
Qed.

Lemma value_uincl_defined wdb v1 v2 :
  value_uincl v1 v2 -> wdb || is_defined v1 -> wdb || is_defined v2.
Proof.
  case: wdb => //=.
  case: v1 => [b | z| len t| ws w | t i] /value_uinclE //; try by move=> ->.
  + by move=> [? ->].
  by move=> [? [? [-> _]]].
Qed.

Lemma value_uincl_DB wdb v1 v2 :
  value_uincl v1 v2 -> DB wdb v1 -> DB wdb v2.
Proof.
  case: wdb => //.
  case: v1 => [b | z| len t| ws w | t i] /value_uinclE; try by move=> ->.
  + by move=> [? ->]. + by move=> [? [? [-> _]]].
  by rewrite /DB => /= + /eqP ?; subst t => /eqP <-; rewrite eqxx orbT.
Qed.

Lemma truncate_val_typeE ty v vt :
  truncate_val ty v = ok vt ->
  match ty with
  | cbool => exists2 b: bool, v = b & vt = b
  | cint => exists2 i: Z, v = i & vt = i
  | carr len => exists2 a : WArray.array len, v = Varr a & vt = Varr a
  | cword ws => exists w ws' (w': word ws'),
    [/\ truncate_word ws w' = ok w, v = Vword w' & vt = Vword w]
  end.
Proof.
  rewrite /truncate_val; t_xrbindP; case: v => > /of_valE; case=> ?;
    try (by subst=> /= -> <-; eauto); case=> ? [? []]; subst=> /= hv -> <-.
  by eexists; eexists; eexists; constructor; auto.
Qed.

Lemma truncate_valE ty v vt :
  truncate_val ty v = ok vt ->
  match v with
  | Vbool b => ty = cbool /\ vt = b
  | Vint i => ty = cint /\ vt = i
  | Varr len a => ty = carr len /\ vt = Varr a
  | Vword ws w => exists ws' w',
    [/\ ty = cword ws', truncate_word ws' w = ok w' & vt = Vword w']
  | Vundef _ _ => False
  end.
Proof.
  case: ty => > /truncate_val_typeE
    => [ [] | [] | [] | [? [? [? []]]] ] ? -> -> //.
  by eexists; eexists; split; auto.
Qed.

Lemma truncate_valI ty v vt :
  truncate_val ty v = ok vt ->
  match vt with
  | Vbool b => ty = cbool /\ v = b
  | Vint i => ty = cint /\ v = i
  | Varr len a => ty = carr len /\ v = Varr a
  | Vword ws w => exists ws' (w': word ws'),
    [/\ ty = cword ws, truncate_word ws w' = ok w & v = Vword w']
  | Vundef _ _ => False
  end.
Proof.
  by case: ty => > /truncate_val_typeE
    => [ [] | [] | [] | [? [? [? []]]] ] ? -> -> //;
    eexists; eexists; split; auto.
Qed.

Lemma truncate_val_subctype ty v v' :
  truncate_val ty v = ok v' →
  subctype ty (type_of_val v).
Proof.
  by case: v => > /truncate_valE
   => [ [] | [] | [] | [?[?[+/truncate_wordP[??]]]]|//] => ->.
Qed.

Lemma truncate_val_has_type ty v v' :
  truncate_val ty v = ok v' →
  type_of_val v' = ty.
Proof.
  by case: v' => > /truncate_valI
    => [[]|[]|[]|[?[?[+/truncate_wordP[??]]]]|//]
    => ->.
Qed.

Lemma truncate_val_subctype_eq ty v v' :
  truncate_val ty v = ok v' ->
  subctype (type_of_val v) ty ->
  v = v'.
Proof.
  move=> /truncate_valE; case: v => [b | z | len a | ws w | //]; try by move=> [_ ->].
  move=> [ws' [w' [-> /truncate_wordP [h ->]->]]] /= /(cmp_le_antisym h) ?; subst ws'.
  by rewrite zero_extend_u.
Qed.

Lemma truncate_val_idem (t : ctype) (v v' : value) :
  truncate_val t v = ok v' -> truncate_val t v' = ok v'.
Proof.
  move=> /truncate_valI; case: v' => [b[]|z[]|len a[]|ws w[?[?[]]]| ] //= -> //=.
  + by move=> _; rewrite /truncate_val /= WArray.castK.
  by move=> _ _; rewrite /truncate_val /= truncate_word_u.
Qed.

Lemma subctype_truncate_val_idem ty1 ty2 v v1 v2 :
  subctype ty2 ty1 ->
  truncate_val ty1 v = ok v1 ->
  truncate_val ty2 v1 = ok v2 ->
  truncate_val ty2 v = ok v2.
Proof.
  move=> /subctypeE hsub /truncate_valE htr.
  case: v htr hsub => //.
  + by move=> b [-> ->] _.
  + by move=> z [-> ->] _.
  + by move=> len a [-> ->] _.
  move=> ws w [ws1 [w1 [-> /truncate_wordP [hcmp1 ->] ->]]] [ws2 [-> hcmp2]].
  rewrite /truncate_val /= truncate_word_le //= => -[<-].
  rewrite truncate_word_le /=; last by apply (cmp_le_trans hcmp2 hcmp1).
  by rewrite zero_extend_idem.
Qed.

Lemma subctype_truncate_val ty1 ty2 v v1 :
  subctype ty2 ty1 ->
  truncate_val ty1 v = ok v1 ->
  exists v2, truncate_val ty2 v1 = ok v2.
Proof.
  move=> /subctypeE hsub /truncate_valI htr.
  case: v1 htr hsub => //.
  + by move=> b [-> _] ->; eexists; reflexivity.
  + by move=> z [-> _] ->; eexists; reflexivity.
  + move=> len a [-> _] ->.
    by rewrite /truncate_val /= WArray.castK; eexists; reflexivity.
  move=> ws1 w1 [_ [_ [-> _ _]]] [ws2 [-> hcmp2]].
  rewrite /truncate_val /= truncate_word_le //.
  by eexists; reflexivity.
Qed.

Lemma truncate_val_defined ty v v' : truncate_val ty v = ok v' -> is_defined v'.
Proof. by move=> /truncate_valI; case: v'. Qed.

Lemma truncate_val_DB wdb ty v v' : truncate_val ty v = ok v' -> DB wdb v'.
Proof. by case: wdb => //; move=> /truncate_valI; case: v'. Qed.

Lemma value_uincl_truncate_r_gen ty y x' :
  value_uincl x' y →
  is_defined x' → type_of_val x' = ty →
  exists2 y', truncate_val ty y = ok y' & value_uincl x' y'.
Proof.
  case: x' => [b|z|len a|ws w|//] /value_uinclE
    => [ -> | -> | [a2 -> hincl] | [ws2 [w2 [-> hincl]]] ] _ <-;
    rewrite /truncate_val /=.
  + by eexists; first by reflexivity.
  + by eexists; first by reflexivity.
  + rewrite WArray.castK.
    by eexists; first by reflexivity.
  rewrite (word_uincl_truncate hincl (truncate_word_u _)).
  eexists; first by reflexivity.
  by apply word_uincl_refl.
Qed.

Lemma value_uincl_truncate_r ty x y x' :
  value_uincl x' y →
  truncate_val ty x = ok x' →
  exists2 y', truncate_val ty y = ok y' & value_uincl x' y'.
Proof.
  move=> hincl htr.
  by apply (value_uincl_truncate_r_gen hincl (truncate_val_defined htr) (truncate_val_has_type htr)).
Qed.

Lemma truncate_value_uincl t v1 v2 : truncate_val t v1 = ok v2 -> value_uincl v2 v1.
Proof.
  rewrite /truncate_val; case: t; t_xrbindP=> > /=.
  + by move=> /to_boolI -> <-.
  + by move=> /to_intI -> <-.
  + by move=> /to_arrI -> <-.
  by move=> /to_wordI [? [? [-> ? <-]]] /=; exact: truncate_word_uincl.
Qed.

Lemma value_uincl_truncate ty x y x' :
  value_uincl x y →
  truncate_val ty x = ok x' →
  exists2 y', truncate_val ty y = ok y' & value_uincl x' y'.
Proof.
  move=> hincl htr.
  have {}hincl := value_uincl_trans (truncate_value_uincl htr) hincl.
  by apply (value_uincl_truncate_r hincl htr).
Qed.

Lemma mapM2_truncate_value_uincl tyin vargs1 vargs1' :
  mapM2 ErrType truncate_val tyin vargs1 = ok vargs1' ->
  values_uincl vargs1' vargs1.
Proof.
  move/mapM2_Forall3.
  elim {vargs1 vargs1'} => //.
  move=> _ v1 v1' _ vargs1 vargs1' /truncate_value_uincl huincl _ ih.
  by constructor.
Qed.

Lemma mapM2_truncate_val tys vs1' vs1 vs2' :
  mapM2 ErrType truncate_val tys vs1' = ok vs1 ->
  values_uincl vs1' vs2' ->
  exists2 vs2, mapM2 ErrType truncate_val tys vs2' = ok vs2 &
    values_uincl vs1 vs2.
Proof.
  elim: tys vs1' vs1 vs2' => [ | t tys hrec] [|v1' vs1'] //=.
  + by move => ? ? [<-] /List_Forall2_inv_l ->; eauto.
  move=> vs1 vs2';t_xrbindP => v1 htr vs2 htrs <- /List_Forall2_inv_l [v] [vs] [->] [hv hvs].
  have [v2 -> hv2 /=]:= value_uincl_truncate hv htr.
  have [vs2'' -> hvs2 /=] := hrec _ _ _ htrs hvs;eexists; first reflexivity.
  by constructor.
Qed.

Lemma type_of_val_ltuple tout (p : sem_tuple tout) :
  List.map type_of_val (list_ltuple p) = tout.
Proof.
  elim: tout p => //= t1 [|t2 tout] /=.
  + by rewrite /sem_tuple /= => _ x;rewrite type_of_oto_val.
  by move=> hrec [] x xs /=; rewrite type_of_oto_val hrec.
Qed.

Lemma app_sopn_truncate_val T l f vargs (t:T) :
  app_sopn l f vargs = ok t ->
  exists vargs',
    mapM2 ErrType truncate_val l vargs = ok vargs' /\
    app_sopn l f vargs' = ok t.
Proof.
  elim: l f vargs => /= [|ty l ih] f [|v vargs] //.
  + move=> ->.
    by eexists; split; first by reflexivity.
  t_xrbindP=> w hv /ih [vargs' [htr hvargs']].
  rewrite /truncate_val hv /= htr /=.
  eexists; split; first by reflexivity.
  by rewrite /= of_val_to_val /=.
Qed.

Lemma truncate_val_app_sopn T l f vargs vargs' (t : T) :
  mapM2 ErrType truncate_val l vargs = ok vargs' ->
  app_sopn l f vargs' = ok t ->
  app_sopn l f vargs = ok t.
Proof.
  move => htr; move/mapM2_Forall3: htr f.
  elim => {l vargs vargs'} //=.
  move=> ty v v' tys vargs vargs' htr _ ih f.
  t_xrbindP=> w' ok_w' ok_t.
  move: htr => /[dup] /truncate_val_idem.
  rewrite /truncate_val ok_w' /=.
  t_xrbindP=> <- _ -> /to_val_inj -> /=.
  by apply ih.
Qed.

Lemma value_eqb_eq v1 v2 : value_eqb v1 v2 -> v1 = v2.
Proof.
  case: v1 v2 =>
   [b1 | n1 | ?? | sz1 w1 | t1 ht1] [b2 | n2 | ?? | sz2 w2 | t2 ht2] //=.
  1,2: by move=> /eqP ->.
  + case: eqP => // ?; subst sz2.
    by rewrite truncate_word_u => /eqP ->.
  move=> /eqP; apply Vundef_eq.
Qed.

Lemma value_eqb_refl v :
   match v with
   | Varr _ _ => false
   | _ => true
   end ->
  value_eqb v v.
Proof.
  by case: v => //= sz w _; rewrite eqxx truncate_word_u.
Qed.
