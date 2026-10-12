From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith Setoid Morphisms.
Require Import var type values values_facts.
Require Import varmap.
Import Utf8 ssrbool.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Section Section.
Context {wsw: WithSubWord}.

Lemma compat_valE ty v: compat_val ty v ->
  match v with
  | Vbool _ => ty = cbool
  | Vint _ => ty = cint
  | Varr len _ => ty = carr len
  | Vword ws _ =>
    exists2 ws', ty = cword ws' &
     if sw_allowed then ((ws <= ws')%CMP:Prop) else ws = ws'
  | Vundef ty' _ => subctype ty' ty
  end.
Proof.
  rewrite /compat_val; case: v => [b|i|len t|ws w|t h] /= /compat_ctypeEl //.
  + by rewrite orbF => -[ws'] -> ?; eauto.
  rewrite orbT => {h}; case: t => > h //; try by subst ty.
  by case: h => ? -> /=.
Qed.

Lemma compat_valEl ty v: compat_val ty v ->
  match ty with
  | cbool => v = undef_b \/ exists b, v = Vbool b
  | cint  => v = undef_i \/ exists i, v = Vint i
  | carr len => exists t, v = @Varr len t
  | cword ws =>
    v = undef_w \/
    exists ws', exists2 w:word ws', v = Vword w &
      if sw_allowed then ((ws' <= ws)%CMP:Prop) else ws = ws'
  end.
Proof.
  rewrite /compat_val => /compat_ctypeE; case: ty => [ | |len|ws [ws']] /type_of_valI //.
  move=> [ | [w]] -> /=; auto.
  rewrite orbF; right; eauto.
Qed.

Lemma truncatable_cword ws (v: word ws) :
  truncatable true (cword ws) (Vword v).
Proof. by rewrite /= cmp_le_refl orbT. Qed.

Lemma if_zero_extend_w ws ws' (w:word ws) :
  (if (ws ≤ ws')%CMP then Vword w else Vword (zero_extend ws' w)) =
  if (ws' ≤ ws)%CMP then Vword (zero_extend ws' w) else Vword w.
Proof.
  case: ifPn.
  + by case: ifPn => // h1 h2; have ? := cmp_le_antisym h1 h2; subst ws'; rewrite zero_extend_u.
  by rewrite cmp_nle_lt => h; rewrite (cmp_lt_le h).
Qed.

Lemma compat_val_truncatable wdb t v :
  compat_val t v ->
  truncatable wdb t v.
Proof.
  move=> /compat_valE; rewrite /truncatable /=.
  case: v => [b ->|z ->|len a ->|ws w [ws' -> h]|t' i] //=.
  by apply/orP; right; case: sw_allowed h => //= ->.
Qed.

Lemma subctype_truncatable wdb t v :
  subctype t (type_of_val v) ->
  truncatable wdb t v.
Proof.
  rewrite /truncatable.
  case: v => [b|z|len a|ws w|t' i] /=.
  1-3: by move=> /subctypeE ->.
  by move=> /subctypeE [ws'] [-> ->]; rewrite !orbT.
  case/or3P: i => /eqP -> /subctypeE.
  1-2: by move=> ->.
  by move=> [? [-> ?]] /=.
Qed.

Lemma truncatable_type_of wdb v :
  truncatable wdb (type_of_val v) v.
Proof. by apply subctype_truncatable. Qed.

(* TODO: rename this lemma and its siblings; vm_truncate_val -> truncatable *)
Lemma vm_truncate_valE_wdb wdb ty v :
  truncatable wdb ty v ->
  match v with
  | Vbool b => ty = cbool /\ vm_truncate_val ty v = b
  | Vint i => ty = cint /\ vm_truncate_val ty v = i
  | Varr len a => ty = carr len /\ vm_truncate_val ty v = Varr a
  | Vword ws w =>
     exists ws',
     [/\ ty = cword ws', ~~wdb || (sw_allowed || (ws' <= ws)%CMP) &
         vm_truncate_val ty v =
           (if sw_allowed || (ws' ≤ ws)%CMP then
              if (ws ≤ ws')%CMP then Vword w else Vword (zero_extend ws' w)
            else undef_addr (cword ws'))]

  | Vundef t h => subctype t ty /\ vm_truncate_val ty v = v
  end.
Proof.
  rewrite /truncatable /=.
  case: v => [b|z|len a|ws w|t i] //=; last first.
  + move=> h; split => //.
    apply: undef_addr_eq.
    move: h => /(subctype_trans (undef_t_subctype t)) /subctype_undef_tP <-.
    by rewrite (is_undef_undef_t i).
  all: case: ty => // >.
  + move=> h; eexists; split; eauto.
  by move=> /eqP <-; rewrite eqxx.
Qed.

Lemma vm_truncate_valE ty v :
  truncatable true ty v ->
  match v with
  | Vbool b => ty = cbool /\ vm_truncate_val ty v = b
  | Vint i => ty = cint /\ vm_truncate_val ty v = i
  | Varr len a => ty = carr len /\ vm_truncate_val ty v = Varr a
  | Vword ws w =>
     exists ws',
     [/\ ty = cword ws', (sw_allowed || (ws' <= ws)%CMP) &
         vm_truncate_val ty v = if (ws <= ws')%CMP then Vword w else Vword (zero_extend ws' w)]
  | Vundef t h => subctype t ty /\ vm_truncate_val ty v = v
  end.
Proof.
  move=> /vm_truncate_valE_wdb; case: v => //.
  by move=> > [] ws [/= -> h ?]; exists ws; split; auto; rewrite h.
Qed.

Lemma vm_truncate_valEl_wdb wdb ty v :
  truncatable wdb ty v ->
  let vt := vm_truncate_val ty v in
  match ty with
  | cbool =>
      v = undef_b /\ vt = undef_b \/ exists2 b, v = Vbool b & vt = Vbool b
  | cint  => v = undef_i /\ vt = undef_i \/ exists2 i, v = Vint i & vt = Vint i
  | carr len => exists2 t, v = @Varr len t & vt = Varr t
  | cword ws =>
    v = undef_w /\ vt = undef_w \/
    exists ws' (w:word ws'),
      [/\ v = Vword w,
         ~~wdb || (sw_allowed || (ws <= ws')%CMP) &
         vm_truncate_val ty v =
           (if sw_allowed || (ws ≤ ws')%CMP then
              if (ws' ≤ ws)%CMP then Vword w else Vword (zero_extend ws w)
            else undef_addr (cword ws))]
  end.
Proof.
  move=> /vm_truncate_valE_wdb /=; case: v => /=.
  1,2: by move=> ? [-> ]; eauto.
  + by move=> > [-> ] _; rewrite eqxx; eauto.
  + move=> ws w [ws' [-> h ?]]; right.
    do 2!eexists; split; eauto.
  move=> t i [/subctypeEl + ->].
  have /or3P [] := i => /eqP ?; subst t.
  1,2: by move=> <-;left; split; apply Vundef_eq.
  by move=> [sz' [-> ?]]; left; split; apply Vundef_eq.
Qed.

Lemma vm_truncate_valEl ty v :
  truncatable true ty v ->
  let vt := vm_truncate_val ty v in
  match ty with
  | cbool =>
      v = undef_b /\ vt = undef_b \/ exists2 b, v = Vbool b & vt = Vbool b
  | cint  => v = undef_i /\ vt = undef_i \/ exists2 i, v = Vint i & vt = Vint i
  | carr len => exists2 t, v = @Varr len t & vt = Varr t
  | cword ws =>
    v = undef_w /\ vt = undef_w \/
    exists ws' (w:word ws'),
      [/\ v = Vword w,
          vt = if (ws' <= ws)%CMP then Vword w else Vword (zero_extend ws w) &
          sw_allowed || (ws <= ws')%CMP]
  end.
Proof.
  move=> /vm_truncate_valEl_wdb /=; case: ty => // ? []; auto.
  move=> [? [? [-> h ->]]]; rewrite h; right; do 2!eexists; split; eauto.
Qed.

Lemma vm_truncate_val_subctype ty v:
  (sw_allowed -> ~is_cword ty) -> DB true v ->
  truncatable true ty v ->
  subctype ty (type_of_val v).
Proof.
  move=> hna hdb htr.
  move/vm_truncate_valE: htr hdb; case: v => [b | i | p t | ws w | t ht] /=.
  1,2,3: by move=> [-> ].
  + by move=> [ws' [? + _] _]; subst ty; case: sw_allowed hna => //= /(_ erefl).
  by rewrite /DB /= => -[] + _ /eqP ?; subst t => /subctypeEl ->.
Qed.

Lemma vm_truncate_value_uincl wdb t v :
  truncatable wdb t v → value_uincl (vm_truncate_val t v) v.
Proof.
  move=> /vm_truncate_valE_wdb; case: v.
  1-3: by move=> > [-> ]// ->.
  + move => ws w [ws' [-> ? ->]].
    case: ifPn => //= _.
    case: ifPn => //; rewrite cmp_nle_lt => hlt /=.
    by apply/word_uincl_zero_ext/cmp_lt_le.
  by move=> > [? ->].
Qed.

Lemma vm_truncate_val_DB wdb ty v:
  truncatable wdb ty v ->
  DB wdb v = DB wdb (vm_truncate_val ty v).
Proof.
  case: wdb => //.
  move=> /vm_truncate_valE; case: v => [b [_ ->]| z [_ ->] | len a [_ ->] | ws w | t i [_ ->]] //=.
  by move=> [ws' [_ _ ->]]; case: ifP.
Qed.

Lemma vm_truncate_val_defined wdb ty v:
  truncatable wdb ty v ->
  (~~wdb || is_defined v) = (~~wdb || is_defined (vm_truncate_val ty v)).
Proof.
  case: wdb => //.
  move=> /vm_truncate_valE; case: v => [b [_ ->]| z [_ ->] | len a [_ ->] | ws w | t i [_ ->]] //=.
  by move=> [ws' [_ _ ->]]; case: ifP.
Qed.

Lemma vm_truncate_val_eq ty v :
  type_of_val v = ty -> vm_truncate_val ty v = v.
Proof.
  rewrite /vm_truncate_val => <-; case: v => //= [ len a | ws w | t h].
  + by rewrite eqxx.
  + by rewrite cmp_le_refl orbT.
  by apply/undef_addr_eq/is_undef_undef_t.
Qed.

Lemma vm_truncate_val_subctype_word v ws:
  DB true v ->
  subctype (cword ws) (type_of_val v) ->
  truncatable true (cword ws) v ->
  exists2 w : word ws, vm_truncate_val (cword ws) v = Vword w & to_word ws v = ok w.
Proof.
  move=> hd /subctypeEl [ws' [/type_of_valI [? | [w ?]]]] hle1; subst v => //=.
  rewrite if_zero_extend_w hle1 truncate_word_le //= => ->; eauto.
Qed.

Lemma to_word_vm_truncate_val wdb ws t v w:
  t = cword ws ->
  to_word ws v = ok w ->
  [/\ truncatable wdb t v, vm_truncate_val t v = (Vword w), DB wdb v & is_defined v].
Proof. by move=> -> /to_wordI' [sz' [w' [hle -> ->]]] /=; rewrite /truncatable /DB if_zero_extend_w hle !orbT. Qed.

Lemma compat_truncatable wdb ty1 ty2 v:
  compat_ctype sw_allowed ty1 ty2 ->
  truncatable wdb ty1 v ->
  truncatable wdb ty2 v.
Proof.
  rewrite /compat_ctype; case: ifP => hwsw; last by move=> /eqP ->; eauto.
  move=> hsub htr.
  move/vm_truncate_valE_wdb: htr hsub; case: v => [b | z | len a| ws w | t i]; rewrite /truncatable.
  1-3: by move=> [-> ?] /subctypeEl <- /=.
  + by move=> [ws' [-> ?? ]] /subctypeEl [sz' [-> h1]] /=; rewrite hwsw /= orbT.
  move=> [+ _]; apply subctype_trans.
Qed.

Lemma value_uincl_vm_truncate v1 v2 ty:
  value_uincl v1 v2 ->
  value_uincl (vm_truncate_val ty v1) (vm_truncate_val ty v2).
Proof.
  move=> /value_uinclE; case: v1 => [b->|z->|len a|ws w|t i] //.
  + by move=> [a' ->];case: ty => //= ?; case:ifP.
  + move=> [ws' [w2 [-> /andP[hle1 /eqP ->]]]]; case: ty => //= ws2.
    case sw_allowed => /=.
    + case: (boolP (ws' <= ws2)%CMP).
      + by move=> /(cmp_le_trans hle1) -> /=; apply word_uincl_zero_ext.
      move=> hle2.
      case: (boolP (ws <= ws2)%CMP) => hle3 /=.
      + by rewrite -(zero_extend_idem _ hle3); apply word_uincl_zero_ext.
      by rewrite zero_extend_idem //; apply cmp_lt_le; rewrite -cmp_nle_lt.
    case: (boolP (ws2 <= ws)%CMP).
    + move=> hle2; rewrite (cmp_le_trans hle2 hle1).
      case: ifPn.
      + move=> /(cmp_le_antisym hle2) ?; subst ws2.
        by case: ifPn => //= ?; apply word_uincl_zero_ext.
      move=> ?; rewrite zero_extend_idem //; case:ifPn => //= ?; apply word_uincl_zero_ext.
      by apply: cmp_le_trans hle1.
    by move=> ?; case:ifP => // ?; case:ifP => //=.
    move=> /= ?; apply compat_value_uincl_undef; apply vm_truncate_val_compat.
Qed.

Lemma compat_vm_truncate_val t1 t2 v1 v2 :
  compat_ctype sw_allowed t1 t2 ->
  value_uincl v1 v2 ->
  value_uincl (vm_truncate_val t1 v1) (vm_truncate_val t2 v2).
Proof.
  case: (boolP sw_allowed) => /=; last by move=> _ /eqP ->; apply value_uincl_vm_truncate.
  move=> hsw.
  case: t1 => [||len|ws1] /subctypeEl.
  1-3: by move=> ->; apply  value_uincl_vm_truncate.
  move=> [ws2 [-> hle]].
  case: v1 => [b|z|len1 a1|ws1' w1|t i] /value_uinclE.
  1-2: by move=> -> /=.
  + by move=> [? -> ?] /=.
  + move=> [ws2' [w2 [-> /andP [hle' /eqP ->]]]] /=.
    rewrite hsw /=; case: ifPn => h1; case: ifPn => h2 //=.
    + by apply word_uincl_zero_ext.
    + have hle_ := cmp_le_trans h1 hle; rewrite -(zero_extend_idem _ hle_).
      by apply word_uincl_zero_ext.
    + rewrite cmp_nle_lt in h1; have h1_ := cmp_lt_le h1; rewrite zero_extend_idem //.
      by apply word_uincl_zero_ext; apply: cmp_le_trans hle'.
    rewrite cmp_nle_lt in h1; have h1_ := cmp_lt_le h1; rewrite zero_extend_idem //.
    by rewrite -(zero_extend_idem _ hle); apply word_uincl_zero_ext.
  move=> /=; move/or3P: i => [] /eqP ->; case: v2 => //= > _.
  by rewrite hsw /=; case: ifP => /=.
Qed.

Lemma truncatable_subctype (wdb : bool) ty v1 v2 :
  (wdb -> ~sw_allowed -> is_cword ty -> ~is_defined v1 -> subctype ty (type_of_val v2)) ->
  truncatable wdb ty v1 ->
  subctype (type_of_val v1) (type_of_val v2) ->
  truncatable wdb ty v2.
Proof.
  move=> + /vm_truncate_valE_wdb; case: v1 => [b | i | p t | ws w | t ht]; rewrite /truncatable.
  1,2: by move=> _ [-> _] /subctypeEl /= /esym /type_of_valI [|[?]]->.
  + by move=> _ [-> _] /subctypeEl /= /esym /type_of_valI [? ->] //=.
  + move=> _ [ws' [? h _]] /=; subst ty; case: v2 => // ws'' w' /= hle.
    + by case: wdb h => //=; case: sw_allowed => //= h; apply:cmp_le_trans h hle.
    by move/or3P:w' hle => []/eqP -> //=.
  move=> h [hsub _] /= /subctypeEl.
  rewrite -(@undef_addr_eq t _ ht) in h; last by apply is_undef_undef_t.
  move/or3P:ht hsub h => []/eqP -> //=.
  1,2: by move=> /eqP <- _ /esym /type_of_valI [|[?]]->.
  case: ty => // w _ h [ws [/type_of_valI]] [|[w']] ?; subst v2 => //= _.
  by case: wdb h => //; case: sw_allowed => //=; apply.
Qed.

Lemma vm_truncate_val_uincl (wdb : bool) v1 v2 ty:
  (wdb -> ~sw_allowed -> is_cword ty -> ~is_defined v1 -> subctype ty (type_of_val v2)) ->
  truncatable wdb ty v1 ->
  value_uincl v1 v2 ->
  truncatable wdb ty v2 /\ value_uincl (vm_truncate_val ty v1) (vm_truncate_val ty v2).
Proof.
  move=> h htr hu; split.
  apply (truncatable_subctype h htr (value_uincl_subctype hu)).
  apply: value_uincl_vm_truncate hu.
Qed.

Lemma compat_truncate_uincl wdb t1 t2 v1 v2:
  compat_ctype sw_allowed t1 t2 ->
  truncatable wdb t1 v1 ->
  value_uincl v1 v2 ->
  DB wdb v1 ->
  [/\ truncatable wdb t2 v2,
      value_uincl (vm_truncate_val t1 v1) (vm_truncate_val t2 v2) &
      DB wdb v2].
Proof.
  move=> hc htr1 hu hdb.
  have [|??]:= vm_truncate_val_uincl _ htr1 hu.
  + move=> /eqP/eqP ? /negP/negbTE hsw hword hndef; subst wdb.
    apply: subctype_trans (value_uincl_subctype hu).
    by apply vm_truncate_val_subctype => //; rewrite hsw.
  split.
  + by apply (compat_truncatable hc).
  + by apply compat_vm_truncate_val.
  by apply: value_uincl_DB hu hdb.
Qed.

Lemma vm_truncate_val_undef t : vm_truncate_val t (undef_addr t) = undef_addr t.
Proof. by case: t => //= p; rewrite eqxx. Qed.

Lemma compat_val_vm_truncate_val t v :
  compat_val t v -> vm_truncate_val t v = v.
Proof.
  move=> /compat_valE; case: v => [b ->|z ->|len a ->|ws w [ws' -> h]|t' i htt'] //=.
  + by rewrite eqxx.
  + case: sw_allowed h => [h1 | ?] /=.
    + by rewrite h1.
    by subst ws'; rewrite cmp_le_refl.
  apply undef_addr_eq.
  by (case/or3P: i htt' => /eqP -> /subctypeEl) => [<- | <- | [? [-> _]]].
Qed.

End Section.

Open Scope vm_scope.

Section GET_SET.
Context {wsw: WithSubWord}.

Lemma vm_truncate_val_get x vm :
  vm_truncate_val (eval_atype (vtype x)) vm.[x] = vm.[x].
Proof. apply/compat_val_vm_truncate_val/Vm.getP. Qed.

Lemma getP_subctype vm x : subctype (type_of_val vm.[x]) (eval_atype (vtype x)).
Proof. apply/compat_ctype_subctype/Vm.getP. Qed.

Lemma subctype_undef_get vm x :
  subctype (undef_t (eval_atype (vtype x))) (type_of_val vm.[x]).
Proof.
  have /compat_ctype_undef_t <- := Vm.getP vm x.
  apply undef_t_subctype.
Qed.

Lemma set_varP wdb vm x v vm' :
  set_var wdb vm x v = ok vm' <-> [/\ DB wdb v, truncatable wdb (eval_atype (vtype x)) v & vm' = vm.[x <- v]].
Proof. by rewrite /set_var; split => [ | [-> -> -> //]]; t_xrbindP. Qed.

Lemma set_var_truncate wdb x v :
  DB wdb v -> truncatable wdb (eval_atype (vtype x)) v ->
  forall vm, set_var wdb vm x v = ok vm.[x <- v].
Proof. by rewrite /set_var => -> ->. Qed.

Lemma set_var_eq_type wdb x v:
  DB wdb v -> type_of_val v = eval_atype (vtype x) ->
  forall vm, set_var wdb vm x v = ok vm.[x <- v].
Proof. move => h1 h2; apply set_var_truncate => //; rewrite -h2; apply truncatable_type_of. Qed.

Lemma set_varDB wdb vm x v vm' : set_var wdb vm x v = ok vm' -> DB wdb v.
Proof. by move=> /set_varP []. Qed.

Lemma get_varP wdb vm x v : get_var wdb vm x = ok v ->
  [/\ v = vm.[x], ~~wdb || is_defined v & compat_val (eval_atype (vtype x)) v].
Proof. rewrite/get_var;t_xrbindP => ? <-; split => //; apply Vm.getP. Qed.

Lemma get_var_compat wdb vm x v : get_var wdb vm x = ok v ->
   (~~wdb || is_defined v) /\ compat_val (eval_atype (vtype x)) v.
Proof. by move=>/get_varP []. Qed.

Lemma get_var_undef vm x v ty h :
  get_var true vm x = ok v -> v <> Vundef ty h.
Proof. by move=> /get_var_compat [] * ?; subst. Qed.

Lemma get_varI vm x v : get_var true vm x = ok v ->
  match v with
  | Vbool _ => eval_atype (vtype x) = cbool
  | Vint _ => eval_atype (vtype x) = cint
  | Varr len _ => eval_atype (vtype x) = carr len
  | Vword ws _ =>
    exists2 ws', eval_atype (vtype x) = cword ws' &
     if sw_allowed then ((ws <= ws')%CMP:Prop) else ws = ws'
  | Vundef ty' _ => False
  end.
Proof. by move=> /get_var_compat [] + /compat_valE; case: v. Qed.

Lemma get_varE vm x v : get_var true vm x = ok v ->
  match eval_atype (vtype x) with
  | cbool => exists b, v = Vbool b
  | cint  => exists i, v = Vint i
  | carr len => exists t, v = @Varr len t
  | cword ws =>
    exists ws', exists2 w:word ws', v = Vword w &
      if sw_allowed then ((ws' <= ws)%CMP:Prop) else ws = ws'
  end.
Proof.
  by move=> /get_var_compat [] h1 /compat_valEl h2; case:vtype h2 h1 => [ | | len | ws] // [->|].
Qed.

Lemma type_of_get_var wdb x vm v :
  get_var wdb vm x = ok v ->
  subctype (type_of_val v) (eval_atype x.(vtype)).
Proof.
  by move=> /get_var_compat [] _; rewrite /compat_val /compat_ctype; case: ifP => // _ /eqP <-.
Qed.

(* We have a more precise result in the non-word cases. *)
Lemma type_of_get_var_not_word vm x v :
  (sw_allowed -> ~ is_aword x.(vtype)) ->
  get_var true vm x = ok v ->
  type_of_val v = eval_atype x.(vtype).
Proof.
  move=> h /get_var_compat [] /= hdb; rewrite /compat_val /compat_ctype hdb orbF.
  case: ifP => //; last by move=> _ /eqP.
  by move=> /h; case: vtype => //= [||ws len] _ /subctypeE.
Qed.

Lemma get_word_uincl_eq vm x ws (w:word ws) :
  value_uincl (Vword w) vm.[x] ->
  subctype (eval_atype (vtype x)) (cword ws) ->
  vm.[x] = Vword w.
Proof.
  move => /value_uinclE [ws' [w' [heq ]]]; have := getP_subctype vm x; rewrite heq.
  move=> /subctypeEl [ws''] [-> h1] /andP [h2 /eqP ->] /= h3.
  by have ? := cmp_le_antisym (cmp_le_trans h1 h3) h2; subst ws'; rewrite zero_extend_u.
Qed.

End GET_SET.

Section REL.
  Context {wsw1 wsw2 : WithSubWord}.

  Lemma vm_eq_vm_rel vm1 vm2 : vm_eq vm1 vm2 <-> vm_rel (@eq value) (fun _ => True) vm1 vm2.
  Proof. by split => [h x _ | h x]; apply h. Qed.

End REL.

Section REL_EQUIV.
  Context {wsw : WithSubWord}.

  Lemma vm_relI R (P1 P2 : var -> Prop) vm1 vm2 :
    (forall x, P1 x -> P2 x) ->
    vm_rel R P2 vm1 vm2 -> vm_rel R P1 vm1 vm2.
  Proof. by move=> h hvm v /h hv; apply hvm. Qed.

  Lemma vm_uinclT vm2 vm1 vm3 : vm1 <=1 vm2 -> vm2 <=1 vm3 -> vm1 <=1 vm3.
  Proof. rewrite !vm_uincl_vm_rel; apply vm_rel_trans => ???; apply: value_uincl_trans. Qed.

  Lemma eq_onT vm2 vm1 vm3 s:
    vm1 =[s] vm2 -> vm2 =[s] vm3 -> vm1 =[s] vm3.
  Proof. by apply vm_rel_trans => > -> ->. Qed.

  Lemma eq_onS s vm1 vm2 : vm1 =[s] vm2 -> vm2 =[s] vm1.
  Proof. by apply vm_rel_sym. Qed.

  Lemma eq_onI s1 s2 vm1 vm2 : Sv.Subset s1 s2 -> vm1 =[s2] vm2 -> vm1 =[s1] vm2.
  Proof. move=> h1; apply vm_relI; SvD.fsetdec. Qed.

  Lemma eq_exT vm2 vm1 vm3 s:
    vm1 =[\s] vm2 -> vm2 =[\s] vm3 -> vm1 =[\s] vm3.
  Proof. by apply vm_rel_trans => > -> ->. Qed.

  Lemma eq_exS s vm1 vm2 : vm1 =[\s] vm2 -> vm2 =[\s] vm1.
  Proof. by apply vm_rel_sym. Qed.

  Lemma eq_exI s1 s2 vm1 vm2 : Sv.Subset s2 s1 -> vm1 =[\s2] vm2 -> vm1 =[\s1] vm2.
  Proof. move=> h1; apply vm_relI; SvD.fsetdec. Qed.

  Lemma uincl_onT vm2 vm1 vm3 s:
    vm1 <=[s] vm2 -> vm2 <=[s] vm3 -> vm1 <=[s] vm3.
  Proof. apply vm_rel_trans => ???; apply value_uincl_trans. Qed.

  Lemma uincl_onI s1 s2 vm1 vm2 : Sv.Subset s1 s2 -> vm1 <=[s2] vm2 -> vm1 <=[s1] vm2.
  Proof. move=> h1; apply vm_relI; SvD.fsetdec. Qed.

  Lemma uincl_exI s1 s2 vm1 vm2 :
    Sv.Subset s2 s1 -> vm1 <=[\s2] vm2 -> vm1 <=[\s1] vm2.
  Proof. move=> h1; apply vm_relI; SvD.fsetdec. Qed.

  Lemma eq_ex_union s1 s2 vm1 vm2 :
    vm1 =[\s1] vm2 -> vm1 =[\Sv.union s1 s2] vm2.
  Proof. apply: eq_exI; SvD.fsetdec. Qed.

  Lemma eq_exTI s1 s2 vm1 vm2 vm3 :
    vm1 =[\s1] vm2 ->
    vm2 =[\s2] vm3 ->
    vm1 =[\Sv.union s1 s2] vm3.
  Proof.
    move => h12 h23; apply: (@eq_exT vm2); apply: eq_exI; eauto; SvD.fsetdec.
  Qed.

  Lemma eq_ex_eq_on x y z e o :
    x =[\e]  y →
    z =[o] y →
    x =[Sv.diff o e] z.
  Proof. move => he ho j hj; rewrite he ?ho; SvD.fsetdec. Qed.

  Lemma vm_rel_set_var (wdb:bool) (P : var -> Prop) vm1 vm1' vm2 x v1 v2 :
    value_uincl v1 v2 ->
    vm_rel value_uincl (fun z => x <> z /\ P z) vm1 vm2 ->
    set_var wdb vm1 x v1 = ok vm1' ->
    set_var wdb vm2 x v2 = ok vm2.[x<-v2] /\ vm_rel value_uincl P vm1' vm2.[x<-v2].
  Proof.
    move=> hu hvm /set_varP [hdb htr1 ->].
    split.
    rewrite (set_var_truncate (value_uincl_DB hu hdb)) //.
    + apply: truncatable_subctype (htr1) (value_uincl_subctype hu).
      case: wdb hdb htr1 => //=; rewrite /DB /= => /orP [-> // | /eqP /type_of_valI].
      by move=> [-> /eqP <- | [b ->]].
    move=> z; rewrite !Vm.setP; case: eqP => // ??; last by apply hvm.
    by apply value_uincl_vm_truncate.
  Qed.

  Lemma vm_uincl_set vm1 vm2 x v1 v2 :
    value_uincl (vm_truncate_val (eval_atype (vtype x)) v1) (vm_truncate_val (eval_atype (vtype x)) v2) ->
    vm1 <=1 vm2 ->
    vm1.[x <- v1] <=1 vm2.[x <- v2].
  Proof. by rewrite !vm_uincl_vm_rel => hvu hu; apply vm_rel_set => //; apply: vm_relI hu. Qed.

  Lemma vm_uincl_set_l vm1 vm2 x v :
    value_uincl (vm_truncate_val (eval_atype (vtype x)) v) vm2.[x] ->
    vm1 <=1 vm2 ->
    vm1.[x <- v] <=1 vm2.
  Proof. by rewrite !vm_uincl_vm_rel => hvu hu; apply vm_rel_set_l => //; apply: vm_relI hu. Qed.

  Lemma vm_uincl_set_r vm1 vm2 x v :
    value_uincl vm1.[x] (vm_truncate_val (eval_atype (vtype x)) v) ->
    vm1 <=1 vm2 ->
    vm1 <=1 vm2.[x <- v].
  Proof. by rewrite !vm_uincl_vm_rel => hvu hu; apply vm_rel_set_r => //; apply: vm_relI hu. Qed.

  Lemma vm_uincl_set_var wdb vm1 vm1' vm2 x v1 v2 :
    value_uincl v1 v2 ->
    vm1 <=1 vm2 ->
    set_var wdb vm1 x v1 = ok vm1' ->
    set_var wdb vm2 x v2 = ok vm2.[x<-v2] /\ vm1' <=1 vm2.[x<-v2].
  Proof.
    move=> h1 /vm_uincl_vm_rel h2 h3.
    have /(_ (fun _ => True) vm2) [|? /vm_uincl_vm_rel //]:= vm_rel_set_var h1 _ h3.
    by apply: vm_relI h2.
  Qed.

  Lemma uincl_on_set X vm1 vm2 x v1 v2:
    (Sv.In x X -> value_uincl (vm_truncate_val (eval_atype (vtype x)) v1) (vm_truncate_val (eval_atype (vtype x)) v2)) ->
    vm1 <=[Sv.remove x X] vm2 ->
    vm1.[x <- v1] <=[X] vm2.[x <- v2].
  Proof. move=> hvu hu; apply vm_rel_set => //; apply: vm_relI hu; SvD.fsetdec. Qed.

  Lemma uincl_on_set_l X vm1 vm2 x v :
    (Sv.In x X -> value_uincl (vm_truncate_val (eval_atype (vtype x)) v) vm2.[x]) ->
    vm1 <=[Sv.remove x X] vm2 ->
    vm1.[x <- v] <=[X] vm2.
  Proof. move=> hvu hu; apply vm_rel_set_l => //; apply: vm_relI hu; SvD.fsetdec. Qed.

  Lemma uincl_on_set_r X vm1 vm2 x v :
    (Sv.In x X ->value_uincl vm1.[x] (vm_truncate_val (eval_atype (vtype x)) v)) ->
    vm1 <=[Sv.remove x X] vm2 ->
    vm1 <=[X] vm2.[x <- v].
  Proof. by move=> hvu hu; apply vm_rel_set_r => //; apply: vm_relI hu; SvD.fsetdec. Qed.

  Lemma uincl_on_set_var (wdb:bool) s vm1 vm1' vm2 x v1 v2 :
    value_uincl v1 v2 ->
    vm1 <=[Sv.remove x s] vm2 ->
    set_var wdb vm1 x v1 = ok vm1' ->
    set_var wdb vm2 x v2 = ok vm2.[x<-v2] /\ vm1' <=[s] vm2.[x<-v2].
  Proof. move=> h1 h2; apply vm_rel_set_var => // z hz; apply h2; SvD.fsetdec. Qed.

  Lemma eq_ex_set s vm1 vm2 x v1 v2 :
    (~Sv.In x s -> vm_truncate_val (eval_atype (vtype x)) v1 = vm_truncate_val (eval_atype (vtype x)) v2) ->
    vm1 =[\Sv.add x s] vm2 ->
    vm1.[x<-v1] =[\ s] vm2.[x<-v2].
  Proof. move=> h1 h2; apply vm_rel_set => // z hz; apply h2; SvD.fsetdec. Qed.

  Lemma eq_ex_set_r s vm1 vm2 x v :
    (~Sv.In x s -> vm1.[x] = vm_truncate_val (eval_atype (vtype x)) v) ->
    vm1 =[\Sv.add x s] vm2 ->
    vm1 =[\ s] vm2.[x<-v].
  Proof. move=> h1 h2; apply vm_rel_set_r => // z hz; apply h2; SvD.fsetdec. Qed.

  Lemma eq_ex_set_l s vm1 vm2 x v :
    (~Sv.In x s -> vm_truncate_val (eval_atype (vtype x)) v = vm2.[x]) ->
    vm1 =[\Sv.add x s] vm2 ->
    vm1.[x<-v] =[\ s] vm2.
  Proof. move=> h1 h2; apply vm_rel_set_l => // z hz; apply h2; SvD.fsetdec. Qed.

  Lemma uincl_ex_set s vm1 vm2 x v1 v2 :
    (~Sv.In x s -> value_uincl (vm_truncate_val (eval_atype (vtype x)) v1) (vm_truncate_val (eval_atype (vtype x)) v2)) ->
    vm1 <=[\Sv.add x s] vm2 ->
    vm1.[x<-v1] <=[\ s] vm2.[x<-v2].
  Proof. move=> h1 h2; apply vm_rel_set => // z hz; apply h2; SvD.fsetdec. Qed.

  Lemma uincl_ex_set_r s vm1 vm2 x v :
    (~Sv.In x s -> value_uincl vm1.[x] (vm_truncate_val (eval_atype (vtype x)) v)) ->
    vm1 <=[\Sv.add x s] vm2 ->
    vm1 <=[\ s] vm2.[x<-v].
  Proof. move=> h1 h2; apply vm_rel_set_r => // z hz; apply h2; SvD.fsetdec. Qed.

  Lemma uincl_ex_set_l s vm1 vm2 x v :
    (~Sv.In x s -> value_uincl (vm_truncate_val (eval_atype (vtype x)) v) vm2.[x]) ->
    vm1 <=[\Sv.add x s] vm2 ->
    vm1.[x<-v] <=[\ s] vm2.
  Proof. move=> h1 h2; apply vm_rel_set_l => // z hz; apply h2; SvD.fsetdec. Qed.

  Lemma uincl_ex_set_var (wdb:bool) s vm1 vm1' vm2 x v1 v2 :
    value_uincl v1 v2 ->
    vm1 <=[\s] vm2 ->
    set_var wdb vm1 x v1 = ok vm1' ->
    set_var wdb vm2 x v2 = ok vm2.[x<-v2] /\ vm1' <=[\ Sv.remove x s] vm2.[x<-v2].
  Proof. move=> h1 h2; apply vm_rel_set_var => // ??; apply h2; SvD.fsetdec. Qed.

  Lemma uincl_on_vm_uincl vm1 vm2 vm1' vm2' d :
    vm1  <=1   vm2 →
    vm1' <=[d] vm2' →
    vm1  =[\d] vm1'→
    vm2  =[\d] vm2' →
    vm1' <=1   vm2'.
  Proof.
    move => out on t1 t2 x.
    case: (Sv_memP x d); first exact: on.
    by move => hx; rewrite -!(t1, t2) //; apply out.
  Qed.

  Lemma eq_on_eq_vm vm1 vm2 vm1' vm2' d :
    (vm1  =1   vm2)%vm →
    vm1' =[d] vm2' →
    vm1  =[\d] vm1'→
    vm2  =[\d] vm2' →
    (vm1' =1   vm2')%vm.
  Proof.
    move => out on t1 t2 x.
    case: (Sv_memP x d); first exact: on.
    by move => hx; rewrite -!(t1, t2) //; apply out.
  Qed.

  Lemma eq_on_union vm1 vm2 vm1' vm2' X Y :
    vm1  =[X]  vm2 →
    vm1' =[Y]  vm2' →
    vm1  =[\Y] vm1'→
    vm2  =[\Y] vm2' →
    vm1' =[Sv.union Y X] vm2'.
  Proof.
    move => out on t1 t2 x hx.
    case: (Sv_memP x Y); first exact: on.
    move => hxY; rewrite -!(t1, t2) //; apply out; SvD.fsetdec.
  Qed.

  Lemma uincl_on_union vm1 vm2 vm1' vm2' X Y :
    vm1  <=[X]  vm2 →
    vm1' <=[Y]  vm2' →
    vm1  =[\Y] vm1'→
    vm2  =[\Y] vm2' →
    vm1' <=[Sv.union Y X] vm2'.
  Proof.
    move => out on t1 t2 x hx.
    case: (Sv_memP x Y); first exact: on.
    move => hxY; rewrite -!(t1, t2) //; apply out; SvD.fsetdec.
  Qed.

  Lemma set_var_eq_ex (wdb: bool) (x:var) v vm1 vm2 :
    set_var wdb vm1 x v = ok vm2 ->
    vm1 =[\ Sv.singleton x] vm2.
  Proof. move=> /set_varP [??->] z hz; rewrite Vm.setP_neq //; apply/eqP; SvD.fsetdec. Qed.

  Lemma set_var_eq_on1 wdb x v vm1 vm2 vm1':
    set_var wdb vm1  x v = ok vm2 ->
    set_var wdb vm1' x v = ok vm1'.[x <- v] /\ vm2 =[Sv.singleton x] vm1'.[x <- v].
  Proof.
    move=> /set_varP [hdb htr ->]; split; first by rewrite set_var_truncate.
    move=> z hz; rewrite !Vm.setP; case: eqP => // hne; SvD.fsetdec.
  Qed.

  Lemma set_var_eq_on wdb s x v vm1 vm2 vm1':
    set_var wdb vm1 x v = ok vm2 ->
    vm1 =[s] vm1' ->
    set_var wdb vm1' x v = ok vm1'.[x <- v] /\ vm2 =[Sv.add x s] vm1'.[x <- v].
  Proof.
    move=> /[dup] /(set_var_eq_on1 vm1') [hw2 h] hw1 hs.
    split => //; rewrite SvP.MP.add_union_singleton.
    apply: (eq_on_union hs h); apply: set_var_eq_ex; eauto.
  Qed.

  Lemma get_var_uincl_at wdb x vm1 vm2 v1 :
    (value_uincl vm1.[x] vm2.[x]) ->
    get_var wdb vm1 x = ok v1 ->
    exists2 v2, get_var wdb vm2 x = ok v2 & value_uincl v1 v2.
  Proof. rewrite /get_var; t_xrbindP => hu /(value_uincl_defined hu) -> <- /=; eauto. Qed.

  Lemma get_var_uincl wdb x vm1 vm2 v1:
    vm1 <=1 vm2 ->
    get_var wdb vm1 x = ok v1 ->
    exists2 v2, get_var wdb vm2 x = ok v2 & value_uincl v1 v2.
  Proof. move => /(_ x); exact: get_var_uincl_at. Qed.

  Lemma eq_on_uincl_on X vm1 vm2 : vm1 =[X] vm2 -> vm1 <=[X] vm2.
  Proof. by move=> H ? /H ->. Qed.

  Lemma eq_ex_uincl_ex X vm1 vm2: vm1 =[\X] vm2 -> vm1 <=[\X] vm2.
  Proof. by move=> H ? /H ->. Qed.

  Lemma vm_uincl_uincl_on dom vm1 vm2 :
    vm1 <=1 vm2 →
    vm1 <=[dom] vm2.
  Proof. by move => h x _; exact: h. Qed.

  Lemma vm_eq_eq_on dom vm1 vm2 :
    (vm1 =1 vm2)%vm →
    vm1 =[dom] vm2.
  Proof. by move => h x _; exact: h. Qed.

  Lemma uincl_on_union_and dom dom' vm1 vm2 :
   vm1 <=[Sv.union dom dom'] vm2 ↔
   vm1 <=[dom] vm2 ∧ vm1 <=[dom'] vm2.
  Proof.
    split.
    + by move => h; split => x hx; apply: h; SvD.fsetdec.
    by case => h h' x /Sv.union_spec[]; [ exact: h | exact: h' ].
  Qed.

  Lemma vm_uincl_uincl_ex dom vm1 vm2 :
    vm1 <=1 vm2 →
    vm1 <=[\dom] vm2.
  Proof. by move => h x _; exact: h. Qed.

  Lemma uincl_ex_empty vm1 vm2 :
    vm1 <=[\ Sv.empty ] vm2 ↔ vm_uincl vm1 vm2.
  Proof.
    split; last exact: vm_uincl_uincl_ex.
    move => h x; apply/h; SvD.fsetdec.
  Qed.

  Lemma eq_ex_disjoint_eq_on s s' x y :
    x =[\s] y →
    disjoint s s' →
    x =[s'] y.
  Proof. rewrite /disjoint /is_true Sv.is_empty_spec => h d r hr; apply: h; SvD.fsetdec. Qed.

  Lemma set_var_spec wdb x v vm1 vm2 vm1' :
    set_var wdb vm1 x v = ok vm2 ->
    exists vm2', [/\ set_var wdb vm1' x v = ok vm2', vm1' =[\ Sv.singleton x] vm2'  & vm2'.[x] = vm2.[x]  ].
  Proof.
    move=> /set_varP [hdb htr ->].
    exists vm1'.[x <- v]; split.
    + by rewrite set_var_truncate.
    + by apply vm_rel_set_r => //; SvD.fsetdec.
    by rewrite !Vm.setP_eq.
  Qed.

End REL_EQUIV.
