From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssralg.
Require Import ZArith Setoid Morphisms.
Require Export var type values.
Import Utf8 ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ----------------------------------------------------------- *)
Section Section.

Context {wsw: WithSubWord}.

Definition compat_val ty v :=
  compat_type (sw_allowed || ~~is_defined v) (type_of_val v) ty.

Lemma compat_valE ty v: compat_val ty v ->
  match v with
  | Vbool _ => ty = sbool
  | Vint _ => ty = sint
  | Varr len _ => ty = sarr len
  | Vword ws _ =>
    exists2 ws', ty = sword ws' &
     if sw_allowed then ((ws <= ws')%CMP:Prop) else ws = ws'
  | Vundef ty' _ => subtype ty' ty
  end.
Proof.
  rewrite /compat_val; case: v => [b|i|len t|ws w|t h] /= /compat_typeEl //.
  + by rewrite orbF => -[ws'] -> ?; eauto.
  rewrite orbT => {h}; case: t => > h //; try by subst ty.
  by case: h => ? -> /=.
Qed.

Lemma compat_valEl ty v: compat_val ty v ->
  match ty with
  | sbool => v = undef_b \/ exists b, v = Vbool b
  | sint  => v = undef_i \/ exists i, v = Vint i
  | sarr len => exists t, v = @Varr len t
  | sword ws =>
    v = undef_w \/
    exists ws', exists2 w:word ws', v = Vword w &
      if sw_allowed then ((ws' <= ws)%CMP:Prop) else ws = ws'
  end.
Proof.
  rewrite /compat_val => /compat_typeE; case: ty => [ | |len|ws [ws']] /type_of_valI //.
  move=> [ | [w]] -> /=; auto.
  rewrite orbF; right; eauto.
Qed.

Definition truncatable wdb ty v :=
 match v, ty with
 | Vbool _, sbool => true
 | Vint _, sint   => true
 | Varr p _, sarr p' => p == p'
 (* TODO: change the order of the conditions to simplify proofs
  suggestion: ws' ≤ ws || sw_allowed || ~~ wdb *)
 | Vword ws w, sword ws' =>  ~~wdb || (sw_allowed || (ws' <= ws)%CMP)
 | Vundef t _, _ => subtype t ty
 | _, _ => false
 end.

Lemma truncatable_arr wdb len a : truncatable wdb (sarr len) (@Varr len a).
Proof. by rewrite /truncatable /= eqxx. Qed.

Definition vm_truncate_val ty v :=
 match v, ty with
 | Vbool _, sbool => v
 | Vint _, sint   => v
 | Varr p _, sarr p' => if p == p' then v else undef_addr ty
 | Vword ws w, sword ws' =>
   if (sw_allowed || (ws' <= ws)%CMP) then
     if (ws <= ws')%CMP then Vword w else Vword (zero_extend ws' w)
   else undef_addr ty
 | Vundef t _, _ => undef_addr ty
 | _, _ => undef_addr ty
 end.

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

Lemma subtype_truncatable wdb t v :
  subtype t (type_of_val v) ->
  truncatable wdb t v.
Proof.
  rewrite /truncatable.
  case: v => [b|z|len a|ws w|t' i] /=.
  1-3: by move=> /subtypeE ->.
  by move=> /subtypeE [ws'] [-> ->]; rewrite !orbT.
  case/or3P: i => /eqP -> /subtypeE.
  1-2: by move=> ->.
  by move=> [? [-> ?]] /=.
Qed.

Lemma truncatable_type_of wdb v :
  truncatable wdb (type_of_val v) v.
Proof. by apply subtype_truncatable. Qed.

(* TODO: rename this lemma and its siblings; vm_truncate_val -> truncatable *)
Lemma vm_truncate_valE_wdb wdb ty v :
  truncatable wdb ty v ->
  match v with
  | Vbool b => ty = sbool /\ vm_truncate_val ty v = b
  | Vint i => ty = sint /\ vm_truncate_val ty v = i
  | Varr len a => ty = sarr len /\ vm_truncate_val ty v = Varr a
  | Vword ws w =>
     exists ws',
     [/\ ty = sword ws', ~~wdb || (sw_allowed || (ws' <= ws)%CMP) &
         vm_truncate_val ty v =
           (if sw_allowed || (ws' ≤ ws)%CMP then
              if (ws ≤ ws')%CMP then Vword w else Vword (zero_extend ws' w)
            else undef_addr (sword ws'))]

  | Vundef t h => subtype t ty /\ vm_truncate_val ty v = v
  end.
Proof.
  rewrite /truncatable /=.
  case: v => [b|z|len a|ws w|t i] //=; last first.
  + move=> h; split => //.
    apply: undef_addr_eq.
    move: h => /(subtype_trans (undef_t_subtype t)) /subtype_undef_tP <-.
    by rewrite (is_undef_undef_t i).
  all: case: ty => // >.
  + move=> h; eexists; split; eauto.
  by move=> /eqP <-; rewrite eqxx.
Qed.

Lemma vm_truncate_valE ty v :
  truncatable true ty v ->
  match v with
  | Vbool b => ty = sbool /\ vm_truncate_val ty v = b
  | Vint i => ty = sint /\ vm_truncate_val ty v = i
  | Varr len a => ty = sarr len /\ vm_truncate_val ty v = Varr a
  | Vword ws w =>
     exists ws',
     [/\ ty = sword ws', (sw_allowed || (ws' <= ws)%CMP) &
         vm_truncate_val ty v = if (ws <= ws')%CMP then Vword w else Vword (zero_extend ws' w)]
  | Vundef t h => subtype t ty /\ vm_truncate_val ty v = v
  end.
Proof.
  move=> /vm_truncate_valE_wdb; case: v => //.
  by move=> > [] ws [/= -> h ?]; exists ws; split; auto; rewrite h.
Qed.

Lemma compat_val_undef_addr t : compat_val t (undef_addr t).
Proof. by rewrite /compat_val; case: t => //= w; rewrite orbT /= wsize_le_U8. Qed.
Hint Resolve compat_val_undef_addr : core.

Lemma vm_truncate_val_compat v ty : compat_val ty (vm_truncate_val ty v).
Proof.
Opaque undef_addr.
  case : v => [b | i | p t | ws w | t ht] => //=.
  1-2: by case: ty => [||len|ws'] //=; rewrite /compat_val.
  + by case: ty => [||len|ws'] //=; case: eqP => [<-|//]; rewrite /compat_val.
  case: ty => [||len|ws'] //=; case: ifP => //= h; rewrite /compat_val; case: ifP => //=.
  by case: sw_allowed h => //= h1 h2; rewrite (cmp_le_antisym h2 h1).
Transparent undef_addr.
Qed.

Lemma vm_truncate_valEl_wdb wdb ty v :
  truncatable wdb ty v ->
  let vt := vm_truncate_val ty v in
  match ty with
  | sbool =>
      v = undef_b /\ vt = undef_b \/ exists2 b, v = Vbool b & vt = Vbool b
  | sint  => v = undef_i /\ vt = undef_i \/ exists2 i, v = Vint i & vt = Vint i
  | sarr len => exists2 t, v = @Varr len t & vt = Varr t
  | sword ws =>
    v = undef_w /\ vt = undef_w \/
    exists ws' (w:word ws'),
      [/\ v = Vword w,
         ~~wdb || (sw_allowed || (ws <= ws')%CMP) &
         vm_truncate_val ty v =
           (if sw_allowed || (ws ≤ ws')%CMP then
              if (ws' ≤ ws)%CMP then Vword w else Vword (zero_extend ws w)
            else undef_addr (sword ws))]
  end.
Proof.
  move=> /vm_truncate_valE_wdb /=; case: v => /=.
  1,2: by move=> ? [-> ]; eauto.
  + by move=> > [-> ] _; rewrite eqxx; eauto.
  + move=> ws w [ws' [-> h ?]]; right.
    do 2!eexists; split; eauto.
  move=> t i [/subtypeEl + ->].
  have /or3P [] := i => /eqP ?; subst t.
  1,2: by move=> ->;left; split; apply Vundef_eq.
  by move=> [sz' [-> ?]]; left; split; apply Vundef_eq.
Qed.

Lemma vm_truncate_valEl ty v :
  truncatable true ty v ->
  let vt := vm_truncate_val ty v in
  match ty with
  | sbool =>
      v = undef_b /\ vt = undef_b \/ exists2 b, v = Vbool b & vt = Vbool b
  | sint  => v = undef_i /\ vt = undef_i \/ exists2 i, v = Vint i & vt = Vint i
  | sarr len => exists2 t, v = @Varr len t & vt = Varr t
  | sword ws =>
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

Lemma vm_truncate_val_subtype ty v:
  (sw_allowed -> ~is_sword ty) -> DB true v ->
  truncatable true ty v ->
  subtype ty (type_of_val v).
Proof.
  move=> hna hdb htr.
  move/vm_truncate_valE: htr hdb; case: v => [b | i | p t | ws w | t ht] /=.
  1,2,3: by move=> [-> ].
  + by move=> [ws' [? + _] _]; subst ty; case: sw_allowed hna => //= /(_ erefl).
  by rewrite /DB /= => -[] + _ /eqP ?; subst t => /subtypeEl ->.
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

Lemma compat_value_uincl_undef ty v :
  compat_val ty v ->
  value_uincl (undef_addr ty) v.
Proof.
  move=> /compat_typeEl.
  case: v => //= [b -> | z -> | len a -> | ws w [ws' -> hle] | t i] //=.
  + by apply WArray.uincl_empty.
  by (case: (is_undef_tE i) => ?; subst t) => [ -> | -> | [ws ->]].
Qed.

Lemma vm_truncate_val_eq ty v :
  type_of_val v = ty -> vm_truncate_val ty v = v.
Proof.
  rewrite /vm_truncate_val => <-; case: v => //= [ len a | ws w | t h].
  + by rewrite eqxx.
  + by rewrite cmp_le_refl orbT.
  by apply/undef_addr_eq/is_undef_undef_t.
Qed.

Lemma vm_truncate_val_subtype_word v ws:
  DB true v ->
  subtype (sword ws) (type_of_val v) ->
  truncatable true (sword ws) v ->
  exists2 w : word ws, vm_truncate_val (sword ws) v = Vword w & to_word ws v = ok w.
Proof.
  move=> hd /subtypeEl [ws' [/type_of_valI [? | [w ?]]]] hle1; subst v => //=.
  rewrite if_zero_extend_w hle1 truncate_word_le //= => ->; eauto.
Qed.

Lemma to_word_vm_truncate_val wdb ws t v w:
  t = sword ws ->
  to_word ws v = ok w ->
  [/\ truncatable wdb t v, vm_truncate_val t v = (Vword w), DB wdb v & is_defined v].
Proof. by move=> -> /to_wordI' [sz' [w' [hle -> ->]]] /=; rewrite /truncatable /DB if_zero_extend_w hle !orbT. Qed.

Lemma compat_truncatable wdb ty1 ty2 v:
  compat_type sw_allowed ty1 ty2 ->
  truncatable wdb ty1 v ->
  truncatable wdb ty2 v.
Proof.
  rewrite /compat_type; case: ifP => hwsw; last by move=> /eqP ->; eauto.
  move=> hsub htr.
  move/vm_truncate_valE_wdb: htr hsub; case: v => [b | z | len a| ws w | t i]; rewrite /truncatable.
  1-3: by move=> [-> ?] /subtypeEl -> /=.
  + by move=> [ws' [-> ?? ]] /subtypeEl [sz' [-> h1]] /=; rewrite hwsw /= orbT.
  move=> [+ _]; apply subtype_trans.
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
  compat_type sw_allowed t1 t2 ->
  value_uincl v1 v2 ->
  value_uincl (vm_truncate_val t1 v1) (vm_truncate_val t2 v2).
Proof.
  case: (boolP sw_allowed) => /=; last by move=> _ /eqP ->; apply value_uincl_vm_truncate.
  move=> hsw.
  case: t1 => [||len|ws1] /subtypeEl.
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

Lemma truncatable_subtype (wdb : bool) ty v1 v2 :
  (wdb -> ~sw_allowed -> is_sword ty -> ~is_defined v1 -> subtype ty (type_of_val v2)) ->
  truncatable wdb ty v1 ->
  subtype (type_of_val v1) (type_of_val v2) ->
  truncatable wdb ty v2.
Proof.
  move=> + /vm_truncate_valE_wdb; case: v1 => [b | i | p t | ws w | t ht]; rewrite /truncatable.
  1,2: by move=> _ [-> _] /subtypeEl /type_of_valI [|[?]]->.
  + by move=> _ [-> _] /subtypeEl /type_of_valI [? ->] //=.
  + move=> _ [ws' [? h _]] /=; subst ty; case: v2 => // ws'' w' /= hle.
    + by case: wdb h => //=; case: sw_allowed => //= h; apply:cmp_le_trans h hle.
    by move/or3P:w' hle => []/eqP -> //=.
  move=> h [hsub _] /= /subtypeEl.
  rewrite -(@undef_addr_eq t _ ht) in h; last by apply is_undef_undef_t.
  move/or3P:ht hsub h => []/eqP -> //=.
  1,2: by move=> /eqP <- _ /type_of_valI [|[?]]->.
  case: ty => // w _ h [ws [/type_of_valI]] [|[w']] ?; subst v2 => //= _.
  by case: wdb h => //; case: sw_allowed => //=; apply.
Qed.

Lemma vm_truncate_val_uincl (wdb : bool) v1 v2 ty:
  (wdb -> ~sw_allowed -> is_sword ty -> ~is_defined v1 -> subtype ty (type_of_val v2)) ->
  truncatable wdb ty v1 ->
  value_uincl v1 v2 ->
  truncatable wdb ty v2 /\ value_uincl (vm_truncate_val ty v1) (vm_truncate_val ty v2).
Proof.
  move=> h htr hu; split.
  apply (truncatable_subtype h htr (value_uincl_subtype hu)).
  apply: value_uincl_vm_truncate hu.
Qed.

Lemma compat_truncate_uincl wdb t1 t2 v1 v2:
  compat_type sw_allowed t1 t2 ->
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
    apply: subtype_trans (value_uincl_subtype hu).
    by apply vm_truncate_val_subtype => //; rewrite hsw.
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
  by (case/or3P: i htt' => /eqP -> /subtypeEl) => [-> | -> | [? [-> _]]].
Qed.

End Section.

(* ----------------------------------------------------------- *)

Module Type VM.

  Parameter t : forall {wsw:WithSubWord}, Type.

  Parameter init : forall {wsw:WithSubWord}, t.

  Parameter get : forall {wsw:WithSubWord}, t -> var -> value.

  Parameter set : forall {wsw:WithSubWord}, t -> var -> value -> t.

  Parameter initP : forall {wsw:WithSubWord} x,
    get init x = undef_addr (vtype x).

  Parameter getP : forall {wsw:WithSubWord} vm x,
    compat_val (vtype x) (get vm x).

  Parameter setP : forall {wsw:WithSubWord} vm x v y,
    get (set vm x v) y = if x == y then vm_truncate_val (vtype x) v else get vm y.

  Parameter setP_eq : forall {wsw:WithSubWord} vm x v, get (set vm x v) x = vm_truncate_val (vtype x) v.

  Parameter setP_neq : forall {wsw:WithSubWord} vm x v y, x != y -> get (set vm x v) y = get vm y.

End VM.

Module Vm : VM.
  Section Section.

  Context {wsw: WithSubWord}.

  Definition wf (data: Mvar.t value) :=
    forall x v, Mvar.get data x = Some v -> compat_val (vtype x) v.

  Record t_ := { data :> Mvar.t value; prop : wf data }.
  Definition t := t_.

  Lemma init_prop : wf (Mvar.empty value).
  Proof. by move=> x v; rewrite Mvar.get0. Qed.

  Definition init := {| prop := init_prop |}.

  Definition get (vm:t) (x:var) := odflt (undef_addr (vtype x)) (Mvar.get vm x).

  Lemma set_prop (vm:t) x v : wf (Mvar.set vm x (vm_truncate_val (vtype x) v)).
  Proof.
    move=> y vy; rewrite Mvar.setP; case: eqP => [<- [<-] | _ /prop //].
    apply vm_truncate_val_compat.
  Qed.

  Definition set (vm:t) (x:var) v :=
    {| data := Mvar.set vm x (vm_truncate_val (vtype x) v); prop := @set_prop vm x v |}.

  Lemma initP x : get init x = undef_addr (vtype x).
  Proof. done. Qed.

  Lemma getP vm x : compat_val (vtype x) (get vm x).
  Proof. rewrite /get; case h : Mvar.get => [ v | ] /=;[apply: prop h | apply compat_val_undef_addr]. Qed.

  Lemma setP vm x v y :
    get (set vm x v) y = if x == y then vm_truncate_val (vtype x) v else get vm y.
  Proof. by rewrite /get /set Mvar.setP; case: eqP => [<- | hne]. Qed.

  Lemma setP_eq vm x v : get (set vm x v) x = vm_truncate_val (vtype x) v.
  Proof. by rewrite setP eqxx. Qed.

  Lemma setP_neq vm x v y : x != y -> get (set vm x v) y = get vm y.
  Proof. by rewrite setP => /negbTE ->. Qed.

  End Section.

End Vm.

Declare Scope vm_scope.
Delimit Scope vm_scope with vm.
Notation "vm .[ x ]" := (@Vm.get _ vm x) : vm_scope.
Notation "vm .[ x <- v ]" := (@Vm.set _ vm x v) : vm_scope.
Open Scope vm_scope.


Section GET_SET.

Context {wsw: WithSubWord}.

Lemma vm_truncate_val_get x vm :
  vm_truncate_val (vtype x) vm.[x] = vm.[x].
Proof. apply/compat_val_vm_truncate_val/Vm.getP. Qed.

Lemma getP_subtype vm x : subtype (type_of_val vm.[x]) (vtype x).
Proof. apply/compat_type_subtype/Vm.getP. Qed.

Lemma subtype_undef_get vm x :
  subtype (undef_t (vtype x)) (type_of_val vm.[x]).
Proof.
  have /compat_type_undef_t <- := Vm.getP vm x.
  apply undef_t_subtype.
Qed.

Definition set_var wdb vm x v :=
  Let _ := assert (DB wdb v) ErrAddrUndef in
  Let _ := assert (truncatable wdb (vtype x) v) ErrType in
  ok vm.[x <- v].

(* Ensure that the variable is defined *)
Definition get_var wdb vm x :=
  let v := vm.[x]%vm in
  Let _ := assert (~~wdb || is_defined v) ErrAddrUndef in
  ok v.

Definition get_vars wdb vm := mapM (get_var wdb vm).

Definition vm_initialized_on vm : seq var → Prop :=
  all (λ x, is_ok (get_var true vm x >>= of_val (vtype x))).

Lemma set_varP wdb vm x v vm' :
  set_var wdb vm x v = ok vm' <-> [/\ DB wdb v, truncatable wdb (vtype x) v & vm' = vm.[x <- v]].
Proof. by rewrite /set_var; split => [ | [-> -> -> //]]; t_xrbindP. Qed.

Lemma set_var_truncate wdb x v :
  DB wdb v -> truncatable wdb (vtype x) v ->
  forall vm, set_var wdb vm x v = ok vm.[x <- v].
Proof. by rewrite /set_var => -> ->. Qed.

Lemma set_var_eq_type wdb x v:
  DB wdb v -> type_of_val v = vtype x ->
  forall vm, set_var wdb vm x v = ok vm.[x <- v].
Proof. move => h1 h2; apply set_var_truncate => //; rewrite -h2; apply truncatable_type_of. Qed.

Lemma set_varDB wdb vm x v vm' : set_var wdb vm x v = ok vm' -> DB wdb v.
Proof. by move=> /set_varP []. Qed.

Lemma get_varP wdb vm x v : get_var wdb vm x = ok v ->
  [/\ v = vm.[x], ~~wdb || is_defined v & compat_val (vtype x) v].
Proof. rewrite/get_var;t_xrbindP => ? <-; split => //; apply Vm.getP. Qed.

Lemma get_var_compat wdb vm x v : get_var wdb vm x = ok v ->
   (~~wdb || is_defined v) /\ compat_val (vtype x) v.
Proof. by move=>/get_varP []. Qed.

Lemma get_var_undef vm x v ty h :
  get_var true vm x = ok v -> v <> Vundef ty h.
Proof. by move=> /get_var_compat [] * ?; subst. Qed.

Lemma get_varI vm x v : get_var true vm x = ok v ->
  match v with
  | Vbool _ => vtype x = sbool
  | Vint _ => vtype x = sint
  | Varr len _ => vtype x = sarr len
  | Vword ws _ =>
    exists2 ws', vtype x = sword ws' &
     if sw_allowed then ((ws <= ws')%CMP:Prop) else ws = ws'
  | Vundef ty' _ => False
  end.
Proof. by move=> /get_var_compat [] + /compat_valE; case: v. Qed.

Lemma get_varE vm x v : get_var true vm x = ok v ->
  match vtype x with
  | sbool => exists b, v = Vbool b
  | sint  => exists i, v = Vint i
  | sarr len => exists t, v = @Varr len t
  | sword ws =>
    exists ws', exists2 w:word ws', v = Vword w &
      if sw_allowed then ((ws' <= ws)%CMP:Prop) else ws = ws'
  end.
Proof.
  by move=> /get_var_compat [] h1 /compat_valEl h2; case:vtype h2 h1 => [ | | len | ws] // [->|].
Qed.

Lemma type_of_get_var wdb x vm v :
  get_var wdb vm x = ok v ->
  subtype (type_of_val v) (x.(vtype)).
Proof.
  by move=> /get_var_compat [] _; rewrite /compat_val /compat_type; case: ifP => // _ /eqP <-.
Qed.

(* We have a more precise result in the non-word cases. *)
Lemma type_of_get_var_not_word vm x v :
  (sw_allowed -> ~ is_sword x.(vtype)) ->
  get_var true vm x = ok v ->
  type_of_val v = x.(vtype).
Proof.
  move=> h /get_var_compat [] /= hdb; rewrite /compat_val /compat_type hdb orbF.
  case: ifP => //; last by move=> _ /eqP.
  by move=> /h; case: vtype => //= [||len] _ /subtypeE.
Qed.

Lemma get_word_uincl_eq vm x ws (w:word ws) :
  value_uincl (Vword w) vm.[x] ->
  subtype (vtype x) (sword ws) ->
  vm.[x] = Vword w.
Proof.
  move => /value_uinclE [ws' [w' [heq ]]]; have := getP_subtype vm x; rewrite heq.
  move=> /subtypeEl [ws''] [-> h1] /andP [h2 /eqP ->] /= h3.
  by have ? := cmp_le_antisym (cmp_le_trans h1 h3) h2; subst ws'; rewrite zero_extend_u.
Qed.

End GET_SET.

(* Attempt to simplify goals of the form [vm.[y0 <- z0]...[yn <- zn].[x]]. *)
Ltac t_vm_get :=
  repeat (
    rewrite Vm.setP_eq
    || (rewrite Vm.setP_neq; last (apply/eqP; by [|apply/nesym]))
  ).

(* ----------------------------------------------------------------------- *)
(* Generic relation over varmap                                            *)

Section REL.

  Context {wsw1 wsw2 : WithSubWord}.

  Section Section.

  Context (R:value -> value -> Prop).

  Definition vm_rel (P : var -> Prop) (vm1 : @Vm.t wsw1) (vm2 : @Vm.t wsw2) :=
    forall x, P x -> R (Vm.get vm1 x) (Vm.get vm2 x).

  Lemma vm_rel_set (P : var -> Prop) vm1 vm2 x v1 v2 :
    (P x -> R (vm_truncate_val (wsw:=wsw1) (vtype x) v1) (vm_truncate_val (wsw:=wsw2) (vtype x) v2)) ->
    vm_rel (fun z => x <> z /\ P z) vm1 vm2 ->
    vm_rel P vm1.[x <- v1] vm2.[x <- v2].
  Proof. move=> h hu y hy; rewrite !Vm.setP; case: eqP => heq; subst; auto. Qed.

  Lemma vm_rel_set_r (P : var -> Prop) vm1 vm2 x v2 :
    (P x -> R vm1.[x] (vm_truncate_val (wsw:=wsw2) (vtype x) v2)) ->
    vm_rel (fun z => x <> z /\ P z) vm1 vm2 ->
    vm_rel P vm1 (vm2.[x <- v2]).
  Proof. move=> h hu y hy; rewrite !Vm.setP; case: eqP => heq; subst; auto. Qed.

  Lemma vm_rel_set_l (P : var -> Prop) vm1 vm2 x v1 :
    (P x -> R (vm_truncate_val (wsw:=wsw1) (vtype x) v1) vm2.[x]) ->
    vm_rel (fun z => x <> z /\ P z) vm1 vm2 ->
    vm_rel P vm1.[x <- v1] vm2.
  Proof. move=> h hu y hy; rewrite !Vm.setP; case: eqP => heq; subst; auto. Qed.

  End Section.

  #[export] Instance vm_rel_impl :
    Proper (subrelation ==>
            pointwise_lifting (Basics.flip Basics.impl) (Tcons var Tnil) ==>
            @eq Vm.t ==> @eq Vm.t ==> Basics.impl) vm_rel.
  Proof. by move=> R1 R2 hR P1 P2 hP vm1 ? <- vm2 ? <- h x hx; apply/hR/h/hP. Qed.

  #[export] Instance vm_rel_m :
    Proper (relation_equivalence ==>
            pointwise_lifting iff (Tcons var Tnil) ==>
            @eq Vm.t ==> @eq Vm.t ==> iff) vm_rel.
  Proof.
    move=> R1 R2 hR P1 P2 hP vm1 ? <- vm2 ? <-; split; apply vm_rel_impl => //.
    1,3: by move=> ??;apply hR.
    1,2: by move=> x /=; case: (hP x).
  Qed.

  Definition vm_eq (vm1:Vm.t (wsw:=wsw1)) (vm2:Vm.t (wsw:=wsw2)) :=
    forall x, vm1.[x] = vm2.[x].

  Definition eq_on     (X:Sv.t) := vm_rel (@eq value) (fun x => Sv.In x X).
  Definition eq_ex (X:Sv.t) := vm_rel (@eq value) (fun x => ~Sv.In x X).

  Definition vm_uincl (vm1:Vm.t (wsw:=wsw1)) (vm2:Vm.t (wsw:=wsw2)) :=
    forall x, value_uincl vm1.[x] vm2.[x].

  Definition uincl_on     (X:Sv.t) := vm_rel value_uincl (fun x => Sv.In x X).
  Definition uincl_ex (X:Sv.t) := vm_rel value_uincl (fun x => ~Sv.In x X).

  #[export] Instance eq_on_impl :
    Proper (Basics.flip Sv.Subset ==> @eq Vm.t ==> @eq Vm.t ==> Basics.impl) eq_on.
  Proof. by move=> s1 s2 hS; apply vm_rel_impl. Qed.

  #[export] Instance eq_on_m :
    Proper (Sv.Equal ==> @eq Vm.t ==> @eq Vm.t ==> iff) eq_on.
  Proof. by move=> s1 s2 hS; apply vm_rel_m. Qed.

  #[export] Instance eq_ex_impl :
    Proper (Sv.Subset ==> @eq Vm.t ==> @eq Vm.t ==> Basics.impl) eq_ex.
  Proof. by move=> s1 s2 hS; apply vm_rel_impl => // x hnx hx; apply/hnx/hS. Qed.

  #[export] Instance eq_ex_m :
    Proper (Sv.Equal ==> @eq Vm.t ==> @eq Vm.t ==> iff) eq_ex.
  Proof. by move=> s1 s2 hS; apply vm_rel_m => // x; rewrite hS. Qed.

  #[export] Instance uincl_on_impl :
    Proper (Basics.flip Sv.Subset ==> @eq Vm.t ==> @eq Vm.t ==> Basics.impl) uincl_on.
  Proof. by move=> s1 s2 hS; apply vm_rel_impl. Qed.

  #[export] Instance uincl_on_m :
    Proper (Sv.Equal ==> @eq Vm.t ==> @eq Vm.t ==> iff) uincl_on.
  Proof. by move=> s1 s2 hS; apply vm_rel_m. Qed.

  #[export] Instance uincl_ex_impl :
    Proper (Sv.Subset ==> @eq Vm.t ==> @eq Vm.t ==> Basics.impl) uincl_ex.
  Proof. by move=> s1 s2 hS; apply vm_rel_impl => // x hnx hx; apply/hnx/hS. Qed.

  #[export] Instance uincl_ex_m :
    Proper (Sv.Equal ==> @eq Vm.t ==> @eq Vm.t ==> iff) uincl_ex.
  Proof. by move=> s1 s2 hS; apply vm_rel_m => // x; rewrite hS. Qed.

  Lemma vm_eq_vm_rel vm1 vm2 : vm_eq vm1 vm2 <-> vm_rel (@eq value) (fun _ => True) vm1 vm2.
  Proof. by split => [h x _ | h x]; apply h. Qed.

  Lemma vm_uincl_vm_rel vm1 vm2 : vm_uincl vm1 vm2 <-> vm_rel value_uincl (fun _ => True) vm1 vm2.
  Proof. by split => [h x _ | h x]; apply h. Qed.

End REL.

Notation "vm1 '=1' vm2" := (vm_eq vm1 vm2)
  (at level 70, vm2 at next level) : vm_scope.

Notation "vm1 '=[' s ']' vm2" := (eq_on s vm1 vm2)
  (at level 70, vm2 at next level,
  format "'[hv ' vm1  =[ s ] '/'  vm2 ']'") : vm_scope.

Notation "vm1 '=[\' s ']' vm2" := (eq_ex s vm1 vm2)
  (at level 70, vm2 at next level,
  format "'[hv ' vm1  =[\ s ] '/'  vm2 ']'") : vm_scope.

Notation "vm1 '<=1' vm2" := (vm_uincl vm1 vm2)
  (at level 70, vm2 at next level,
  format "'[hv ' vm1  <=1  '/'  vm2 ']'") : vm_scope.

Notation "vm1 '<=[' s ']' vm2" := (uincl_on s vm1 vm2)
  (at level 70, vm2 at next level,
  format "'[hv ' vm1  <=[ s ] '/'  vm2 ']'") : vm_scope.

Notation "vm1 '<=[\' s ']' vm2" := (uincl_ex s vm1 vm2)
  (at level 70, vm2 at next level,
  format "'[hv ' vm1  <=[\ s ] '/'  vm2 ']'") : vm_scope.

Section REL_EQUIV.
  Context {wsw : WithSubWord}.

  Lemma vm_rel_refl R P : Reflexive R -> Reflexive (vm_rel R P).
  Proof. by move=> h x v _. Qed.

  Lemma vm_rel_sym R P : Symmetric R -> Symmetric (vm_rel R P).
  Proof. by move=> h x y hxy v hv; apply/h/hxy. Qed.

  Lemma vm_rel_trans R P : Transitive R -> Transitive (vm_rel R P).
  Proof. move=> h x y z hxy hyz v hv; apply: h (hxy v hv) (hyz v hv). Qed.

  Lemma vm_relI R (P1 P2 : var -> Prop) vm1 vm2 :
    (forall x, P1 x -> P2 x) ->
    vm_rel R P2 vm1 vm2 -> vm_rel R P1 vm1 vm2.
  Proof. by move=> h hvm v /h hv; apply hvm. Qed.

  #[export]Instance equiv_vm_rel R P : Equivalence R -> Equivalence (vm_rel R P).
  Proof.
    by constructor; [apply: vm_rel_refl | apply: vm_rel_sym | apply: vm_rel_trans].
  Qed.

  #[export]Instance equiv_vm_eq : Equivalence vm_eq.
  Proof. by constructor => > // => [h1 x | h1 h2 x]; rewrite h1 ?h2. Qed.

  #[export]Instance equiv_eq_on s : Equivalence (eq_on s).
  Proof. apply equiv_vm_rel; apply eq_equivalence. Qed.

  #[export]Instance equiv_eq_ex s : Equivalence (eq_ex s).
  Proof. apply equiv_vm_rel; apply eq_equivalence. Qed.

  #[export]Instance po_vm_rel R P: PreOrder R -> PreOrder (vm_rel R P).
  Proof. by constructor; [apply: vm_rel_refl | apply: vm_rel_trans]. Qed.

  #[export]Instance po_value_uincl : PreOrder value_uincl.
  Proof. constructor => // ???; apply value_uincl_trans. Qed.

  #[export]Instance po_vm_uincl : PreOrder vm_uincl.
  Proof.
   constructor => [ vm1 // | vm1 vm2 vm3].
   rewrite !vm_uincl_vm_rel; apply vm_rel_trans => ???; apply value_uincl_trans.
  Qed.

  #[export]Instance po_uincl_on s : PreOrder (uincl_on s).
  Proof. apply po_vm_rel; apply po_value_uincl. Qed.

  #[export]Instance po_uincl_ex s : PreOrder (uincl_ex s).
  Proof. apply po_vm_rel; apply po_value_uincl. Qed.

  Lemma vm_uincl_refl vm : vm <=1 vm.
  Proof. done. Qed.

  Lemma vm_uinclT vm2 vm1 vm3 : vm1 <=1 vm2 -> vm2 <=1 vm3 -> vm1 <=1 vm3.
  Proof. rewrite !vm_uincl_vm_rel; apply vm_rel_trans => ???; apply: value_uincl_trans. Qed.

  Lemma eq_on_refl s vm : vm =[s] vm.
  Proof. by apply vm_rel_refl. Qed.

  Lemma eq_onT vm2 vm1 vm3 s:
    vm1 =[s] vm2 -> vm2 =[s] vm3 -> vm1 =[s] vm3.
  Proof. by apply vm_rel_trans => > -> ->. Qed.

  Lemma eq_onS s vm1 vm2 : vm1 =[s] vm2 -> vm2 =[s] vm1.
  Proof. by apply vm_rel_sym. Qed.

  Lemma eq_onI s1 s2 vm1 vm2 : Sv.Subset s1 s2 -> vm1 =[s2] vm2 -> vm1 =[s1] vm2.
  Proof. move=> h1; apply vm_relI; SvD.fsetdec. Qed.

  Lemma eq_ex_refl s vm : vm =[\s] vm.
  Proof. by apply vm_rel_refl. Qed.

  Lemma eq_exT vm2 vm1 vm3 s:
    vm1 =[\s] vm2 -> vm2 =[\s] vm3 -> vm1 =[\s] vm3.
  Proof. by apply vm_rel_trans => > -> ->. Qed.

  Lemma eq_exS s vm1 vm2 : vm1 =[\s] vm2 -> vm2 =[\s] vm1.
  Proof. by apply vm_rel_sym. Qed.

  Lemma eq_exI s1 s2 vm1 vm2 : Sv.Subset s2 s1 -> vm1 =[\s2] vm2 -> vm1 =[\s1] vm2.
  Proof. move=> h1; apply vm_relI; SvD.fsetdec. Qed.

  Lemma uincl_on_refl vm s : vm <=[s] vm.
  Proof. done. Qed.

  Lemma uincl_onT vm2 vm1 vm3 s:
    vm1 <=[s] vm2 -> vm2 <=[s] vm3 -> vm1 <=[s] vm3.
  Proof. apply vm_rel_trans => ???; apply value_uincl_trans. Qed.

  Lemma uincl_onI s1 s2 vm1 vm2 : Sv.Subset s1 s2 -> vm1 <=[s2] vm2 -> vm1 <=[s1] vm2.
  Proof. move=> h1; apply vm_relI; SvD.fsetdec. Qed.

  Lemma uincl_ex_refl s vm : vm <=[\s] vm.
  Proof. apply vm_rel_refl => ?; apply value_uincl_refl. Qed.

  Lemma uincl_exT vm2 vm1 vm3 s:
    vm1 <=[\s] vm2 -> vm2 <=[\s] vm3 -> vm1 <=[\s] vm3.
  Proof. apply vm_rel_trans => ???; apply value_uincl_trans. Qed.

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
    + apply: truncatable_subtype (htr1) (value_uincl_subtype hu).
      case: wdb hdb htr1 => //=; rewrite /DB /= => /orP [-> // | /eqP /type_of_valI].
      by move=> [-> /eqP <- | [b ->]].
    move=> z; rewrite !Vm.setP; case: eqP => // ??; last by apply hvm.
    by apply value_uincl_vm_truncate.
  Qed.

  Lemma vm_uincl_set vm1 vm2 x v1 v2 :
    value_uincl (vm_truncate_val (vtype x) v1) (vm_truncate_val (vtype x) v2) ->
    vm1 <=1 vm2 ->
    vm1.[x <- v1] <=1 vm2.[x <- v2].
  Proof. by rewrite !vm_uincl_vm_rel => hvu hu; apply vm_rel_set => //; apply: vm_relI hu. Qed.

  Lemma vm_uincl_set_l vm1 vm2 x v :
    value_uincl (vm_truncate_val (vtype x) v) vm2.[x] ->
    vm1 <=1 vm2 ->
    vm1.[x <- v] <=1 vm2.
  Proof. by rewrite !vm_uincl_vm_rel => hvu hu; apply vm_rel_set_l => //; apply: vm_relI hu. Qed.

  Lemma vm_uincl_set_r vm1 vm2 x v :
    value_uincl vm1.[x] (vm_truncate_val (vtype x) v) ->
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
    (Sv.In x X -> value_uincl (vm_truncate_val (vtype x) v1) (vm_truncate_val (vtype x) v2)) ->
    vm1 <=[Sv.remove x X] vm2 ->
    vm1.[x <- v1] <=[X] vm2.[x <- v2].
  Proof. move=> hvu hu; apply vm_rel_set => //; apply: vm_relI hu; SvD.fsetdec. Qed.

  Lemma uincl_on_set_l X vm1 vm2 x v :
    (Sv.In x X -> value_uincl (vm_truncate_val (vtype x) v) vm2.[x]) ->
    vm1 <=[Sv.remove x X] vm2 ->
    vm1.[x <- v] <=[X] vm2.
  Proof. move=> hvu hu; apply vm_rel_set_l => //; apply: vm_relI hu; SvD.fsetdec. Qed.

  Lemma uincl_on_set_r X vm1 vm2 x v :
    (Sv.In x X ->value_uincl vm1.[x] (vm_truncate_val (vtype x) v)) ->
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
    (~Sv.In x s -> vm_truncate_val (vtype x) v1 = vm_truncate_val (vtype x) v2) ->
    vm1 =[\Sv.add x s] vm2 ->
    vm1.[x<-v1] =[\ s] vm2.[x<-v2].
  Proof. move=> h1 h2; apply vm_rel_set => // z hz; apply h2; SvD.fsetdec. Qed.

  Lemma eq_ex_set_r s vm1 vm2 x v :
    (~Sv.In x s -> vm1.[x] = vm_truncate_val (vtype x) v) ->
    vm1 =[\Sv.add x s] vm2 ->
    vm1 =[\ s] vm2.[x<-v].
  Proof. move=> h1 h2; apply vm_rel_set_r => // z hz; apply h2; SvD.fsetdec. Qed.

  Lemma eq_ex_set_l s vm1 vm2 x v :
    (~Sv.In x s -> vm_truncate_val (vtype x) v = vm2.[x]) ->
    vm1 =[\Sv.add x s] vm2 ->
    vm1.[x<-v] =[\ s] vm2.
  Proof. move=> h1 h2; apply vm_rel_set_l => // z hz; apply h2; SvD.fsetdec. Qed.

  Lemma uincl_ex_set s vm1 vm2 x v1 v2 :
    (~Sv.In x s -> value_uincl (vm_truncate_val (vtype x) v1) (vm_truncate_val (vtype x) v2)) ->
    vm1 <=[\Sv.add x s] vm2 ->
    vm1.[x<-v1] <=[\ s] vm2.[x<-v2].
  Proof. move=> h1 h2; apply vm_rel_set => // z hz; apply h2; SvD.fsetdec. Qed.

  Lemma uincl_ex_set_r s vm1 vm2 x v :
    (~Sv.In x s -> value_uincl vm1.[x] (vm_truncate_val (vtype x) v)) ->
    vm1 <=[\Sv.add x s] vm2 ->
    vm1 <=[\ s] vm2.[x<-v].
  Proof. move=> h1 h2; apply vm_rel_set_r => // z hz; apply h2; SvD.fsetdec. Qed.

  Lemma uincl_ex_set_l s vm1 vm2 x v :
    (~Sv.In x s -> value_uincl (vm_truncate_val (vtype x) v) vm2.[x]) ->
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
    move=> /dup [] /(set_var_eq_on1 vm1') [hw2 h] hw1 hs.
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

  Lemma eq_on_empty vm1 vm2 :
    vm1 =[Sv.empty] vm2.
  Proof. by move => ?; SvD.fsetdec. Qed.

  Lemma uincl_on_empty vm1 vm2 :
    vm1 <=[Sv.empty] vm2.
  Proof. by move => ?; SvD.fsetdec. Qed.

  Hint Resolve eq_on_empty uincl_on_empty : core.

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

  Instance uincl_ex_trans dom : Transitive (uincl_ex dom).
  Proof. by move => x y z; apply: uincl_exT. Qed.

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

  Lemma vm_uincl_init vm : Vm.init <=1 vm.
  Proof. move=> z; rewrite Vm.initP; apply/compat_value_uincl_undef/Vm.getP. Qed.

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

#[export] Hint Resolve vm_uincl_refl eq_on_refl eq_ex_refl uincl_on_refl uincl_ex_refl vm_uincl_init : core.
#[export] Hint Resolve eq_on_empty uincl_on_empty : core.
#[export] Hint Resolve truncatable_arr : core.

#[export] Existing Instance vm_rel_impl.
#[export] Existing Instance vm_rel_m.
#[export] Existing Instance eq_on_impl.
#[export] Existing Instance eq_on_m.
#[export] Existing Instance eq_ex_impl.
#[export] Existing Instance eq_ex_m.
#[export] Existing Instance uincl_on_impl.
#[export] Existing Instance uincl_on_m.
#[export] Existing Instance uincl_ex_impl.
#[export] Existing Instance uincl_ex_m.
#[export] Existing Instance equiv_vm_rel.
#[export] Existing Instance equiv_vm_eq.
#[export] Existing Instance equiv_eq_on.
#[export] Existing Instance equiv_eq_ex.
#[export] Existing Instance po_vm_rel.
#[export] Existing Instance po_value_uincl.
#[export] Existing Instance po_vm_uincl.
#[export] Existing Instance po_uincl_on.
#[export] Existing Instance po_uincl_ex.
#[export] Existing Instance uincl_ex_trans.

#[ global ]Arguments get_var {wsw} wdb vm%vm_scope x.
#[ global ]Arguments set_var {wsw} wdb vm%vm_scope x v.

