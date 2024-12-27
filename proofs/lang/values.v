(* * Syntax and semantics of the Jasmin source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import xseq.
Require Export warray_ word sem_type.
Import Utf8.
Require Import JMeq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ----------------------------------------------------------- *)

Definition is_undef_t (t: stype) := [|| t == sbool, t == sint, is_sabstract t | t == sword8 ].

Lemma is_undef_tE t : is_undef_t t -> [\/ t = sbool, t = sint,  is_sabstract t | t = sword8].
Proof. case/or4P => [/eqP | /eqP| | /eqP ] ; firstorder. Qed.

Lemma is_undef_t_sword s : is_undef_t (sword s) -> s = U8.
Proof. by case: s. Qed.

Lemma is_undef_t_not_sarr t : is_undef_t t -> is_not_sarr t.
Proof. by case: t. Qed.

Definition undef_t t := if is_sword t then sword8 else t.
Arguments undef_t _ : clear implicits.

Lemma is_undef_t_undef_t t : is_not_sarr t -> is_undef_t (undef_t t).
Proof. by case: t. Qed.

Lemma is_abstractP t : is_sabstract t -> exists s, t = sabstract s.
Proof. case: t => //=. eauto. Qed.

Lemma subtype_undef_tP t1 t2 :
  subtype (undef_t t1) t2 <-> undef_t t1 = undef_t t2.
Proof.
  case: t1 => [ | | len1 | ws1| s1] ; case: t2 => [ | | len2 | ws2 | s2] //=; split  => /eqP //=.
Qed.

Lemma undef_tK t : undef_t (undef_t t) = undef_t t.
Proof. by case: t. Qed.

Lemma undef_t_subtype ty : subtype (undef_t ty) ty.
Proof. by rewrite subtype_undef_tP. Qed.
#[global] Hint Resolve undef_t_subtype : core.

Lemma compat_type_undef_t b t1 t2 : compat_type b t1 t2 -> undef_t t1 = undef_t t2.
Proof. by move=> /compat_type_subtype h; rewrite -subtype_undef_tP (subtype_trans _ h). Qed.

(* ** Values
 * -------------------------------------------------------------------- *)
Section VALUE.

  Context {tabstract : Tabstract}.

  Variant value : Type :=
    | Vbool  :> bool -> value
    | Vint   :> Z    -> value
    | Varr   : forall len, WArray.array len -> value
    | Vword  : forall s, word s -> value
    | Vabstract : forall s, iabstract s -> value
    | Vundef : forall (t:stype), is_undef_t t -> value.
  Arguments Vundef _ _ : clear implicits.

  Lemma Varr_inj n n' t t' (e: @Varr n t = @Varr n' t') :
    exists en: n = n', eq_rect n (λ s, WArray.array s) t n' en = t'.
  Proof.
    case: e => ?; subst n'; exists erefl.
    exact: (Eqdep_dec.inj_pair2_eq_dec _ Pos.eq_dec).
  Qed.

  Corollary Varr_inj1 n t t' : @Varr n t = @Varr n t' -> t = t'.
  Proof.
    by move=> /Varr_inj [en ]; rewrite (Eqdep_dec.UIP_dec Pos.eq_dec en erefl).
  Qed.

  Lemma Vabstract_inj s s' a a' (e: @Vabstract s a = @Vabstract s' a') :
    exists en: s = s', eq_rect s (λ s, iabstract s) a s' en = a'.
  Proof. by case: e => ?; subst s' => [[<-]]; exists erefl. Qed.

  Corollary Vabstract_inj1 s a a' : @Vabstract s a = @Vabstract s a' -> a = a'.
  Proof.
    by move=> /Vabstract_inj [en ]; rewrite (Eqdep_dec.UIP_dec string_eq_dec en erefl).
  Qed.

  Lemma Vword_inj sz sz' w w' (e: @Vword sz w = @Vword sz' w') :
    exists e : sz = sz', eq_rect sz (λ s, (word s)) w sz' e = w'.
  Proof. by case: e => ?; subst sz' => [[<-]]; exists erefl. Qed.

  Lemma ok_word_inj E sz sz' w w' :
    ok (@Vword sz w) = Ok E (@Vword sz' w') →
    ∃ e : sz = sz', eq_rect sz word w sz' e = w'.
  Proof. by move => h; have /Vword_inj := ok_inj h. Qed.

  Notation undef_b := (Vundef sbool erefl).
  Notation undef_i := (Vundef sint erefl).
  Notation undef_w := (Vundef sword8 erefl).
  Notation undef_a s := (Vundef (sabstract s) erefl).

  Definition undef_v t (h1: is_not_sarr t) :=
    Vundef (undef_t t) (is_undef_t_undef_t h1).
  Arguments undef_v _ _ : clear implicits.

  Definition undef_addr t :=
    match t with
    | sarr n => Varr (WArray.empty n)
    | t0 => undef_v t0 erefl
    end.

  Definition values := seq value.

  Definition is_defined v := if v is Vundef _ _ then false else true.

  Lemma undef_x_vundef t h : Vundef t h =
                               match t with
                               | sbool => undef_b
                               | sint => undef_i
                               | sword ws => undef_w
                               | sabstract s => undef_a s
                               | _ => Vundef t h
                               end.
  Proof.
    case: t h  => [||//|_ /[dup] /is_undef_t_sword ->|? ] ?;
                  f_equal; exact: Eqdep_dec.UIP_refl_bool.
  Qed.

  Lemma Vundef_eq t1 t2 i1 i2 :
    t1 = t2 ->
    Vundef t1 i1 = Vundef t2 i2.
  Proof. by move=> ?; subst t2; rewrite (Eqdep_dec.UIP_dec Bool.bool_dec i1 i2). Qed.

  Lemma is_undef_undef_t t :
    is_undef_t t ->
    undef_t t = t.
  Proof.  move=> /or4P [/eqP ->| /eqP ->| /is_abstractP [] ? ->| /eqP ->]  //=. Qed.

  Lemma undef_addr_eq t1 t2 (i : is_undef_t t2) :
    undef_t t1 = t2 ->
    undef_addr t1 = Vundef t2 i.
  Proof. by move=> ?; subst t2; case: t1 i => //= *; apply Vundef_eq. Qed.

  (* ** Type of values
   * -------------------------------------------------------------------- *)

  Definition type_of_val v :=
    match v with
    | Vbool _ => sbool
    | Vint  _ => sint
    | Varr n _ => sarr n
    | Vword s _ => sword s
    | Vabstract s _ => sabstract s
    | Vundef t _ => t
    end.

  Lemma type_of_valI v t :
    type_of_val v = t ->
    match t with
    | sbool => v = undef_b \/ exists b: bool, v = b
    | sint => v = undef_i \/ exists i: Z, v = i
    | sarr len => exists a, v = @Varr len a
    | sabstract s => v = undef_a s \/ exists a, v = @Vabstract s a
    | sword ws => v = undef_w \/ exists w, v = @Vword ws w
    end.
  Proof.
    move=> <-; case: v; last case; move=> > //=; eauto; rewrite undef_x_vundef; eauto.
  Qed.

  Definition check_ty_val (ty:stype) (v:value) :=
    subtype ty (type_of_val v).

  Definition is_word v := is_sword (type_of_val v).

  Lemma is_wordI v : is_word v → subtype sword8 (type_of_val v).
  Proof. by case: v => // [> | [] > //] _; exact: wsize_le_U8. Qed.

  Definition DB wdb v :=
    ~~wdb || (is_defined v || (type_of_val v == sbool)).

  (* ** Test for extension of values
   * -------------------------------------------------------------------- *)

  Definition abstract_uincl (s1 s2 : string) (a1: iabstract s1) (a2: iabstract s2) :=
    if string_beq s1 s2 then JMeq a1 a2 else False.
    (* match s1 =P s2 with *)
    (* | ReflectT h => ecast s2 (iabstract s2) h a1 = a2 *)
    (* | _ => False *)
    (* end. *)

  Lemma abstract_uinclude_ext s1 s2 (a1:iabstract s1) (a2:iabstract s2) :
    (s1 = s2)%CMP /\ JMeq a1 a2 -> abstract_uincl a1 a2.
  Proof.
    unfold abstract_uincl.
    move => [/internal_string_dec_lb] -> //=.
  Qed.

  Lemma ext_abstract_uinclude s1 s2 (a1:iabstract s1) (a2:iabstract s2) :
    abstract_uincl a1 a2 -> (s1 = s2)%CMP /\ JMeq a1 a2.
  Proof.
    unfold abstract_uincl.
    destruct (string_beq s1 s2) eqn: h => ?.
    + apply internal_string_dec_bl in h => //=.
      by move.
  Qed.

  Lemma abstract_uincl_refl (s: string) (a: iabstract s): abstract_uincl a a.
  Proof. apply abstract_uinclude_ext; split ;[reflexivity|apply JMeq_refl]. Qed.

  Hint Resolve abstract_uincl_refl : core.

  Lemma abstract_uincl_trans (s1 s2 s3 : string) (a1 : iabstract s1)
    (a2 : iabstract s2) (a3 : iabstract s3) :
    abstract_uincl a1 a2 → abstract_uincl a2 a3 → abstract_uincl a1 a3.
  Proof.
    by move => /ext_abstract_uinclude [?] ? /ext_abstract_uinclude [?] ?; subst.
  Qed.

  Definition value_uincl (v1 v2:value) :=
    match v1, v2 with
    | Vbool b1, Vbool b2 => b1 = b2
    | Vint n1, Vint n2   => n1 = n2
    | Varr n1 t1, Varr n2 t2 => WArray.uincl t1 t2
    | Vword sz1 w1, Vword sz2 w2 => word_uincl w1 w2
    | Vabstract s1 a1, Vabstract s2 a2 => abstract_uincl a1 a2
    | Vundef t _, _ => subtype t (type_of_val v2)
    | _, _ => False
    end.

  Lemma value_uinclE v1 v2 :
    value_uincl v1 v2 →
    match v1 with
    | Varr n1 t1 => exists2 t2, v2 = @Varr n1 t2 & WArray.uincl t1 t2
    | Vword sz1 w1 => exists sz2 w2, v2 = @Vword sz2 w2 /\ word_uincl w1 w2
    | Vabstract s1 a1 => exists s2 a2, v2 = @Vabstract s2 a2 /\ abstract_uincl a1 a2
    | Vundef t _ => subtype t (type_of_val v2)
    | _ => v2 = v1
    end.
  Proof.
    case: v1 ; case: v2 => //= h; subst; eauto.
    move => ? H; rewrite H; reflexivity.
    move => ? H; rewrite H; reflexivity.
    move => ? ? ? H; have ?:= WArray.uincl_len H; subst; eauto.
  Qed.

  Lemma value_uincl_refl v: value_uincl v v.
  Proof.  case: v => //=. Qed.

  Lemma Array_set_uincl n1 n2
    (a1 a1': WArray.array n1) (a2 : WArray.array n2) wz al aa i (v:word wz):
    value_uincl (Varr a1) (Varr a2) ->
    WArray.set a1 al aa i v = ok a1' ->
    exists2 a2', WArray.set a2 al aa i v = ok a2' &
                   value_uincl (Varr a1) (Varr a2).
  Proof. move=> /= hu hs; have [?[]]:= WArray.uincl_set hu hs; eauto. Qed.

  Hint Resolve value_uincl_refl : core.

  Lemma value_uincl_subtype v1 v2 :
    value_uincl v1 v2 ->
    subtype (type_of_val v1) (type_of_val v2).
  Proof.
    case: v1 => [||||t h|] > /value_uinclE; try by move=> ->.
    + by case=> ?->.
    + by move=> [? [? [-> ]]] /= /andP [].
      move=> [x [? [-> H]]] /=.
      unfold abstract_uincl in H.
      destruct (string_beq t x) eqn: H1.
      apply internal_string_dec_bl in H1.
      subst => /=; case x => //=.
      by move.
  Qed.

  Lemma value_uincl_trans v2 v1 v3 :
    value_uincl v1 v2 -> value_uincl v2 v3 -> value_uincl v1 v3.
  Proof.
    case: v1 => > /value_uinclE; try by move=> -> /value_uinclE ->.
    + by move=> [? -> /WArray.uincl_trans h] /value_uinclE [? -> /h].
    + by move=> [? [? [-> /word_uincl_trans h]]] /value_uinclE [? [? [-> /h]]].
    + by move=> [? [? [-> /abstract_uincl_trans h]]] /value_uinclE [? [? [-> /h]]].
      by move=> h /value_uincl_subtype; apply: subtype_trans.
  Qed.

  Lemma check_ty_val_uincl v1 x v2 :
    check_ty_val x v1 → value_uincl v1 v2 → check_ty_val x v2.
  Proof.
    rewrite /check_ty_val => h /value_uincl_subtype.
    by apply: subtype_trans.
  Qed.

  Lemma type_of_undef t : type_of_val (undef_addr t) = undef_t t.
  Proof. by case: t. Qed.

  Lemma is_defined_undef_addr ty :
    is_defined (undef_addr ty) -> exists len, ty = sarr len.
  Proof. case: ty => //=; eauto. Qed.

  Lemma subtype_value_uincl_undef t v :
    subtype (undef_t t) (type_of_val v) ->
    value_uincl (undef_addr t) v.
  Proof.
    by case: t => //= p /eqP /(@sym_eq stype) /type_of_valI [a ->]; apply WArray.uincl_empty.
  Qed.

  Lemma value_uincl_undef t v :
    undef_t t = undef_t (type_of_val v) ->
    value_uincl (undef_addr t) v.
  Proof. move=> /subtype_undef_tP; apply subtype_value_uincl_undef. Qed.

  Lemma value_uincl_undef_t t1 t2 :
    undef_t t1 = undef_t t2 ->
    value_uincl (undef_addr t1) (undef_addr t2).
  Proof. by move=> h; apply value_uincl_undef; rewrite type_of_undef h undef_tK. Qed.

  (* ** Conversions between values and sem_t
   * -------------------------------------------------------------------- *)

  Definition to_bool v :=
    match v with
    | Vbool b => ok b
    | Vundef sbool _ => undef_error
    | _ => type_error
    end.

  Lemma to_boolI x b : to_bool x = ok b → x = b.
  Proof. by case: x => //= => [? [->] | []]. Qed.

  Lemma to_bool_undef v : to_bool v = undef_error -> v = undef_b.
  Proof. by case: v => //= - [] // e; rewrite (Eqdep_dec.UIP_refl_bool _ e). Qed.

  Definition to_int v :=
    match v with
    | Vint i => ok i
    | Vundef sint _ => undef_error
    | _ => type_error
    end.

  Lemma to_intI v n: to_int v = ok n → v = n.
  Proof. by case: v => //= [? [<-] | [] ]. Qed.

  Lemma to_int_undef v : to_int v = undef_error -> v = undef_i.
  Proof. by case: v => //= -[] // e; rewrite (Eqdep_dec.UIP_refl_bool _ e). Qed.

  Definition to_arr len v : exec (sem_t (sarr len)) :=
    match v with
    | Varr len' t => WArray.cast len t
    | _ => type_error
    end.

  Lemma to_arrI n v t : to_arr n v = ok t -> v = Varr t.
  Proof. 
    case: v => //= n' t' /[dup] /WArray.cast_len ?; subst n'.
    by rewrite WArray.castK => -[<-].
  Qed.

  Lemma to_arr_undef p v : to_arr p v <> undef_error.
  Proof. by case: v => //= ??; rewrite /WArray.cast; case: ifP. Qed.

  Definition to_word s v : exec (word s) :=
    match v with
    | Vword s' w => truncate_word s w
    | Vundef (sword s') _ => undef_error
    | _ => type_error
    end.

  Notation to_pointer := (to_word Uptr).

  Lemma to_wordI sz v w : to_word sz v = ok w ->
    exists sz' (w': word sz'), v = Vword w' /\ truncate_word sz w' = ok w.
  Proof. by case: v => //=; eauto; case => //. Qed.

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

  Definition cast_abstract s s' (a: iabstract s') : exec (iabstract s) :=
    match gcmp s s' as c return gcmp s s' = c → exec (iabstract s) with
    | Eq => λ h, ok (ecast s (iabstract s) (esym (cmp_eq h)) a)
    | Lt => λ _, type_error
    | Gt => λ _, type_error
    end erefl.

  Variant cast_abstract_spec s s' (a: iabstract s') : exec (iabstract s) → Type :=
    | CastAbstractEq (h: s' = s) : cast_abstract_spec a (ok (ecast s (iabstract s) h a))
    | CastAbstractLt : (s < s')%CMP -> cast_abstract_spec a type_error
    | CastAbstractGt : (s' < s)%CMP → cast_abstract_spec a type_error
  .

  Lemma cast_abstractP' s s' (a: iabstract s') : cast_abstract_spec a (cast_abstract s a).
  Proof.
    rewrite /cast_abstract/gcmp.
    case: {2 3} (string_cmp s s') erefl.
    - move => /cmp_eq ?; exact: CastAbstractEq.
    - move => h; apply: CastAbstractLt.
      by rewrite /cmp_lt /gcmp h.
      rewrite -/(gcmp s s') => h.
      apply: CastAbstractGt.
      by rewrite /cmp_lt cmp_sym h.
  Qed.

  Lemma cast_abstractP s1 s2 (a1:iabstract s1) (a2:iabstract s2) :
    cast_abstract s1 a2 = ok a1 → (s1 = s2)%CMP /\ JMeq a1 a2.
  Proof.
    case: cast_abstractP' => //=.
    by move => ? ; subst => /ok_inj ?;subst.
  Qed.

  Lemma cast_abstract_errP s1 s2 (a: iabstract s2) e :
    cast_abstract s1 a = Error e → e = ErrType.
  Proof.  by case: cast_abstractP' => //= ? [] <-. Qed.

  Definition cast_abstract_u s  (a : iabstract s):
    cast_abstract s a = ok a.
  Proof.
    case: cast_abstractP' => //.
    - move => h.
      rewrite (Eqdep_dec.UIP_dec string_eq_dec h erefl).
      reflexivity.
    - rewrite -cmp_nle_lt => /negbTE.
      specialize (cmp_le_refl s).
      intros H h.
      rewrite h in H.
      inversion H.
    - rewrite -cmp_nle_lt => /negbTE.
      specialize (cmp_le_refl s).
      intros H h.
      rewrite h in H.
      inversion H.
  Qed.

  Definition to_abstract s v : exec (iabstract s) :=
    match v with
    | Vabstract s' a => cast_abstract s a
    | Vundef (sabstract s') _ => if s == s' then undef_error else type_error
    | _ => type_error
    end.

  Lemma to_abstractI s v a : to_abstract s v = ok a ->
    exists s' (a': iabstract s'), v = Vabstract a' /\ cast_abstract s a' = ok a.
  Proof. case: v => //=; eauto; case => //= ??.
         by case : eqP.
  Qed.

  Lemma to_abstract_undef s v :
    to_abstract s v = undef_error -> v = undef_a s.
  Proof.
    case: v => //= [> /cast_abstract_errP |] // t i; rewrite undef_x_vundef.
    case: t i  => //= ? ?.
    by case : eqP => // ->.
  Qed.

  Lemma cast_abstract_uincl s1 s2 a1 (a2: iabstract s2) :
    cast_abstract s1 a2 = ok a1 → abstract_uincl a1 a2.
  Proof. move=> /cast_abstractP  ?.
         exact: abstract_uinclude_ext.
  Qed.

  Lemma abstract_uincl_cast s1 (a1: iabstract s1) s2 (a2: iabstract s2) s a:
    abstract_uincl a1 a2 -> cast_abstract s a1 = ok a -> cast_abstract s a2 = ok a.
  Proof.
    move => /ext_abstract_uinclude [?] ?.
    by subst.
  Qed.

  (* ----------------------------------------------------------------------- *)

  Definition of_val t : value -> exec (sem_t t) :=
    match t return value -> exec (sem_t t) with
    | sbool => to_bool
    | sint => to_int
    | sarr n => to_arr n
    | sword s => to_word s
    | sabstract s => to_abstract s
    end.

  Lemma of_val_typeE t v v' : of_val t v = ok v' ->
    match t, v' with
    | sarr len, vt => v = Varr vt
    | sword ws, vt => exists ws' (w: word ws'),
        v = Vword w /\ truncate_word ws w = ok vt
    | sbool, vt => v = vt
    | sint, vt => v = vt
    | sabstract s, vt => exists s' (a: iabstract s'),
        v = Vabstract a /\ cast_abstract s a = ok vt
    end.
  Proof.
    case: t v' => /= >.
    + exact: to_boolI.
    + exact: to_intI.
    + exact: to_arrI.
    + exact: to_wordI.
      exact :to_abstractI.
  Qed.

  Lemma of_valE t v v' : of_val t v = ok v' ->
    match v with
    | Vbool b => exists h: t = sbool, eq_rect _ _ v' _ h = b
    | Vint i => exists h: t = sint, eq_rect _ _ v' _ h = i
    | Varr len a => exists (h: t = sarr len), eq_rect _ _ v' _ h = a
    | Vword ws w => exists ws' (h: t = sword ws') w',
        truncate_word ws' w = ok w' /\ eq_rect _ _ v' _ h = w'
    | Vabstract s a => exists s' (h: t = sabstract s') a',
        cast_abstract s' a = ok a' /\ eq_rect _ _ v' _ h = a'
    | Vundef t h => False
    end.
  Proof.
    by case: t v' => > /of_val_typeE; try (simpl=> ->; exists erefl; eauto);
                    simpl=> > [? [? [-> ]]]; eexists; exists erefl; eauto.
  Qed.

  Lemma of_val_subtype t v sv : of_val t v = ok sv -> subtype t (type_of_val v).
  Proof.
    case: t sv => > /of_val_typeE; try by move=> ->.
    + by case=> ? [? [-> /truncate_wordP[]]].
      by case=> ? [? [-> /cast_abstractP [?] ?]]; subst.
  Qed.

  Lemma of_value_uincl ty v v' vt :
    value_uincl v v' -> of_val ty v = ok vt ->
    match v' with
    | Varr len a => exists (h: ty = sarr len), WArray.uincl (eq_rect _ _ vt _ h) a
    | _ => of_val ty v' = ok vt
    end.
  Proof.
    case: v => > /value_uinclE + /of_valE //;
                                  try (by move=> -> [? ]; subst=> /= ->).
    + by move=> [t2 ->] h [?]; subst => /= ->; exists erefl.
                                             + move=> [sz2 [w2 [-> h]]] [ws' [? [w' []]]]; subst => /= h1 ->.
                                               exact: word_uincl_truncate h1.
                                               move=> [s2 [a2 [-> h]]] [s' [? [w' []]]] ; subst => /= h1 ->.
                                               exact: abstract_uincl_cast h1.
  Qed.

  (* can be use to shorten proofs drastically, see psem/vuincl_sem_sop1 *)
  Lemma of_value_uincl_te ty v v' vt :
    value_uincl v v' -> of_val ty v = ok vt ->
    match ty as ty return sem_t ty -> Prop with
    | sarr n => fun vt =>
                 exists2 vt', of_val (sarr n) v' = ok vt' & WArray.uincl vt vt'
    | _ => fun _ => of_val ty v' = ok vt
    end vt.
  Proof.
    case: v => > /value_uinclE + /of_valE //; try (by move=> -> [? ]; subst=> /= ->).
    + by move: vt => + [? -> +] [?] => vt ??; subst => /=; rewrite WArray.castK; eauto.
    + move: vt => + [? [? [-> +]]] [? [? [? []]]]; subst=> /= _ ++ ->.
      exact: word_uincl_truncate.
      move: vt => + [? [? [-> +]]] [? [? [? []]]]; subst=> /= _ ++ ->.
      exact: abstract_uincl_cast.
  Qed.

  (* ----------------------------------------------------------------------- *)

  Definition to_val t : sem_t t -> value :=
    match t return sem_t t -> value with
    | sbool => Vbool
    | sint => Vint
    | sarr n  => @Varr n
    | sword s => @Vword s
    | sabstract s => @Vabstract s
    end.

  Lemma to_val_inj t (v1 v2: sem_t t) : to_val v1 = to_val v2 -> v1 = v2.
  Proof. by case: t v1 v2 => /= > => [[]|[]| /Varr_inj1 |[]| /Vabstract_inj1]. Qed.

  Lemma of_val_to_val t (v : sem_t t) : of_val t (to_val v) = ok v.
  Proof.
    case: t v => //=.
    + by move=> len a; rewrite WArray.castK.
    + by move=> ws w; rewrite truncate_word_u.
    by move=> s v; rewrite cast_abstract_u.
  Qed.

  Lemma to_valI t (x: sem_t t) v : to_val x = v ->
    match v with
    | Vbool b => exists h: t = sbool, eq_rect _ _ x _ h = b
    | Vint i => exists h: t = sint, eq_rect _ _ x _ h = i
    | Varr len a => exists h: t = sarr len, eq_rect _ _ x _ h = a
    | Vword ws w => exists h: t = sword ws, eq_rect _ _ x _ h = w
    | Vabstract s a => exists h: t = sabstract s, eq_rect _ _ x _ h = a
    | Vundef _ _ => False
    end.
  Proof. by case: t x => /= > <-; exists erefl. Qed.

  Lemma type_of_to_val t (s: sem_t t) : type_of_val (to_val s) = t.
  Proof. by case: t s. Qed.

  Definition oto_val t : sem_ot t -> value :=
    match t return sem_ot t -> value with
    | sbool => fun ob => if ob is Some b then Vbool b else undef_b
    | x => @to_val x
    end.

  Lemma type_of_oto_val t (s: sem_ot t) : type_of_val (oto_val s) = t.
  Proof. by case: t s => //= -[]. Qed.

  Definition val_uincl (t1 t2:stype) (v1:sem_t t1) (v2:sem_t t2) :=
    value_uincl (to_val v1) (to_val v2).

  Lemma val_uincl_alt t1 t2 : @val_uincl t1 t2 =
    match t1, t2 return sem_t t1 -> sem_t t2 -> Prop with
    | sarr _, sarr _ => WArray.uincl
    | sword s1, sword s2 => @word_uincl s1 s2
    | sabstract s1, sabstract s2 => @abstract_uincl s1 s2
    | t1', t2' => if boolP (t1' == t2') is AltTrue h
                 then eq_rect _ (fun x => sem_t t1' -> sem_t x -> Prop) eq _ (eqP h)
                 else fun _ _ => False
    end.
  Proof.
    by case: t1; case: t2 => >; rewrite /val_uincl //=;
       case: {-}_/ boolP => // h >;
       rewrite (Eqdep_dec.UIP_dec stype_eq_dec (eqP h)).
  Qed.

  Lemma val_uinclEl t1 t2 v1 v2 :
    val_uincl v1 v2 ->
    match t1 return sem_t t1 -> sem_t t2 -> Prop with
    | sarr len => fun v1 v2 => exists (h: t2 = sarr len),
                     WArray.uincl v1 (eq_rect _ _ v2 _ h)
    | sword ws => fun v1 v2 => exists ws' (h: t2 = sword ws'),
                     word_uincl v1 (eq_rect _ _ v2 _ h)
    | sabstract s => fun v1 v2 => exists s' (h: t2 = sabstract s'),
                        abstract_uincl v1 (eq_rect _ _ v2 _ h)
    | t => fun v1 v2 => exists h: t2 = t, v1 = eq_rect _ _ v2 _ h
    end v1 v2.
  Proof.
    case: t1 v1 => /=; case: t2 v2 => //=; try (exists erefl; done);
                                    rewrite /val_uincl /=.
    + by move=> > /[dup] /WArray.uincl_len ? ?; subst; exists erefl.
    + by eexists; exists erefl.
      by eexists; exists erefl.
  Qed.

  Lemma val_uinclE t1 t2 v1 v2 :
    val_uincl v1 v2 ->
    match t2 return sem_t t1 -> sem_t t2 -> Prop with
    | sarr len => fun v1 v2 => exists (h: t1 = sarr len),
                     WArray.uincl (eq_rect _ _ v1 _ h) v2
    | sword ws => fun v1 v2 => exists ws' (h: t1 = sword ws'),
                     word_uincl (eq_rect _ _ v1 _ h) v2
    | sabstract s => fun v1 v2 => exists s' (h: t1 = sabstract s'),
                        abstract_uincl (eq_rect _ _ v1 _ h) v2
    | t => fun v1 v2 => exists h: t1 = t, v2 = eq_rect _ _ v1 _ h
    end v1 v2.
  Proof.
    case: t1 v1 => /=; case: t2 v2 => //=; try (exists erefl; done);
                                    rewrite /val_uincl /=.
    + by move=> > /[dup] /WArray.uincl_len ? ?; subst; exists erefl.
    + by eexists; exists erefl.
      by eexists; exists erefl.
  Qed.

  Lemma val_uincl_refl t v: @val_uincl t t v v.
  Proof. by rewrite /val_uincl. Qed.

  Hint Resolve val_uincl_refl : core.

  Lemma val_uincl_of_val ty v v' vt :
    value_uincl v v' -> of_val ty v = ok vt ->
    exists2 vt', of_val ty v' = ok vt' & val_uincl vt vt'.
  Proof.
    case: v => > /value_uinclE + /of_valE //;
                                  try (by move=> -> [? ]; subst => /= ->; eauto).
    + by move=> [???] [??]; subst => /=; rewrite WArray.castK; eauto.
    + move: vt => + [? [? [-> +]]] [s [x [? []]]]; subst=> /= _ ++ ->.
      move=> /word_uincl_truncate h/h{h} ->; eauto.
      move: vt => + [? [? [-> +]]] [s [x [? []]]]; subst=> /= _ ++ ->.
      move=> /abstract_uincl_cast h/h{h} ->; eauto.
  Qed.

  Lemma value_uincl_defined wdb v1 v2 :
    value_uincl v1 v2 -> wdb || is_defined v1 -> wdb || is_defined v2.
  Proof.
    case: wdb => //=.
    case: v1 => [b | z| len t| ws w | t i| t i] /value_uinclE //; try by move=> ->.
    + by move=> [? ->].
    + by move=> [? [? [-> _]]].
      by move=> [? [? [-> _]]].
  Qed.

  Lemma value_uincl_DB wdb v1 v2 :
    value_uincl v1 v2 -> DB wdb v1 -> DB wdb v2.
  Proof.
    case: wdb => //.
    case: v1 => [b | z| len t| ws w | t i | t i] /value_uinclE; try by move=> ->.
    + by move=> [? ->]. + by move=> [? [? [-> _]]]. + by move=> [? [? [-> _]]].
                                                  by rewrite /DB => /= + /eqP ?; subst t => /eqP <-; rewrite eqxx orbT.
  Qed.

  (* ** Values implicit downcast (upcast is explicit because of signedness)
   * -------------------------------------------------------------------- *)

  Definition truncate_val (ty: stype) (v: value) : exec value :=
    of_val ty v >>= λ x, ok (to_val x).

  Lemma truncate_val_typeE ty v vt :
    truncate_val ty v = ok vt ->
    match ty with
    | sbool => exists2 b: bool, v = b & vt = b
    | sint => exists2 i: Z, v = i & vt = i
    | sarr len => exists2 a : WArray.array len, v = Varr a & vt = Varr a
    | sword ws => exists w ws' (w': word ws'),
        [/\ truncate_word ws w' = ok w, v = Vword w' & vt = Vword w]
    | sabstract s => exists a s' (a': iabstract s'),
        [/\ cast_abstract s a' = ok a, v = Vabstract a' & vt = Vabstract a]
    end.
  Proof.
    rewrite /truncate_val; t_xrbindP; case: v => > /of_valE; case=> ?;
                                                                    try (by subst=> /= -> <-; eauto); case=> ? [? []]; subst=> /= hv -> <-.
    + by eexists; eexists; eexists; constructor; auto.
      by eexists; eexists; eexists; constructor; auto.
  Qed.

  Lemma truncate_valE ty v vt :
    truncate_val ty v = ok vt ->
    match v with
    | Vbool b => ty = sbool /\ vt = b
    | Vint i => ty = sint /\ vt = i
    | Varr len a => ty = sarr len /\ vt = Varr a
    | Vword ws w => exists ws' w',
        [/\ ty = sword ws', truncate_word ws' w = ok w' & vt = Vword w']
    | Vabstract s a => exists s' a',
        [/\ ty = sabstract s', cast_abstract s' a = ok a' & vt = Vabstract a']
    | Vundef _ _ => False
    end.
  Proof.
    case: ty => > /truncate_val_typeE
        => [ [] | [] | [] | [? [? [? []]]] | [? [? [? []]]] ] ? -> -> //.
    + by eexists; eexists; split; auto.
      by eexists; eexists; split; auto.
  Qed.

  Lemma truncate_valI ty v vt :
    truncate_val ty v = ok vt ->
    match vt with
    | Vbool b => ty = sbool /\ v = b
    | Vint i => ty = sint /\ v = i
    | Varr len a => ty = sarr len /\ v = Varr a
    | Vword ws w => exists ws' (w': word ws'),
        [/\ ty = sword ws, truncate_word ws w' = ok w & v = Vword w']
    | Vabstract s a => exists s' (a': iabstract s'),
        [/\ ty = sabstract s, cast_abstract s a' = ok a & v = Vabstract a']
    | Vundef _ _ => False
    end.
  Proof.
    by case: ty => > /truncate_val_typeE
    => [ [] | [] | [] | [? [? [? []]]] | [? [? [? []]]]] ? -> -> //;
                                                                eexists; eexists; split; auto.
  Qed.

  Lemma truncate_val_subtype ty v v' :
    truncate_val ty v = ok v' →
    subtype ty (type_of_val v).
  Proof.
    case: v => > /truncate_valE
        => [ [] | [] | [] | [?[?[+/truncate_wordP[??]]]] | [s[?[+/cast_abstractP [h] _ _]]] | //] => -> //=.
    rewrite <- h.
    by case s.
  Qed.

  Lemma truncate_val_has_type ty v v' :
    truncate_val ty v = ok v' →
    type_of_val v' = ty.
  Proof.
    by case: v' => > /truncate_valI
    => [[]|[]|[]|[?[?[+/truncate_wordP[??]]]]| [?[?[+/cast_abstractP[??]]]]|//]
    => ->.
  Qed.

  Lemma truncate_val_subtype_eq ty v v' :
    truncate_val ty v = ok v' ->
    subtype (type_of_val v) ty ->
    v = v'.
  Proof.
    move=> /truncate_valE; case: v => [b | z | len a | ws w | s a | //]; try by move=> [_ ->].
    + move=> [ws' [w' [-> /truncate_wordP [h ->]->]]] /= /(cmp_le_antisym h) ?; subst ws'.
      by rewrite zero_extend_u.
      by move=> [s' [a' [-> /cast_abstractP [h] h1 h2 _]]] /=;subst.
  Qed.

  Lemma truncate_val_idem (t : stype) (v v' : value) :
    truncate_val t v = ok v' -> truncate_val t v' = ok v'.
  Proof.
    move=> /truncate_valI; case: v' => [b[]|z[]|len a[]|ws w[?[?[]]]| s a [? [? []]]|] //= -> //=.
    + by move=> _; rewrite /truncate_val /= WArray.castK.
    + by move=> _ _; rewrite /truncate_val /= truncate_word_u.
      by move=> _ _; rewrite /truncate_val /= cast_abstract_u.
  Qed.

  Lemma subtype_truncate_val_idem ty1 ty2 v v1 v2 :
    subtype ty2 ty1 ->
    truncate_val ty1 v = ok v1 ->
    truncate_val ty2 v1 = ok v2 ->
    truncate_val ty2 v = ok v2.
  Proof.
    move=> /subtypeE hsub /truncate_valE htr.
    case: v htr hsub => //.
    + by move=> b [-> ->] _.
    + by move=> z [-> ->] _.
    + by move=> len a [-> ->] _.
    + move=> ws w [ws1 [w1 [-> /truncate_wordP [hcmp1 ->] ->]]] [ws2 [-> hcmp2]].
      rewrite /truncate_val /= truncate_word_le //= => -[<-].
      rewrite truncate_word_le /=; last by apply (cmp_le_trans hcmp2 hcmp1).
      by rewrite zero_extend_idem.
    move=> s ? [? [? [-> /cast_abstractP[h1 h2] -> ->]]] /=.
    by subst s; have -> := JMeq_eq h2.
  Qed.

  Lemma subtype_truncate_val ty1 ty2 v v1 :
    subtype ty2 ty1 ->
    truncate_val ty1 v = ok v1 ->
    exists v2, truncate_val ty2 v1 = ok v2.
  Proof.
    move=> /subtypeE hsub /truncate_valI htr.
    case: v1 htr hsub => //.
    + by move=> b [-> _] ->; eexists; reflexivity.
    + by move=> z [-> _] ->; eexists; reflexivity.
    + move=> len a [-> _] ->.
      by rewrite /truncate_val /= WArray.castK; eexists; reflexivity.
    + move=> ws1 w1 [_ [_ [-> _ _]]] [ws2 [-> hcmp2]].
      rewrite /truncate_val /= truncate_word_le //.
      by eexists; reflexivity.
    move=> s ? [? [? [-> /cast_abstractP[h1 h2] h3 h4]]] /=.
    subst s v ty2; have -> := JMeq_eq h2.
    rewrite /truncate_val /= cast_abstract_u /=; eexists; eauto.
  Qed.

  Lemma truncate_val_defined ty v v' : truncate_val ty v = ok v' -> is_defined v'.
  Proof. by move=> /truncate_valI; case: v'. Qed.

  Lemma truncate_val_DB wdb ty v v' : truncate_val ty v = ok v' -> DB wdb v'.
  Proof. by case: wdb => //; move=> /truncate_valI; case: v'. Qed.

  (* ----------------------------------------------------------------------- *)

  Lemma value_uincl_truncate ty x y x' :
    value_uincl x y →
    truncate_val ty x = ok x' →
    exists2 y', truncate_val ty y = ok y' & value_uincl x' y'.
  Proof.
    case: x => > /value_uinclE+ /truncate_valE => [ + []  | + []
                                                | [? + ? []]
                                                | [? [? [+ /word_uincl_truncate h]]] [? [? [+ /h{h} h]]]
                                                | [? [? [+ /abstract_uincl_cast h]]] [? [? [+ /h{h} h]]]
                                                    |// ]
        => -> -> ->.
    1,2: by eexists.
    + by rewrite /truncate_val /= WArray.castK /=; eexists.
    + by rewrite /truncate_val /= h /=; eexists=> // /=.
      by rewrite /truncate_val /= h /=; eexists=> // /=.
  Qed.

  Lemma truncate_value_uincl t v1 v2 : truncate_val t v1 = ok v2 -> value_uincl v2 v1.
  Proof.
    rewrite /truncate_val; case: t; t_xrbindP=> > /=.
    + by move=> /to_boolI -> <-.
    + by move=> /to_intI -> <-.
    + by move=> /to_arrI -> <-.
    + by move=> /to_wordI [? [? [-> ? <-]]] /=; exact: truncate_word_uincl.
      by move=> /to_abstractI [? [? [-> ? <-]]] /=; exact: cast_abstract_uincl.
  Qed.

  Lemma mapM2_truncate_value_uincl tyin vargs1 vargs1' :
    mapM2 ErrType truncate_val tyin vargs1 = ok vargs1' ->
    List.Forall2 value_uincl vargs1' vargs1.
  Proof.
    move=> htr.
    have {htr} := mapM2_Forall3 htr.
    elim {vargs1 vargs1'} => //.
    move=> _ v1 v1' _ vargs1 vargs1' /truncate_value_uincl huincl _ ih.
    by constructor.
  Qed.

  Lemma mapM2_truncate_val tys vs1' vs1 vs2' :
    mapM2 ErrType truncate_val tys vs1' = ok vs1 ->
    List.Forall2 value_uincl vs1' vs2' ->
    exists2 vs2, mapM2 ErrType truncate_val tys vs2' = ok vs2 &
                   List.Forall2 value_uincl vs1 vs2.
  Proof.
    elim: tys vs1' vs1 vs2' => [ | t tys hrec] [|v1' vs1'] //=.
    + by move => ? ? [<-] /List_Forall2_inv_l ->; eauto.
      move=> vs1 vs2';t_xrbindP => v1 htr vs2 htrs <- /List_Forall2_inv_l [v] [vs] [->] [hv hvs].
      have [v2 -> hv2 /=]:= value_uincl_truncate hv htr.
      by have [vs2'' -> hvs2 /=] := hrec _ _ _ htrs hvs;eauto.
  Qed.

  (* ----------------------------------------------------------------------- *)

  Fixpoint list_ltuple (ts:list stype) : sem_tuple ts -> values :=
    match ts return sem_tuple ts -> values with
    | [::] => fun (u:unit) => [::]
    | t :: ts =>
        let rec := @list_ltuple ts in
        match ts return (sem_tuple ts -> values) -> sem_tuple (t::ts) -> values with
        | [::] => fun _ x => [:: oto_val x]
        | t1 :: ts' =>
            fun rec (p : sem_ot t * sem_tuple (t1 :: ts')) =>
              oto_val p.1 :: rec p.2
        end rec
    end.

  Lemma type_of_val_ltuple tout (p : sem_tuple tout) :
    List.map type_of_val (list_ltuple p) = tout.
  Proof.
    elim: tout p => //= t1 [|t2 tout] /=.
    + by rewrite /sem_tuple /= => _ x;rewrite type_of_oto_val.
      by move=> hrec [] x xs /=; rewrite type_of_oto_val hrec.
  Qed.

  (* ----------------------------------------------------------------------- *)

  Definition app_sopn := app_sopn of_val.

  Arguments app_sopn {A} ts _ _.

  Definition app_sopn_v tin tout (semi: sem_prod tin (exec (sem_tuple tout))) vs :=
    Let t := app_sopn _ semi vs in
        ok (list_ltuple t).

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
    move=> htr.
    elim: {l vargs vargs' htr} (mapM2_Forall3 htr) f => //=.
    move=> ty v v' tys vargs vargs' htr _ ih f.
    t_xrbindP=> w' ok_w' ok_t.
    move: htr => /[dup] /truncate_val_idem.
    rewrite /truncate_val ok_w' /=.
    t_xrbindP=> <- _ -> /to_val_inj -> /=.
    by apply ih.
  Qed.

  Lemma vuincl_sopn T ts o vs vs' (v: T) :
    all is_not_sarr ts -> List.Forall2 value_uincl vs vs' ->
    app_sopn ts o vs = ok v -> app_sopn ts o vs' = ok v.
  Proof.
    elim: ts o vs vs' => /= [ | t ts Hrec] o [] //.
    + by move => vs' _ /List_Forall2_inv_l -> ->; eauto using List_Forall2_refl.
      move => n vs vs'' /andP [] ht hts /List_Forall2_inv_l [v'] [vs'] [->] {vs''} [/value_uinclE hv hvs].
      t_xrbindP; case: t o ht => [ | | // | sz | sz] o _ + /of_val_typeE;
                                try by simpl=> ??; subst; subst=> /(Hrec _ _ _ hts hvs).
    + simpl=> ? [? [? [? /word_uincl_truncate h]]]; subst.
      by move: hv => [? [? [? /h]]]; subst => /= -> /(Hrec _ _ _ hts hvs).
      simpl=> ? [? [? [? /abstract_uincl_cast h]]]; subst.
      by move: hv => [? [? [? /h]]]; subst => /= -> /(Hrec _ _ _ hts hvs).
  Qed.

  Lemma vuincl_app_sopn_v_eq tin tout (semi: sem_prod tin (exec (sem_tuple tout))) :
    all is_not_sarr tin -> forall vs vs' v, List.Forall2 value_uincl vs vs' ->
                                      app_sopn_v semi vs = ok v -> app_sopn_v semi vs' = ok v.
  Proof.
    rewrite /app_sopn_v => hall vs vs' v hu; t_xrbindP => v' h1 h2.
    by rewrite (vuincl_sopn hall hu h1) /= h2.
  Qed.

  Lemma vuincl_copy_eq ws p :
    let sz := Z.to_pos (arr_size ws p) in
    forall vs vs' v,
      List.Forall2 value_uincl vs vs' ->
      @app_sopn_v [::sarr sz] [::sarr sz] (@WArray.copy ws p) vs = ok v ->
      @app_sopn_v [::sarr sz] [::sarr sz] (@WArray.copy ws p) vs' = ok v.
  Proof.
    move=> sz _ _ v [// | v1 v2 [_ /value_uinclE hu /List_Forall2_inv_l -> |]];
          rewrite /app_sopn_v /=; t_xrbindP=> // ??.
    move: hu => + /to_arrI ? /WArray.uincl_copy H ?; subst.
    by move=> /=[? -> /H h] /=; rewrite WArray.castK /= h.
  Qed.

  Lemma vuincl_app_sopn_v tin tout (semi: sem_prod tin (exec (sem_tuple tout))) :
    all is_not_sarr tin ->
    forall vs vs' v, List.Forall2 value_uincl vs vs' ->
                app_sopn_v semi vs = ok v ->
                exists2 v' : values, app_sopn_v semi vs' = ok v' & List.Forall2 value_uincl v v'.
  Proof.
    move=> /vuincl_app_sopn_v_eq h ?? v /h{h}h/h{h}?.
    by exists v => //; exact: List_Forall2_refl.
  Qed.

  Lemma vuincl_copy ws p :
    let sz := Z.to_pos (arr_size ws p) in
    forall vs vs' v,
      List.Forall2 value_uincl vs vs' ->
      @app_sopn_v [::sarr sz] [::sarr sz] (@WArray.copy ws p) vs = ok v ->
      exists2 v' : values, @app_sopn_v [::sarr sz] [::sarr sz] (@WArray.copy ws p) vs' = ok v' & List.Forall2 value_uincl v v'.
  Proof.
    move=> ??? v /vuincl_copy_eq h/h{h}?.
    by exists v => //; exact: List_Forall2_refl.
  Qed.

  Lemma value_uincl_oto_val ty (z z' : sem_t ty) :
    val_uincl z z' ->
    value_uincl (oto_val (sem_prod_id z)) (oto_val (sem_prod_id z')).
  Proof. by case: ty z z'. Qed.

  Definition swap_semi ty (x y: sem_t ty) : exec (sem_tuple [:: ty; ty]):= ok (sem_prod_id y, sem_prod_id x).

  Lemma swap_semu ty (vs vs' : seq value) (v : values):
    List.Forall2 value_uincl vs vs' ->
    @app_sopn_v [::ty; ty] [::ty; ty] (@swap_semi ty) vs = ok v ->
    exists2 v' : values, @app_sopn_v [::ty; ty] [::ty; ty] (@swap_semi ty) vs' = ok v' & List.Forall2 value_uincl v v'.
  Proof.
    rewrite /app_sopn_v.
    case => //= v1 v1' ?? hu1; t_xrbindP.
    case => //= v2 v2' ?? hu2; t_xrbindP.
    case => // _ z1 hv1 z2 hv2 [] <- <- /=.
    have [z1' -> hu1']:= val_uincl_of_val hu1 hv1.
    have [z2' -> hu2' /=]:= val_uincl_of_val hu2 hv2.
    eexists; first by eauto.
    by repeat constructor;  apply: value_uincl_oto_val.
  Qed.

  Section FORALL.
    Context  (T:Type) (P:T -> Prop).

    Fixpoint mk_forall (l:seq stype) : sem_prod l (exec T) -> Prop :=
      match l as l0 return sem_prod l0 (exec T) -> Prop with
      | [::] => fun o => forall t, o = ok t -> P t
      | t::l => fun o => forall (x:sem_t t), @mk_forall l (o x)
      end.

    Lemma mk_forallP l f vargs t : @mk_forall l f -> app_sopn l f vargs = ok t -> P t.
    Proof.
      elim: l vargs f => [ | a l hrec] [ | v vs] //= f hall; first by apply hall.
      by t_xrbindP => w _;apply: hrec.
    Qed.

    Context (P2:T -> T -> Prop).

    Fixpoint mk_forall_ex (l:seq stype) : sem_prod l (exec T) -> sem_prod l (exec T) -> Prop :=
      match l as l0 return sem_prod l0 (exec T) -> sem_prod l0 (exec T) -> Prop with
      | [::] => fun o1 o2 => forall t, o1 = ok t -> exists2 t', o2 = ok t' & P2 t t'
  | t::l => fun o1 o2 => forall (x:sem_t t), @mk_forall_ex l (o1 x) (o2 x)
    end.

    Lemma mk_forall_exP l f1 f2 vargs t : @mk_forall_ex l f1 f2 -> app_sopn l f1 vargs = ok t ->
                                          exists2 t', app_sopn l f2 vargs = ok t' & P2 t t'.
    Proof.
      elim: l vargs f1 f2 => [ | a l hrec] [ | v vs] //= f1 f2 hall; first by apply hall.
      by t_xrbindP => w ->; apply/hrec.
    Qed.

    Fixpoint mk_forall2 (l:seq stype) : sem_prod l (exec T) -> sem_prod l (exec T) -> Prop :=
      match l as l0 return sem_prod l0 (exec T) -> sem_prod l0 (exec T) -> Prop with
      | [::] => fun o1 o2 => forall t1 t2, o1 = ok t1 -> o2 = ok t2 -> P2 t1 t2
      | t::l => fun o1 o2 => forall (x:sem_t t), @mk_forall2 l (o1 x) (o2 x)
      end.

    Lemma mk_forall2P l f1 f2 vargs t1 t2 : @mk_forall2 l f1 f2 -> app_sopn l f1 vargs = ok t1 -> app_sopn l f2 vargs = ok t2 -> P2 t1 t2.
    Proof.
      elim: l vargs f1 f2 => [ | a l hrec] [ | v vs] //= f1 f2 hall; first by apply hall.
      by t_xrbindP => w -> happ1 ? [<-]; apply: hrec happ1.
    Qed.

  End FORALL.
End VALUE.

Arguments Vundef {tabstract}.
Notation to_pointer := (to_word Uptr).
Notation undef_b := (@Vundef _ sbool erefl).
Notation undef_i := (@Vundef _ sint erefl).
Notation undef_w := (@Vundef _ sword8 erefl).
Notation undef_a s := (@Vundef _ (sabstract s) erefl).

#[global]
  Hint Resolve abstract_uincl_refl : core.
#[global]
  Hint Resolve value_uincl_refl : core.
#[global]
  Hint Resolve val_uincl_refl : core.
