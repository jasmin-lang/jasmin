(* * Syntax and semantics of the Jasmin source language *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Psatz xseq.
Require Export array gen_map low_memory warray_ sem_type.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* ** Values
  * -------------------------------------------------------------------- *)

Variant value : Type :=
  | Vbool  :> bool -> value
  | Vint   :> Z    -> value
  | Varr   : forall len, WArray.array len -> value
  | Vword  : forall s, word s -> value
  | Vundef : forall (t:stype), is_sarr t = false -> value.
Arguments Vundef _ _ : clear implicits.

Definition undef_b := Vundef sbool erefl.
Definition undef_i := Vundef sint erefl.
Definition undef_w ws := Vundef (sword ws) erefl.

Definition values := seq value.

Definition is_word (sz: wsize) (v: value) : exec unit :=
  match v with
  | Vword _ _ | Vundef (sword _) _ => ok tt
  | _ => type_error end.

Definition is_defined (v: value) : bool :=
  if v is Vundef _ _ then false else true.

Definition Varr_inj n n' t t' (e: @Varr n t = @Varr n' t') :
  ∃ (en: n = n'),
      eq_rect n (λ s, WArray.array s) t n' en = t' :=
  let 'Logic.eq_refl := e in
    (ex_intro _ erefl erefl).

Lemma Varr_inj1 n t t' : @Varr n t = @Varr n t' -> t = t'.
Proof.
  by move => /Varr_inj [en ]; rewrite (Eqdep_dec.UIP_dec Pos.eq_dec en erefl).
Qed.

Definition Vword_inj sz sz' w w' (e: @Vword sz w = @Vword sz' w') :
  ∃ e : sz = sz', eq_rect sz (λ s, (word s)) w sz' e = w' :=
  let 'Logic.eq_refl := e in (ex_intro _ erefl erefl).

(* ----------------------------------------------------------------------- *)

Definition to_bool v :=
  match v with
  | Vbool b        => ok b
  | Vundef sbool _ => undef_error
  | _              => type_error
  end.

Lemma to_boolI x b : to_bool x = ok b → x = b.
Proof. by case: x => //=; [move=> ? [->] | case]. Qed.

Lemma to_bool_undef v : to_bool v = undef_error -> v = undef_b.
Proof. by case: v => //= -[] // e _; rewrite (Eqdep_dec.UIP_refl_bool _ e). Qed.

Definition to_int v :=
  match v with
  | Vint z        => ok z
  | Vundef sint _ => undef_error
  | _             => type_error
  end.

Lemma to_intI v n: to_int v = ok n → v = n.
Proof. by case: v => //= [? [<-] | [] ]. Qed.

Lemma to_int_undef v : to_int v = undef_error -> v = undef_i.
Proof. by case: v => //= -[] // e _; rewrite (Eqdep_dec.UIP_refl_bool _ e). Qed.

Definition truncate_word (s s':wsize) (w:word s') : exec (word s) :=
   if (s <= s')%CMP then ok (zero_extend s w) else type_error.

Lemma truncate_word_u s (a : word s): truncate_word s a = ok a.
Proof. by rewrite /truncate_word cmp_le_refl zero_extend_u. Qed.

Lemma truncate_wordP s1 s2 (w1:word s1) (w2:word s2) :
  truncate_word s1 w2 = ok w1 → (s1 <= s2)%CMP /\ w1 = zero_extend s1 w2.
Proof. by rewrite /truncate_word; case: ifP => // ? []. Qed.

Lemma truncate_word_errP s1 s2 (w: word s2) e :
  truncate_word s1 w = Error e → e = ErrType ∧ (s2 < s1)%CMP.
Proof.
  by rewrite /truncate_word; case: ifP => // /negbT; rewrite cmp_nle_lt => ? [].
Qed.

Definition to_word (s: wsize) (v: value) : exec (word s) :=
  match v with
  | Vword s' w          => truncate_word s w
  | Vundef (sword s') _ => Error (if (s <= s')%CMP then ErrAddrUndef else ErrType)
  | _                   => type_error
  end.

Lemma to_wordI sz v w:
  to_word sz v = ok w →
  ∃ sz' (w': word sz'), [/\ (sz <= sz')%CMP, v = Vword w' & w = zero_extend sz w'].
Proof.
 case: v => //=.
 + by move=> s w' /truncate_wordP [];exists s, w'.
 by case => // ?;case: ifP => //.
Qed.

Notation to_pointer := (to_word Uptr).

Definition to_arr len v : exec (sem_t (sarr len)) :=
  match v with
  | Varr len' t => WArray.cast len t
  | _ => type_error
  end.

Lemma to_arrI n v t : to_arr n v = ok t ->
  exists n' (t':WArray.array n'), v = Varr t' /\ WArray.cast n t' = ok t.
Proof. by case: v => //= n' t'; eexists; eauto. Qed.

Lemma to_arr_undef p v : to_arr p v <> undef_error.
Proof. by case: v => //= ??; rewrite /WArray.cast; case: ifP. Qed.

(* ----------------------------------------------------------------------- *)

Definition of_val t : value -> exec (sem_t t) :=
  match t return value -> exec (sem_t t) with
  | sbool   => to_bool
  | sint    => to_int
  | sarr n  => to_arr n
  | sword s => to_word s
  end.

Lemma of_vbool ty b v :
  of_val ty (Vbool b) = ok v → ∃ e : ty = sbool, ecast ty (sem_t ty) e v = b.
Proof. by case: ty v => // _ /ok_inj <-; exists erefl. Qed.

Lemma of_vint t n z : of_val t (Vint n) = ok z -> t = sint.
Proof.
  case: t z => //= s' w'.
Qed.

Lemma of_val_int v z: of_val sint v = ok z -> v = Vint z.
Proof. by case v=> //= [? [->] | []]. Qed.

Lemma of_varr t n (a:WArray.array n) z :
  of_val t (Varr a) = ok z -> subtype t (sarr n).
Proof.
  by case: t z => //= n' z; rewrite /WArray.cast; case: ifP.
Qed.

Lemma of_vword t s (w: word s) z :
  of_val t (Vword w) = ok z -> exists s', (s' <= s)%CMP /\ t = sword s'.
Proof.
  case: t z => //= s' w' H.
  exists s';split => //=.
  by move: H; rewrite /truncate_word;  case: (s' <= s)%CMP => //=.
Qed.

Corollary of_val_word sz v w :
  of_val (sword sz) v = ok w →
  ∃ sz' (w': word sz'), [/\ (sz <= sz')%CMP, v = Vword w' & w = zero_extend sz w'].
Proof. exact: to_wordI. Qed.

Lemma of_val_Vword t s1 (w1:word s1) w2 : of_val t (Vword w1) = ok w2 ->
  exists s2 (e:t = sword s2),
    (s2 <= s1)%CMP /\  eq_rect t sem_t w2 _ e = zero_extend s2 w1.
Proof.
  case: t w2 => //= s2 w2 /truncate_wordP [] hle ->.
  by exists s2, erefl.
Qed.

Lemma of_val_undef t t' hn:
  of_val t (Vundef t' hn) =
    Error (if subtype t t' then ErrAddrUndef else ErrType).
Proof. by case: t t' hn => //= [ | | p | s] []. Qed.

Lemma of_val_undef_ok t t' hn v:
  of_val t (Vundef t' hn) <> ok v.
Proof. by rewrite of_val_undef. Qed.

(* ----------------------------------------------------------------------- *)

Definition type_of_val (v:value) : stype :=
  match v with
  | Vbool _     => sbool
  | Vint  _     => sint
  | Varr n _    => sarr n
  | Vword s _   => sword s
  | Vundef t _  => vundef_type t
  end.

Lemma type_of_val_bool v : type_of_val v = sbool ->
  v = undef_b \/ exists b, v = Vbool b.
Proof.
  case: v => //=; first by eauto.
  by move=> [] //=;auto => e ?; rewrite (Eqdep_dec.UIP_refl_bool _ e); left.
Qed.

Lemma type_of_val_int v : type_of_val v = sint ->
  v = Vundef sint (erefl false) \/ exists n, v = Vint n.
Proof.
  case: v => //=;first eauto.
  by move=> [] //=;auto => e _; rewrite (Eqdep_dec.UIP_refl_bool _ e); left.
Qed.

Lemma type_of_val_arr n v : type_of_val v = sarr n -> exists (a:WArray.array n), v = Varr a.
Proof. by case: v => //= [? a [<-] | []] //; exists a. Qed.

Lemma type_of_val_word v wz :
  type_of_val v = sword wz ->
  (wz = U8 /\ exists wz', v = undef_w wz') \/ (∃ w : word wz, v = Vword w).
Proof.
  case: v => //=.
  + by move=> {wz}ws w [<-]; right; eexists.
  case=> // wz' h [<-]; left; split=> //.
  by rewrite (Eqdep_dec.UIP_refl_bool _ h); eexists.
Qed.

Lemma is_wordI sz v u :
  is_word sz v = ok u →
  subtype (vundef_type (sword sz)) (type_of_val v).
Proof. case: v => // [ sz' w | [] // ] _; exact: wsize_le_U8. Qed.

Lemma of_val_subtype t v sv : of_val t v = ok sv -> subtype t (type_of_val v).
Proof.
  case: t sv => /= [ | |p|ws] sv.
  + by move=> /to_boolI ->.
  + by move=> /to_intI ->.
  + by move=> /to_arrI [p' [t' [-> /WArray.cast_len /ZleP]]].
  by move=> /to_wordI [ws' [w [? -> ?]]] /=.
Qed.

Definition to_val t : sem_t t -> value :=
  match t return sem_t t -> value with
  | sbool   => Vbool
  | sint    => Vint
  | sarr n  => @Varr n
  | sword s => @Vword s
  end.

Lemma to_val_inj t (v1 v2:sem_t t) : to_val v1 = to_val v2 -> v1 = v2.
Proof.
  by case: t v1 v2 => //= [ | | p | sz ] v1 v2 => [ []|[] |/Varr_inj1 |[] ] ->.
Qed.

Lemma to_val_undef t (v:sem_t t) t' h : to_val v <> Vundef t' h.
Proof. by case: t v. Qed.

Lemma type_of_to_val t (s: sem_t t) : type_of_val (to_val s) = t.
Proof. by case: t s. Qed.

Lemma of_val_type_of_val (v: value) :
  is_defined v → exists2 x, of_val (type_of_val v) v = ok x & to_val x = v.
Proof.
case: v => //=; eauto.
+ move=> n a _;rewrite /WArray.cast.
  exists a => //; case: ifP => /ZleP; last by lia.
  by move=> _; f_equal;case: a.
by move => sz w; rewrite truncate_word_u; eauto.
Qed.

(* ----------------------------------------------------------------------- *)

Definition truncate_val (ty: stype) (v: value) : exec value :=
  of_val ty v >>= λ x, ok (to_val x).

Lemma truncate_val_subtype ty v v' :
  truncate_val ty v = ok v' →
  subtype ty (type_of_val v).
Proof.
  case: ty v => [ | | n | sz ] [] //; try by case.
  - move => n' t; rewrite /truncate_val /=.
    by rewrite /WArray.cast; case: ifP.
  by move => sz' w; rewrite /truncate_val /=; t_xrbindP => w' /truncate_wordP [].
Qed.

Lemma truncate_val_has_type ty v v' :
  truncate_val ty v = ok v' →
  type_of_val v' = ty.
Proof.
  case: ty v => [ | | n | sz ] [] //; try by case.
  - by move => b [<-].
  - by move => z [<-].
  - move => n' t; rewrite /truncate_val /= /WArray.cast.
    by case: ifP => h //= [<-].
  by move => sz' w; rewrite /truncate_val /=; t_xrbindP => w' /truncate_wordP [] ? -> <-.
Qed.

Lemma truncate_val_bool t (b:bool) v : truncate_val t b = ok v -> t = sbool /\ v = b.
Proof. by case: t => //= -[] <-. Qed.

Lemma truncate_val_boolI t (b:bool) v : truncate_val t v = ok (Vbool b) -> t = sbool /\ v = b.
Proof.
  move=> h; have /= ? := truncate_val_has_type h;subst t.
  by case: v h => //= [ b' [->] | []].
Qed.

Lemma truncate_val_int ty (z: Z) v :
  truncate_val ty z = ok v →
  ty = sint ∧ v = z.
Proof. by case: ty => // - []. Qed.

Lemma truncate_val_wordI ty v sz w :
  truncate_val ty v = ok (@Vword sz w) →
  ∃ sz' (w': word sz'), ty = sword sz /\ v = Vword w' ∧ (sz ≤ sz')%CMP /\ w = zero_extend sz w'.
Proof.
case: ty v => [ | | n | s ] [] //; try by case.
- by move => n' t; rewrite /truncate_val /= /WArray.cast; case: ifP.
move => sz' w'; rewrite /truncate_val /=.
apply: rbindP => w'' /truncate_wordP [] => hle -> h.
have := ok_inj h => {h} /Vword_inj [] ?; subst => /= ?; subst.
by exists sz', w'.
Qed.

Lemma truncate_val_word ty sz (w: word sz) v :
  truncate_val ty (Vword w) = ok v →
  ∃ sz',
    [/\
    ty = sword sz',
    (sz' ≤ sz)%CMP &
    v = Vword (zero_extend sz' w) ].
Proof.
by case: ty => // sz'; apply: rbindP => w' /truncate_wordP [] hle -> [<-]; exists sz'.
Qed.

Definition oto_val t : sem_ot t -> value :=
  match t return sem_ot t -> value with
  | sbool => fun ob => if ob is Some b then Vbool b else undef_b
  | x     => @to_val x
  end.

Lemma type_of_oto_val t (s: sem_ot t) : type_of_val (oto_val s) = t.
Proof. by case: t s => //= -[]. Qed.

Definition check_ty_val (ty:stype) (v:value) :=
  subtype ty (type_of_val v).

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

Fixpoint app_sopn T ts : sem_prod ts (exec T) → values → exec T :=
  match ts return sem_prod ts (exec T) → values → exec T with
  | [::] => λ (o : exec T) (vs: values), if vs is [::] then o else type_error
  | t :: ts => λ (o: sem_t t → sem_prod ts (exec T)) (vs: values),
    if vs is v :: vs
    then Let v := of_val t v in app_sopn (o v) vs
    else type_error
  end.

Arguments app_sopn {T} ts _ _.

Definition app_sopn_v tin tout (semi: sem_prod tin (exec (sem_tuple tout))) vs :=
  Let t := app_sopn _ semi vs in
  ok (list_ltuple t).

(* ----------------------------------------------------------------------- *)

Definition value_uincl (v1 v2:value) :=
  match v1, v2 with
  | Vbool b1, Vbool b2 => b1 = b2
  | Vint n1, Vint n2   => n1 = n2
  | Varr n1 t1, Varr n2 t2 => WArray.uincl t1 t2
  | Vword sz1 w1, Vword sz2 w2 => word_uincl w1 w2
  | Vundef t _, _     => compat_type t (type_of_val v2)
  | _, _ => False
  end.

Lemma value_uinclE v1 v2 :
  value_uincl v1 v2 →
  match v1 with
  | Vbool _ | Vint _ => v2 = v1
  | Varr n1 t1 =>
    exists n2,
      exists2 t2, v2 = @Varr n2 t2 & WArray.uincl t1 t2
  | Vword sz1 w1 => ∃ sz2 w2, v2 = @Vword sz2 w2 ∧ word_uincl w1 w2
  | Vundef t _ => ~is_sarr t /\ compat_type t (type_of_val v2)
  end.
Proof.
  by case: v1 v2 => [ b1 | n1 | n1 t1 | sz1 w1 | t1 /= /negP h]; eauto; case => //; eauto => ? <-.
Qed.

Lemma value_uincl_refl v: @value_uincl v v.
Proof. by case: v => //= *; apply compat_type_undef. Qed.

Hint Resolve value_uincl_refl : core.

Lemma value_uincl_trans v2 v1 v3 :
  value_uincl v1 v2 ->
  value_uincl v2 v3 ->
  value_uincl v1 v3.
Proof.
  case: v1; case: v2 => //=; last (by
   move=> ???? h; apply:compat_type_trans;
   apply : (compat_type_trans h); rewrite compat_typeC compat_type_undef);
  case:v3=> //=.
  + by move=> ??? ->.
  + by move=> ??? ->.
  + by move=> ?? ?? ??; apply: WArray.uincl_trans.
  by move=> //= ??????;apply word_uincl_trans.
Qed.

Lemma value_uincl_bool1 b v : value_uincl (Vbool b) v -> v = Vbool b.
Proof. by case: v => //= ? ->. Qed.

Lemma value_uincl_bool ve ve' b :
  value_uincl ve ve' -> to_bool ve = ok b -> ve = b /\ ve' = b.
Proof. by case: ve => // [ b' /value_uincl_bool1 -> [->]| []//]. Qed.

Lemma value_uincl_int1 z v : value_uincl (Vint z) v -> v = Vint z.
Proof. by case: v => //= ? ->. Qed.

Lemma value_uincl_int ve ve' z :
  value_uincl ve ve' -> to_int ve = ok z -> ve = z /\ ve' = z.
Proof. by case: ve => // [ b' /value_uincl_int1 -> [->]| []//]. Qed.

Lemma value_uincl_arr ve ve' len (t: WArray.array len) :
  value_uincl ve ve' →
  to_arr len ve  = ok t →
  exists2 t', to_arr len ve' = ok t' & WArray.uincl t t'.
Proof.
case: ve ve' => //=.
by move=> len' a [] // len1 a1 hle /(WArray.uincl_cast hle) [] a2' [] ??; exists a2'.
Qed.

Lemma value_uincl_word ve ve' sz (w: word sz) :
  value_uincl ve ve' →
  to_word sz ve  = ok w →
  to_word sz ve' = ok w.
Proof.
case: ve ve' => //=;last by case.
move => sz' w' [] // sz1 w1 /andP [] hle /eqP -> /truncate_wordP [] hle'.
by rewrite zero_extend_idem // => -> /=; rewrite /truncate_word (cmp_le_trans hle' hle).
Qed.

Lemma value_uincl_word_of_val sz ty v w vt :
  value_uincl v (@Vword sz w) → of_val ty v = ok vt → of_val ty (Vword w) = ok vt.
Proof.
  case: v => //=; last by move=> ??;rewrite of_val_undef.
  move=> sz' w' /andP[hsz1 /eqP ->] /of_val_Vword [sz1 [heq]]; subst ty => /= -[hsz ->].
  by rewrite zero_extend_idem // /truncate_word (cmp_le_trans hsz hsz1).
Qed.

Lemma value_uincl_undef v ty h : value_uincl v (Vundef ty h) -> exists ty' h', v = Vundef ty' h'.
Proof. case: v => //; eauto. Qed.

Lemma value_uincl_zero_ext sz sz' (w':word sz') : (sz ≤ sz')%CMP ->
  value_uincl (Vword (zero_extend sz w')) (Vword w').
Proof. apply word_uincl_zero_ext. Qed.

Lemma value_uincl_subtype v1 v2 :
  value_uincl v1 v2 ->
  subtype (type_of_val v1) (type_of_val v2).
Proof.
case: v1 v2 => [ b | i | n t | s w | ty /= /negP h]; try by case.
+ by case => //= n' t' [] /ZleP.
+ by case => //= s' w' /andP[].
by move => /= v2; apply compat_subtype_undef.
Qed.

Lemma value_uincl_is_defined x y :
  value_uincl x y →
  is_defined x →
  is_defined y.
Proof. by case: y => //=; case; case: x. Qed.

Lemma value_uincl_compat_type v1 v1' v2 v2':
  value_uincl v1 v1' -> value_uincl v2 v2' ->
  compat_type (type_of_val v1) (type_of_val v2) ->
  compat_type (type_of_val v1') (type_of_val v2').
Proof.
  move=> /value_uincl_subtype -/subtype_compat h1.
  move=> /value_uincl_subtype -/subtype_compat h2 hc.
  apply: compat_type_trans h2; apply: compat_type_trans hc.
  by rewrite compat_typeC.
Qed.

(* ------------------------------------------------------------------------ *)

Lemma value_uincl_truncate ty x y x' :
  value_uincl x y →
  truncate_val ty x = ok x' →
  exists2 y', truncate_val ty y = ok y' & value_uincl x' y'.
Proof.
case: ty x y => //.
- by case => // [ b | [] ] // [] //= ? <- [<-]; exists (Vbool b).
- by case => // [ z | [] ] // [] //= ? <- [<-]; exists (Vint z).
- move => n; case => //  n' t' [] //=.
  move => n'' t hu; rewrite /truncate_val /=.
  by t_xrbindP => t1 /(WArray.uincl_cast hu) [t2] [-> ?] <- /=; exists (Varr t2).
(move => sz; case => // [ sz' w | [] // sz' ];
case) => // sz'' w' /=.
case/andP => hsz' /eqP -> {w}; rewrite /truncate_val /= /truncate_word.
case: ifP => // hsz [<-].
rewrite (cmp_le_trans hsz hsz') /=; eexists; first reflexivity.
by rewrite/= zero_extend_idem.
Qed.

Lemma truncate_value_uincl t v1 v2 : truncate_val t v1 = ok v2 -> value_uincl v2 v1.
Proof.
  rewrite /truncate_val;case: t; t_xrbindP => /=.
  + by move=> b /to_boolI -> <-.
  + by move=> b /to_intI -> <-.
  + by move=> n t /to_arrI [n' [t' [-> h]]] <- /=; apply: WArray.cast_uincl.
  move=> sz w /to_wordI [sz' [w' [? -> -> <-]]] => /=.
  by apply word_uincl_zero_ext.
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

Lemma vuincl_sopn T ts o vs vs' (v: T) :
  all is_not_sarr ts ->
  List.Forall2 value_uincl vs vs' ->
  app_sopn ts o vs = ok v ->
  app_sopn ts o vs' = ok v.
Proof.
  elim: ts o vs vs' => /= [ | t ts Hrec] o [] //.
  + by move => vs' _ /List_Forall2_inv_l -> ->; eauto using List_Forall2_refl.
  move => n vs vs'' /andP [] ht hts /List_Forall2_inv_l [v'] [vs'] [->] {vs''} [hv hvs].
  case: t o ht => //= [ | | sz ] o _; apply: rbindP.
  + by move=> b /(value_uincl_bool hv) [] _ -> /= /(Hrec _ _ _ hts hvs).
  + by move=> z /(value_uincl_int hv) [] _ -> /= /(Hrec _ _ _ hts hvs).
  by move=> w /(value_uincl_word hv) -> /= /(Hrec _ _ _ hts hvs).
Qed.

Lemma vuincl_app_sopn_v_eq tin tout (semi: sem_prod tin (exec (sem_tuple tout))) : 
  all is_not_sarr tin -> 
  forall vs vs' v,
  List.Forall2 value_uincl vs vs' -> 
  app_sopn_v semi vs = ok v -> 
  app_sopn_v semi vs' = ok v.
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
  move=> /= vs vs' v; rewrite /app_sopn_v /= => -[] {vs vs'} // v1 v2 ?? hu []; t_xrbindP => //=.
  by move=> t a /(value_uincl_arr hu) /= [a'] -> hut /= /(WArray.uincl_copy hut) -> <-.
Qed.

Lemma ok_values_uincl_refl (f: exec values) v :
  f = ok v →
  exists2 v', f = ok v' & List.Forall2 value_uincl v v'.
Proof. move => ?; exists v => //; exact: List_Forall2_refl value_uincl_refl. Qed.

Definition vuincl_app_sopn_v tin tout (semi: sem_prod tin (exec (sem_tuple tout))) :
  all is_not_sarr tin ->
  forall vs vs' v,
  List.Forall2 value_uincl vs vs' ->
  app_sopn_v semi vs = ok v ->
  _ :=
  λ A vs vs' v B C, ok_values_uincl_refl (vuincl_app_sopn_v_eq A B C).

Definition vuincl_copy ws p :
  let sz := Z.to_pos (arr_size ws p) in
  forall vs vs' v,
  List.Forall2 value_uincl vs vs' ->
  @app_sopn_v [::sarr sz] [::sarr sz] (@WArray.copy ws p) vs = ok v ->
  _ :=
  λ vs vs' v A B, ok_values_uincl_refl (vuincl_copy_eq A B).

Lemma check_ty_val_uincl v1 x v2 :
  check_ty_val x v1 → value_uincl v1 v2 → check_ty_val x v2.
Proof.
  rewrite /check_ty_val => h /value_uincl_subtype.
  by apply: subtype_trans.
Qed.

(* ------------------------------------------------------------------------ *)

Definition val_uincl (t1 t2:stype) (v1:sem_t t1) (v2:sem_t t2) :=
  value_uincl (to_val v1) (to_val v2).

Lemma val_uincl_refl t v: @val_uincl t t v v.
Proof. by rewrite /val_uincl. Qed.
Hint Resolve val_uincl_refl : core.

Lemma val_uincl_sword s (z z':sem_t (sword s)) : val_uincl z z' -> z = z'.
Proof.
  by rewrite /val_uincl /= /word_uincl cmp_le_refl zero_extend_u => /eqP.
Qed.

Lemma value_uincl_is_word v v' sz u :
  value_uincl v v' →
  is_word sz v = ok u →
  is_word sz v' = ok tt.
Proof.
move => /value_uinclE; case: v => //.
+ by move=> ?? [] ? [] ? [] ->.
by move=> [] // ?? [?] /=; case: v' => //= -[].
Qed.

Lemma val_uincl_eq t (x y: sem_t t) :
  val_uincl x y →
  ~~is_sarr t ->
  y = x.
Proof.
  case: t x y => //.
  by move => sz /= x y /andP [] _ /eqP ->; rewrite zero_extend_u.
Qed.

Lemma of_val_uincl v v' t z:
  value_uincl v v' ->
  of_val t v = ok z ->
  exists z', of_val t v' = ok z' /\ val_uincl z z'.
Proof.
  case: v v'=> [b | n | n a | sz w | tv h] [b' | n' | n' a' | sz' w' | tv' h'] //=;
    try by move=> _ /of_val_undef_ok.
  + by move=> <- ->;eauto.
  + by move=> <- ->;eauto.
  + by move=> hu; case: t z => //= p a1 hc; apply: WArray.uincl_cast hu hc.
  move=> /andP []hsz /eqP -> /of_val_Vword [] s2 [] ?;subst => /= -[] hle ->.
  rewrite /truncate_word (cmp_le_trans hle hsz) zero_extend_idem //.
  by eexists;split;first reflexivity.
Qed.
