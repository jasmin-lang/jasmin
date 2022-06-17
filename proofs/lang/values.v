(* * Syntax and semantics of the Jasmin source language *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ.
Require Import Psatz xseq.
Require Export warray_ word sem_type.
Import Utf8.
Import ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* ** Values
  * -------------------------------------------------------------------- *)

Definition is_undef_t (t: stype) := [|| t == sbool, t == sint | t == sword8].

Lemma is_undef_tE t : is_undef_t t -> [\/ t = sbool, t = sint | t = sword8].
Proof. by case/or3P => /eqP; firstorder. Qed.

Lemma is_undef_t_sword s : is_undef_t (sword s) -> s = U8.
Proof. by case: s. Qed.

Lemma is_undef_t_not_sarr t : is_undef_t t -> is_not_sarr t.
Proof. by case: t. Qed.

Definition undef_t t (_: is_not_sarr t) := if is_sword t then sword8 else t.
Arguments undef_t _ _ : clear implicits.

Lemma is_undef_t_undef_t t harr : is_undef_t (undef_t t harr).
Proof. by case: t harr. Qed.

Lemma undef_t_id t harr : is_undef_t t -> undef_t t harr = t.
Proof. by case: t harr => // ?? /is_undef_t_sword ->. Qed.

Lemma is_undef_t_compat_subtype (t t': stype) :
  is_undef_t t -> compat_type t t' -> subtype t t'.
Proof.
  case: t => // ? /is_undef_t_sword -> /compat_typeEl /is_swordP[? ->].
  exact: wsize_le_U8.
Qed.

Variant value : Type :=
  | Vbool :> bool -> value
  | Vint :> Z -> value
  | Varr len :> WArray.array len -> value
  | Vword s : word s -> value
  | Vundef t : is_undef_t t -> value.
Arguments Vundef _ _ : clear implicits.

Lemma Varr_inj n n' t t' (e: @Varr n t = @Varr n' t') :
  exists en: n = n', eq_rect _ _ t _ en = t'.
Proof.
  by case: e => ?; subst; exists erefl;
    exact: (Eqdep_dec.inj_pair2_eq_dec _ Pos.eq_dec).
Qed.

Corollary Varr_inj1 n t t' : @Varr n t = @Varr n t' -> t = t'.
Proof.
  by move=> /Varr_inj [en ]; rewrite (Eqdep_dec.UIP_dec Pos.eq_dec en erefl).
Qed.

Lemma Vword_inj sz sz' w w' (e: @Vword sz w = @Vword sz' w') :
  exists e : sz = sz', eq_rect sz (λ s, (word s)) w sz' e = w'.
Proof. by case: e => ?; subst=> -[->]; exists erefl. Qed.

Notation undef_b := (Vundef sbool erefl).
Notation undef_i := (Vundef sint erefl).
Notation undef_w := (Vundef sword8 erefl).
Definition undef_v t (h: is_not_sarr t) :=
  Vundef (undef_t t h) (is_undef_t_undef_t h).
Arguments undef_v _ _ : clear implicits.

Definition values := seq value.

Definition is_defined v := if v is Vundef _ _ then false else true.

Lemma is_not_defined v : ~is_defined v -> exists t h, v = Vundef t h.
Proof. by case v; eauto. Qed.

Lemma undef_x_vundef t h : Vundef t h =
  match t with
  | sbool => undef_b
  | sint => undef_i
  | sword _ => undef_w
  | _ => Vundef t h
  end.
Proof.
  by case: t h => [||//|_ /[dup] /is_undef_t_sword ->] ?;
    f_equal; exact: Eqdep_dec.UIP_refl_bool.
Qed.

(* ** Type of values
  * -------------------------------------------------------------------- *)

Definition type_of_val v :=
  match v with
  | Vbool _ => sbool
  | Vint  _ => sint
  | Varr n _ => sarr n
  | Vword s _ => sword s
  | Vundef t _ => t
  end.

Lemma type_of_valI v t : type_of_val v = t ->
  match t with
  | sbool => v = undef_b \/ exists b: bool, v = b
  | sint => v = undef_i \/ exists i: Z, v = i
  | sarr len => exists a, v = @Varr len a
  | sword ws => (ws = U8 /\ v = undef_w) \/ exists w, v = @Vword ws w
  end.
Proof.
  case: v => /= [?|?|>|>|++] <-; eauto.
  case=> [||?|?] h; rewrite (undef_x_vundef h) //; auto.
  by rewrite /is_undef_t /= in h; case: (eqP h); auto.
Qed.

Definition typerel_undef (rel: stype -> stype -> bool) ty v :=
  (if is_defined v then rel else compat_type) ty (type_of_val v).

Lemma typerel_undefE rel t v :
  typerel_undef rel t v ->
  match v with
  | Vundef ty _ => compat_type ty t
  | _ => rel t (type_of_val v)
  end.
Proof. by case: v => //= ?; rewrite /typerel_undef compat_typeC. Qed.

Lemma typerel_undef_typeE rel t v :
  subrel rel compat_type -> typerel_undef rel t v ->
  match t with
  | sarr _ => exists2 len, rel t (sarr len) & exists a, v = @Varr len a
  | sword ws => is_sword (type_of_val v) /\ (is_defined v -> rel t (type_of_val v))
  | _ => is_true (compat_type t (type_of_val v))
  end.
Proof.
  by (case: v => [||||? /[dup]/is_undef_tE] >;
    last by case=> -> ?? /compat_typeE => [||/is_swordP[?]] ->)
    => Hs /[dup]/Hs/compat_typeE => [|||/is_swordP[?]] -> //=; eauto.
Qed.

Lemma typerel_undefI rel t v : subrel rel compat_type ->
  is_true (rel t (type_of_val v)) -> typerel_undef rel t v.
Proof. by case: v => // >; apply. Qed.

Lemma typerel_undef_refl rel v :
  reflexive rel -> typerel_undef rel (type_of_val v) v.
Proof. by case: v; rewrite /typerel_undef. Qed.

Lemma typerel_undef_compat rel t v : subrel rel compat_type ->
  typerel_undef rel t v -> compat_type t (type_of_val v).
Proof. by case: v => > //= h/h. Qed.

Lemma typerel_undef_trans rel t t' v : subrel rel compat_type ->
  transitive rel ->
  rel t t' -> typerel_undef rel t' v -> typerel_undef rel t v.
Proof.
  by case: v => [||||> Hs _ /Hs /compat_type_trans Ht/Ht //]
    > Hs Ht /Ht{Ht}Ht /typerel_undefE/Ht/(typerel_undefI Hs).
Qed.

Definition check_ty_val := typerel_undef subtype.

Lemma check_ty_val_refl v : check_ty_val (type_of_val v) v.
Proof. exact: (typerel_undef_refl _ subtype_refl). Qed.

Lemma check_ty_val_compat t v :
  check_ty_val t v -> compat_type t (type_of_val v).
Proof. exact: (typerel_undef_compat subtype_compat). Qed.

(* ** Test for extension of values
  * -------------------------------------------------------------------- *)

Definition value_uincl (v1 v2:value) :=
  match v1, v2 with
  | Vbool b1, Vbool b2 => b1 = b2
  | Vint n1, Vint n2 => n1 = n2
  | Varr len1 t1, Varr len2 t2 => len1 = len2 /\ WArray.uincl t1 t2
  | Vword sz1 w1, Vword sz2 w2 => word_uincl w1 w2
  | Vundef t _, _ => compat_type t (type_of_val v2)
  | _, _ => False
  end.

Lemma value_uinclE v1 v2 :
  value_uincl v1 v2 →
  match v1 with
  | Varr n t1 => exists2 t2, v2 = @Varr n t2 & WArray.uincl t1 t2
  | Vword sz1 w1 => exists sz2, exists2 w2, v2 = @Vword sz2 w2 & word_uincl w1 w2
  | Vundef t _ => compat_type t (type_of_val v2)
  | _ => v2 = v1
  end.
Proof. by (case: v1 => >; case: v2 => > //=) => [||[?]|] ?; subst; eauto. Qed.

Lemma value_uincl_refl v: value_uincl v v.
Proof. by case: v => //= *; exact: compat_type_undef. Qed.

#[global]
Hint Resolve value_uincl_refl : core.

Lemma value_uincl_subtype v1 v2 :
  value_uincl v1 v2 -> subtype (type_of_val v1) (type_of_val v2).
Proof.
  case: v1 => [||||t h] > /value_uinclE; try by move=> ->.
  + by case=> ?->.
  + by case=> ? [? ->]; rewrite /word_uincl => [/andP[]].
  exact: is_undef_t_compat_subtype h.
Qed.

Lemma value_uincl_trans v2 v1 v3 :
  value_uincl v1 v2 -> value_uincl v2 v3 -> value_uincl v1 v3.
Proof.
  case: v1 => > /value_uinclE; try by move=> -> /value_uinclE ->.
  + by case=> ? -> /WArray.uincl_trans h /value_uinclE [? -> /h].
  + by case=> ? [? -> /word_uincl_trans h] /value_uinclE [? [? -> /h]].
  by move=> /compat_type_trans h /value_uincl_subtype /subtype_compat /h.
Qed.

Lemma value_uincl_is_defined x y :
  value_uincl x y → is_defined x → is_defined y.
Proof. by case: y x => // ?? []. Qed.

Lemma value_uincl_compat_type v1 v1' v2 v2':
  value_uincl v1 v1' -> value_uincl v2 v2' ->
  compat_type (type_of_val v1) (type_of_val v2) ->
  compat_type (type_of_val v1') (type_of_val v2').
Proof.
  move=> /value_uincl_subtype /subtype_compat +
    /value_uincl_subtype /subtype_compat /[swap].
  by rewrite compat_typeC => /compat_type_trans h/h; exact: compat_type_trans.
Qed.

(* ** Values implicit downcast (upcast is explicit because of signedness)
  * -------------------------------------------------------------------- *)

Definition truncate_val (ty: stype) v :=
  match v, ty with
  | Vbool b, sbool => ok v
  | Vint i, sint => ok v
  | Varr n _, sarr n' => if n == n' then ok v else type_error
  | Vword s w, sword s' => ok (rapp (@Vword _) v (truncate_word s' w))
  | Vundef t _, _ => if compat_type t ty then ok v else type_error
  | _, _ => type_error
  end.

Lemma truncate_valE ty v vt :
  truncate_val ty v = ok vt ->
  match v with
  | Vbool b => ty = sbool /\ vt = b
  | Vint i => ty = sint /\ vt = i
  | Varr len a => ty = sarr len /\ vt = a
  | Vword _ w => exists2 ws, ty = sword ws &
    vt = rapp (@Vword _) v (truncate_word ws w)
  | Vundef t h => compat_type t ty /\ vt = v
  end.
Proof.
  case: v => > /=; last (by case: ifP => // _ []); case: ty => // >.
  3: by case: ifP => // /eqP <- [<-].
  all: by case=> <-; eexists.
Qed.

Lemma truncate_valE' ty v vt :
  truncate_val ty v = ok vt ->
  match v with
  | Vbool b => ty = sbool /\ vt = b
  | Vint i => ty = sint /\ vt = i
  | Varr len a => ty = sarr len /\ vt = a
  | Vword ws w => exists2 ws', ty = sword ws' &
    ((ws' <= ws)%CMP /\ vt = Vword (zero_extend ws' w)) \/ ((ws < ws')%CMP /\ vt = v)
  | Vundef t h => compat_type t ty /\ vt = v
  end.
Proof.
  case: v => > /truncate_valE[// ? ->].
  by case: Result.rappP => [?/truncate_wordP[? ->]|?/truncate_word_errP[_ ?]] ->; eauto.
Qed.

Lemma truncate_val_typeE ty v vt : truncate_val ty v = ok vt ->
  if is_sword ty
    then subtype (type_of_val vt) ty /\ subtype (type_of_val vt) (type_of_val v)
    else typerel_undef eq_op ty vt /\ v = vt.
Proof.
  (case: v => [||||?/[dup]/is_undef_tE[]->?/truncate_valE[]/[swap]->/compat_typeEl/=/[dup]+->//];
    last by move=> /is_swordP[?->]; split=> //; exact: wsize_le_U8)
    => > /truncate_valE[> -> ->] //=; rewrite /typerel_undef //=.
  case: Result.rappP => [?/truncate_wordP[? _]|?/truncate_word_errP[_ ?]] //=.
  by split=> //; exact: cmp_lt_le.
Qed.

Lemma truncate_valI ty v vt :
  truncate_val ty v = ok vt ->
  match vt with
  | Vbool b => ty = sbool /\ v = b
  | Vint i => ty = sint /\ v = i
  | Varr len a => ty = sarr len /\ v = a
  | Vword ws w => subtype (sword ws) ty /\ subtype (sword ws) (type_of_val v)
  | Vundef t h => compat_type t ty /\ v = vt
  end.
Proof.
  (case: v => [||||?/[dup]/is_undef_tE];
    last by case => -> ? /truncate_valE[] /compat_typeEl
      => [||/is_swordP[?]] -> ->)
    => > /truncate_valE[> -> ->] //.
  case: Result.rappP => [?/truncate_wordP/proj1 //|?/truncate_word_errP/proj2 H].
  by have // := cmp_lt_le H.
Qed.

Lemma subtype_truncate_val ty v : subtype ty (type_of_val v) ->
  exists2 vt, truncate_val ty v = ok vt & is_defined v -> is_defined vt.
Proof.
  case: v => /= [||||?/[dup]/is_undef_tE[]->?] > /subtypeE => [|||[?]|||[?]] ->;
    eexists=> //.
  + by rewrite eq_refl.
  + done.
  by case: truncate_word.
Qed.

Lemma truncate_val_compat_undef ty ty' p :
  compat_type ty ty' -> truncate_val ty' (Vundef ty p) = ok (Vundef ty p).
Proof. by simpl=> /(ifT _ _). Qed.

Lemma truncate_val_u ty v :
  typerel_undef (Basics.flip subtype) ty v -> truncate_val ty v = ok v.
Proof.
  rewrite /Basics.flip; case: v => /= > /typerel_undefE => [||||->//] /subtypeEl
    => [|||[?]] -> //=.
  + by rewrite ifT.
  case: Result.rappP => // ? /truncate_wordP[/cmp_le_antisym h ->]/h{h}?; subst.
  by rewrite zero_extend_u.
Qed.

(* ------------------------------------------------------------------------------- *)

Lemma truncate_val_compat_type ty v v' : truncate_val ty v = ok v' ->
  subtype (type_of_val v') (type_of_val v) /\ compat_type (type_of_val v) ty.
Proof.
  by case: ty => > /truncate_val_typeE[]
    => [|||/subtypeE[? -> _]/subtypeEl[? -> _]//]
    /(typerel_undef_compat _)/Wrap[>/eqP->//|/[swap]->];
    rewrite compat_typeC.
Qed.

Lemma value_uincl_truncate ty x y x' :
  value_uincl x y → truncate_val ty x = ok x' →
  exists2 y', truncate_val ty y = ok y' & value_uincl x' y'.
Proof.
  (case: x => [||||? /[dup]/is_undef_tE] >;
    last by case=> -> ? /compat_typeEl
      => [||/is_swordP[?]] /type_of_valI+ /truncate_valE[/compat_typeEl+ ->]
      => [+|+|+ /is_swordP[?]] -> => [[|[]]|[|[]]|[[?]|[]]] > -> /=;
      eexists=> //; case: truncate_word)
    => /value_uinclE => [||[? + ?]|[? [? + h]]]
    => -> /truncate_valE[] => [|||?] -> ->; eexists; try reflexivity.
  + by rewrite /= ifT.
  + done.
  case: Result.rappP => [?/(word_uincl_truncate h)->//|? /truncate_word_errP[_ h']].
  case: Result.rappP => // ? /truncate_wordP[? ->].
  by rewrite (eqP (proj2 (andP h))){h} /= /word_uincl
    zero_extend_idem (cmp_lt_le h') // eq_refl.
Qed.

Lemma truncate_value_uincl t v1 v2 :
  truncate_val t v1 = ok v2 -> value_uincl v2 v1.
Proof.
  case: v1 => > /truncate_valE[] => [|||?|] _ -> //.
  by case: Result.rappP => // ? /truncate_word_uincl.
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
  if v is Varr len' t then if Sumbool.sumbool_of_bool (len' == len) is left h
    then ok (eq_rect _ _ t _ (eqP h)) else type_error else type_error.

Lemma to_arrI n v t : to_arr n v = ok t -> v = t.
Proof.
  case: v => //= >; case: Sumbool.sumbool_of_bool => // /[dup] /eqP ?.
  by subst=> ? [<-]; rewrite (Eqdep_dec.UIP_dec Pos.eq_dec (eqP _)).
Qed.

Lemma to_arr_id n v : to_arr n (Varr v) = ok v.
Proof.
  by rewrite /= sumbool_of_boolET (Eqdep_dec.UIP_dec Pos.eq_dec (eqP _)).
Qed.

Definition to_word s v : exec (word s) :=
  match v with
  | Vword s' w => truncate_word s w
  | Vundef (sword _) _ => undef_error
  | _ => type_error
  end.

Notation to_pointer := (to_word Uptr).

Lemma to_wordI sz v w : to_word sz v = ok w ->
  exists sz', exists2 w', v = @Vword sz' w' & truncate_word sz w' = ok w.
Proof. by case: v => //=; eauto; case. Qed.

Lemma to_wordI' sz v w : to_word sz v = ok w -> exists sz' w',
  [/\ (sz <= sz')%CMP, v = @Vword sz' w' & w = zero_extend sz w'].
Proof.
  move=> /to_wordI[sz' [w' ? /truncate_wordP[??]]]; eexists _, _.
  by split; eauto.
Qed.

Lemma to_word_undef s v :
  to_word s v = undef_error -> v = undef_w.
Proof.
  case: v => //= [> /truncate_word_errP |] [] // ??.
  by rewrite undef_x_vundef.
Qed.

(* ----------------------------------------------------------------------- *)

Definition of_val t : value -> exec (sem_t t) :=
  match t return value -> exec (sem_t t) with
  | sbool => to_bool
  | sint => to_int
  | sarr n => to_arr n
  | sword s => to_word s
  end.

Lemma of_val_typeE t v vt : of_val t v = ok vt ->
  match t return sem_t t -> Prop with
  | sword ws => fun vt => exists ws',
    exists2 w, v = @Vword ws' w & truncate_word ws w = ok vt
  | _ => fun vt => v = vt
  end vt.
Proof.
  by case: t vt => /=; auto using to_boolI, to_intI, to_arrI, to_wordI.
Qed.

Lemma of_valE t v v' : of_val t v = ok v' ->
  match v with
  | Vbool b => exists h: t = sbool, eq_rect _ _ v' _ h = b
  | Vint i => exists h: t = sint, eq_rect _ _ v' _ h = i
  | Varr len a => exists h: t = sarr len, eq_rect _ _ v' _ h = a
  | Vword ws w => exists ws', exists2 w', truncate_word ws' w = ok w'
    & exists h: t = sword ws', eq_rect _ _ v' _ h = w'
  | Vundef t h => False
  end.
Proof.
  by case: t v' => > /of_val_typeE;
    last (by case=> ? [? -> ?]; eexists; eexists; eauto; exists erefl);
    move=> ->; exists erefl.
Qed.

Lemma of_val_error t v:
  of_val t v = undef_error -> exists h, v = undef_v t h.
Proof.
  case: t => > => [/to_bool_undef -> | /to_int_undef -> | | /to_word_undef ->];
    try by exists erefl; rewrite /undef_v (undef_x_vundef (_ _)).
  by case: v => //= >; case: Sumbool.sumbool_of_bool.
Qed.

Lemma of_val_undef t t' h :
  of_val t (Vundef t' h) = (if compat_type t t' then undef_error else type_error).
Proof. by case: t t' h => //= [ | | p | s] []. Qed.

Lemma of_val_subtype t v sv : of_val t v = ok sv -> subtype t (type_of_val v).
Proof.
  case: t sv => > /of_val_typeE; try by move=> ->.
  by case=> ? [? -> /truncate_wordP[]].
Qed.

(* can be use to shorten proofs drastically, see psem/vuincl_sem_sop1 *)
Lemma of_value_uincl_te ty v v' vt :
  value_uincl v v' -> of_val ty v = ok vt ->
  match ty return sem_t ty -> Prop with
  | sarr n => fun vt => exists2 a, of_val (sarr n) v' = ok a & WArray.uincl vt a
  | _ => fun _ => of_val ty v' = ok vt
  end vt.
Proof.
  ((case: v => > /[swap] /of_valE[] ?; subst)
    => /= [|||[? /word_uincl_truncate h][?]]; subst => /= ->;
    case: v' => // >) => [||[?]] ?; subst => //.
  by eexists; eauto using to_arr_id.
Qed.

Lemma of_value_uincl ty v v' vt :
  value_uincl v v' -> of_val ty v = ok vt ->
  match v' with
  | Varr len a => exists (h: ty = sarr len) a,
    of_val (sarr len) v' = ok a /\ WArray.uincl (eq_rect _ _ vt _ h) a
  | _ => of_val ty v' = ok vt
  end.
Proof.
  (case: ty vt => vt > /of_value_uincl_te h/h{h} => [||[?]|] /of_val_typeE)
    => [->|->|-> ?|[?[? ->]]]; simpl in vt => //.
  by exists erefl; eauto using to_arr_id.
Qed.

(* ----------------------------------------------------------------------- *)

Definition to_val t : sem_t t -> value :=
  match t return sem_t t -> value with
  | sbool => Vbool
  | sint => Vint
  | sarr n => @Varr n
  | sword s => @Vword s
  end.

Lemma to_val_inj t (v1 v2: sem_t t) : to_val v1 = to_val v2 -> v1 = v2.
Proof. by case: t v1 v2 => /= > => [[]|[]| /Varr_inj1 |[]]. Qed.

Lemma to_valI t (x: sem_t t) v : to_val x = v ->
  match v with
  | Vbool b => exists h: t = sbool, eq_rect _ _ x _ h = b
  | Vint i => exists h: t = sint, eq_rect _ _ x _ h = i
  | Varr len a => exists h: t = sarr len, eq_rect _ _ x _ h = a
  | Vword ws w => exists h: t = sword ws, eq_rect _ _ x _ h = w
  | Vundef _ _ => False
  end.
Proof. by case: t x => /= > <-; exists erefl. Qed.

Lemma uincl_of_to_val ty v vt :
  of_val ty v = ok vt -> value_uincl (to_val vt) v.
Proof.
  move=> /of_val_typeE; case: ty vt => /= > => [|||[?[?]]] -> //=.
  exact: truncate_word_uincl.
Qed.

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

Lemma val_uincl_refl t v: @val_uincl t t v v.
Proof. by rewrite /val_uincl. Qed.

#[global]
Hint Resolve val_uincl_refl : core.

Lemma val_uincl_alt t1 t2 : @val_uincl t1 t2 =
  match t1, t2 return sem_t t1 -> sem_t t2 -> Prop with
  | sarr len1, sarr len2 => fun v1 v2 => len1 = len2 /\ WArray.uincl v1 v2
  | sword s1, sword s2 => @word_uincl s1 s2
  | t1', t2' => if Sumbool.sumbool_of_bool (t1' == t2') is left h
    then eq_rect _ (fun x => sem_t t1' -> sem_t x -> Prop) eq _ (eqP h)
    else fun _ _ => False
  end.
Proof.
  by case: t1; case: t2 => >; rewrite /val_uincl //=;
    rewrite -(FunctionalExtensionality.eta_expansion (@eq _))
      (Eqdep_dec.UIP_dec stype_eq_dec (eqP _)).
Qed.

Lemma val_uinclEl t1 t2 v1 v2 :
  val_uincl v1 v2 ->
  match t1 return sem_t t1 -> sem_t t2 -> Prop with
  | sarr len => fun v1 v2 => exists (h: t2 = sarr len),
    WArray.uincl v1 (eq_rect _ _ v2 _ h)
  | sword ws => fun v1 v2 => exists ws' (h: t2 = sword ws'),
    word_uincl v1 (eq_rect _ _ v2 _ h)
  | t => fun v1 v2 => exists h: t2 = t, v1 = eq_rect _ _ v2 _ h
  end v1 v2.
Proof.
  by (case: t1 v1 => /=; case: t2 v2 => // >) => [||[]|] *;
    subst; last eexists; exists erefl.
Qed.

Lemma val_uinclE t1 t2 v1 v2 :
  val_uincl v1 v2 ->
  match t2 return sem_t t1 -> sem_t t2 -> Prop with
  | sarr len => fun v1 v2 => exists (h: t1 = sarr len),
    WArray.uincl (eq_rect _ _ v1 _ h) v2
  | sword ws => fun v1 v2 => exists ws' (h: t1 = sword ws'),
    word_uincl (eq_rect _ _ v1 _ h) v2
  | t => fun v1 v2 => exists h: t1 = t, v2 = eq_rect _ _ v1 _ h
  end v1 v2.
Proof.
  by (case: t1 v1 => /=; case: t2 v2 => // >) => [||[]|] *;
    subst; last eexists; exists erefl.
Qed.

Lemma of_val_uincl v v' t z :
  value_uincl v v' -> of_val t v = ok z ->
  exists2 z', of_val t v' = ok z' & val_uincl z z'.
Proof.
  by (case: t z => vt > /of_value_uincl_te h/h{h} => [||[?]|] /of_val_typeE)
    => [->|->|-> ?|[?[? ->]]]; simpl in * => //;
    rewrite ?/val_uincl /=; eexists; eauto using to_arr_id.
Qed.

(* ** Values implicit downcast (upcast is explicit because of signedness)
  * -------------------------------------------------------------------- *)

Definition truncate_defined_val t v := rmap (@to_val t) (of_val t v).

Lemma truncate_defined_val_typeE ty v vt :
  truncate_defined_val ty v = ok vt ->
  match ty with
  | sbool => exists2 b: bool, v = b & vt = b
  | sint => exists2 i: Z, v = i & vt = i
  | sarr len => exists2 a, v = @Varr len a & vt = a
  | sword ws => exists w ws' (w': word ws'),
    [/\ truncate_word ws w' = ok w, v = Vword w' & vt = Vword w]
  end.
Proof.
  rewrite /truncate_defined_val; t_xrbindP; case: v => > /of_valE; case=> ?;
    try (by subst=> /= -> <-; eauto); case=> ? + [?]; subst=> /= ? -> <-.
  by eexists; eexists; eexists; split=> //.
Qed.

Lemma truncate_defined_valE ty v vt :
  truncate_defined_val ty v = ok vt ->
  match v with
  | Vbool b => ty = sbool /\ vt = b
  | Vint i => ty = sint /\ vt = i
  | Varr len a => ty = sarr len /\ vt = a
  | Vword ws w => exists ws' w',
    [/\ ty = sword ws', truncate_word ws' w = ok w' & vt = Vword w']
  | Vundef _ _ => False
  end.
Proof.
  by case: ty => > /truncate_defined_val_typeE[]
    => [|||? [? [? []]]] ? -> -> //; eexists; eexists; split; auto.
Qed.

Lemma truncate_defined_valI ty v vt :
  truncate_defined_val ty v = ok vt ->
  match vt with
  | Vbool b => ty = sbool /\ v = b
  | Vint i => ty = sint /\ v = i
  | Varr len a => ty = sarr len /\ v = a
  | Vword ws w => exists ws' (w': word ws'),
    [/\ ty = sword ws, truncate_word ws w' = ok w & v = Vword w']
  | Vundef _ _ => False
  end.
Proof.
  by case: ty => > /truncate_defined_val_typeE[]
    => [||| ? [? [? []]] ] ? -> -> //;
    eexists; eexists; split; auto.
Qed.

Lemma truncate_defined_val_arr len a :
  truncate_defined_val (sarr len) (@Varr len a) = ok (Varr a).
Proof.
  by rewrite /truncate_defined_val /=
    sumbool_of_boolET (Eqdep_dec.UIP_dec Pos.eq_dec (eqP _)).
Qed.

Lemma truncate_is_defined_val ty v v' :
  truncate_defined_val ty v = ok v' -> is_defined v /\ is_defined v'.
Proof.
  by case: ty => > /truncate_defined_val_typeE[?] => [|||[?[?[_]]]] -> ->.
Qed.

Lemma truncate_defined_val_subtype ty v v' :
  truncate_defined_val ty v = ok v' →
  subtype ty (type_of_val v).
Proof.
  by case: v => > /truncate_defined_valE[] => [|||?[?[+/truncate_wordP[??]]]] => ->.
Qed.

Lemma truncate_defined_val_has_type ty v v' :
  truncate_defined_val ty v = ok v' →
  type_of_val v' = ty.
Proof.
  by case: v' => > /truncate_defined_valI[] => [|||?[?[+/truncate_wordP[??]]]] => ->.
Qed.

Lemma truncate_undefined_val ty t h :
  exists e, truncate_defined_val ty (Vundef t h) = Error e.
Proof. by move: h => /[dup]/is_undef_tE[]-> ?; case: ty; eexists. Qed.

(* ----------------------------------------------------------------------- *)

Lemma value_uincl_truncate_defined ty x y x' :
  value_uincl x y →
  truncate_defined_val ty x = ok x' →
  exists2 y', truncate_defined_val ty y = ok y' & value_uincl x' y'.
Proof.
  case: x => > /value_uinclE+ /truncate_defined_valE => [ + [] | + [] | [?+?[]]
    | [? [? + /word_uincl_truncate h]] [? [? [+ /h{h} h]]] |//] => -> -> ->.
  1,2: by eexists.
  + by eexists; first rewrite /truncate_defined_val /of_val to_arr_id.
  by rewrite /truncate_defined_val /= h /=; eexists=> //=.
Qed.

Lemma truncate_defined_value_uincl t v1 v2 :
  truncate_defined_val t v1 = ok v2 -> value_uincl v2 v1.
Proof.
  by rewrite /truncate_defined_val; case: t; t_xrbindP=> > /of_val_typeE;
    last case=> ? [?+?+]; move=> -> <- //; exact: truncate_word_uincl.
Qed.

Lemma mapM2_truncate_defined_value_uincl tyin vargs1 vargs1' :
  mapM2 ErrType truncate_defined_val tyin vargs1 = ok vargs1' ->
  List.Forall2 value_uincl vargs1' vargs1.
Proof.
  move=> htr.
  have {htr} := mapM2_Forall3 htr.
  elim {vargs1 vargs1'} => //.
  move=> _ v1 v1' _ vargs1 vargs1' /truncate_defined_value_uincl huincl _ ih.
  by constructor.
Qed.

Lemma mapM2_truncate_defined_val tys vs1' vs1 vs2' :
  mapM2 ErrType truncate_defined_val tys vs1' = ok vs1 ->
  List.Forall2 value_uincl vs1' vs2' ->
  exists2 vs2, mapM2 ErrType truncate_defined_val tys vs2' = ok vs2 &
    List.Forall2 value_uincl vs1 vs2.
Proof.
  elim: tys vs1' vs1 vs2' => [ | t tys hrec] [|v1' vs1'] //=.
  + by move => ? ? [<-] /List_Forall2_inv_l ->; eauto.
  move=> vs1 vs2';t_xrbindP => v1 htr vs2 htrs <- /List_Forall2_inv_l [v] [vs] [->] [hv hvs].
  have [v2 -> hv2 /=]:= value_uincl_truncate_defined hv htr.
  by have [vs2'' -> hvs2 /=] := hrec _ _ _ htrs hvs;eauto.
Qed.

Lemma typerel_undef_truncate rel t v : reflexive rel ->
  typerel_undef rel t v -> typerel_undef rel t (rdflt v (truncate_defined_val t v)).
Proof.
  case: Result.rdfltP => [? /[dup]/truncate_is_defined_val/proj2 h
    /truncate_defined_val_has_type <- + _|//].
  by rewrite /typerel_undef h.
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

Lemma vuincl_sopn T ts o vs vs' (v: T) :
  all is_not_sarr ts -> List.Forall2 value_uincl vs vs' ->
  app_sopn ts o vs = ok v -> app_sopn ts o vs' = ok v.
Proof.
  elim: ts o vs vs' => /= [ | t ts Hrec] o [] //.
  + by move => vs' _ /List_Forall2_inv_l -> ->; eauto using List_Forall2_refl.
  move => n vs vs'' /andP [] ht hts /List_Forall2_inv_l [v'] [vs'] [->] {vs''} [/value_uinclE hv hvs].
  t_xrbindP; case: t o ht => [ | | // | sz ] o _ + /of_val_typeE;
    try by simpl=> ??; subst; subst=> /(Hrec _ _ _ hts hvs).
  simpl=> ? [? [? ? /word_uincl_truncate h]]; subst.
  by move: hv => [? [? ? /h]]; subst => /= -> /(Hrec _ _ _ hts hvs).
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
  move: hu => + /to_arrI ?; subst=> -[? -> /WArray.uincl_copy h/h{h}h].
  by rewrite to_arr_id /= h => <-.
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
