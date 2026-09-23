(* * Facts about the language of the safety conditions.

   [safety_cond.v] is in the extraction cone and contains definitions only;
   what is proved about the language, about [mk_sem_op] and about the
   conditions of the library is here. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import safety_cond values.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
(* ** Extensionally equal semantics                                      *)

(* Two extensionally equal semantics satisfy the same properties. *)
Lemma sem_forall_eq {T} (P : T -> Prop) tin (f g : sem_prod tin T) :
  sem_prod_eq tin f g -> sem_forall P tin g -> sem_forall P tin f.
Proof.
by elim: tin f g => /= [f g -> // | t tin ih f g heq hg v]; apply: (ih _ _ (heq v) (hg v)).
Qed.

Lemma sem_prod_eq_refl {T} tin (f : sem_prod tin T) : sem_prod_eq tin f f.
Proof. by elim: tin f => //= t tin ih f v; apply ih. Qed.

Lemma sem_prod_eq_sym {T} tin (f g : sem_prod tin T) :
  sem_prod_eq tin f g -> sem_prod_eq tin g f.
Proof. by elim: tin f g => /= [f g -> // | t tin ih f g h v]; apply: ih (h v). Qed.

Lemma sem_prod_eq_trans {T} tin (f g h : sem_prod tin T) :
  sem_prod_eq tin f g -> sem_prod_eq tin g h -> sem_prod_eq tin f h.
Proof.
by elim: tin f g h => /= [f g h -> // | t tin ih f g h h1 h2 v]; apply: ih (h1 v) (h2 v).
Qed.

(* Extensionally equal semantics are applied to the same arguments with the
   same result. *)
Lemma sem_prod_eq_app_sopn {A} tin (f g : sem_prod tin (exec A)) vs :
  sem_prod_eq tin f g -> app_sopn tin f vs = app_sopn tin g vs.
Proof.
elim: tin f g vs => /= [f g vs -> // | t tin ih f g [ | v vs] //= heq].
by case: of_val => //= x; apply ih.
Qed.

(* -------------------------------------------------------------------- *)
(* ** An operation without condition                                     *)

Lemma mk_semi_aux_id {T} (P : values -> T -> exec T) vs tin (f : sem_prod tin T) :
  (forall vs r, P vs r = ok r) ->
  sem_prod_eq tin (mk_semi_aux P vs tin f) (sem_prod_ok tin f).
Proof. by move=> h; elim: tin vs f => /= [vs f | t tin ih vs f v]; [apply h | apply ih]. Qed.

(* Without condition, [mk_sem_op] is the total semantics. *)
Lemma mk_sem_op_nil tin t err f :
  sem_prod_eq tin (@mk_sem_op tin t [::] err f) (sem_prod_ok tin f).
Proof. by apply: mk_semi_aux_id. Qed.

(* -------------------------------------------------------------------- *)
(* ** What the conditions of the library compute                         *)

Lemma safety_cond_holds_not_zero ws k (vs : values) (w : word ws) :
  nth undef_b vs k = Vword w -> safety_cond_holds vs (sc_not_zero ws k) = (w != 0%w).
Proof.
by move=> h;
  rewrite /safety_cond_holds /sc_not_zero /sc_neqi /sc_toint /= h /= truncate_word_u /=.
Qed.

(* -------------------------------------------------------------------- *)
(* ** Truncation and the types of the conditions                         *)

(* Truncating at [t] does not change how the value is read at a smaller type:
   this is what makes a condition agree on the arguments and on their
   truncation. *)
Lemma truncate_val_to_val t (x : sem_t t) : truncate_val t (to_val x) = ok (to_val x).
Proof. by rewrite /truncate_val of_val_to_val. Qed.

Lemma of_val_subctype_ok t t' (x : sem_t t) :
  subctype t' t -> exists y : sem_t t', of_val t' (to_val x) = ok y.
Proof.
move=> hsub; have [v2] := subctype_truncate_val hsub (truncate_val_to_val x).
by rewrite /truncate_val; case hof: (of_val t' (to_val x)) => [y|e] //= _; exists y.
Qed.

(* The variables of a well-typed condition are among the arguments. *)
Lemma safety_cond_type_below tin c t :
  safety_cond_type tin c = Some t -> safety_cond_below (size tin) c.
Proof.
elim: c t => //=.
+ by move=> k t; case: ifP.
+ move=> o c ih t; case heq: (safety_cond_type tin c) => [t1|] //=; case: ifP => // _ _.
  by apply: ih heq.
+ move=> o c1 ih1 c2 ih2 t.
  case heq1: (safety_cond_type tin c1) => [t1|] //=; case heq2: (safety_cond_type tin c2) => [t2|] //=.
  case: ifP => // _ _.
  by rewrite (ih1 _ heq1) (ih2 _ heq2).
move=> o c1 ih1 c2 ih2 c3 ih3 t.
case heq1: (safety_cond_type tin c1) => [t1|] //=; case heq2: (safety_cond_type tin c2) => [t2|] //=.
case heq3: (safety_cond_type tin c3) => [t3|] //=.
case: ifP => // _ _.
by rewrite (ih1 _ heq1) (ih2 _ heq2) (ih3 _ heq3).
Qed.

(* The interpretation only depends on the arguments the condition reads. *)
Lemma sem_safety_cond_cat (vs vs' : values) c :
  safety_cond_below (size vs) c -> sem_safety_cond (vs ++ vs') c = sem_safety_cond vs c.
Proof.
elim: c => //=.
+ by move=> k hk; rewrite nth_cat hk.
+ by move=> o c ih h; rewrite ih.
+ by move=> o c1 ih1 c2 ih2 /andP [h1 h2]; rewrite ih1 // ih2.
by move=> o c1 ih1 c2 ih2 c3 ih3 /and3P [h1 h2 h3]; rewrite ih1 // ih2 // ih3.
Qed.

Local Opaque wbase.
(* What the x86 division condition computes: the divisor is not zero and the
   quotient fits in a word. *)
Lemma safety_cond_holds_x86_division sz sg (vs : values) (hi lo dv : word sz) :
  nth undef_b vs 0 = Vword hi ->
  nth undef_b vs 1 = Vword lo ->
  nth undef_b vs 2 = Vword dv ->
  safety_cond_holds vs (sc_x86_division sz sg) =
  ~~ match sg with
     | Signed =>
       let dd := wdwords hi lo in
       let d  := wsigned dv in
       let q  := Z.quot dd d in
       ((d == 0)%Z || ((q <? wmin_signed sz)%Z || (q >? wmax_signed sz)%Z))
     | Unsigned =>
       let dd := wdwordu hi lo in
       let d  := wunsigned dv in
       let q  := (dd / d)%Z in
       ((d == 0)%Z || (q >? wmax_unsigned sz)%Z)
     end.
Proof.
move=> h0 h1 h2; rewrite /safety_cond_holds /sc_x86_division /wdwordu /wdwords.
case: sg => /=;
  rewrite /sc_and /sc_not /sc_or /sc_neqi /sc_lti /sc_addi /sc_muli /sc_divi /sc_toint /=
          h0 h1 h2 /= !truncate_word_u /=.
+ by rewrite !negb_or !Z.gtb_ltb.
by rewrite !negb_or !Z.gtb_ltb.
Qed.
Local Transparent wbase.

(* A guarded condition: when the guard is false the condition is not
   required, when it is true it amounts to the guarded condition. *)
Lemma safety_cond_holds_guarded (vs0 vs2 : values) (b : bool) (c : safety_cond) (bb : bool) :
  safety_cond_below (size vs0) c ->
  sem_safety_cond vs0 c = ok (Vbool bb) ->
  safety_cond_holds (vs0 ++ Vbool b :: vs2) (sc_guarded (size vs0) c) = (~~ b) || bb.
Proof.
move=> hb hev; rewrite /safety_cond_holds /sc_guarded /sc_or /sc_not /=.
rewrite nth_cat ltnn subnn /=.
by rewrite (sem_safety_cond_cat (Vbool b :: vs2) hb) hev /=.
Qed.

(* A well-typed condition evaluates to a value on arguments of the announced
   types. *)
Lemma safety_cond_type_ok tin (vs : values) c t :
  List.Forall2 (fun (t : ctype) v => exists x : sem_t t, v = to_val x) tin vs ->
  safety_cond_type tin c = Some t ->
  exists x : sem_t t, sem_safety_cond vs c = ok (to_val x).
Proof.
move=> hall; elim: c t => /=.
1,2: by move=> x t [<-]; eexists.
+ move=> k t; case: ifP => // hk [<-].
  by have [x hx] := Forall2_nth hall cbool undef_b hk; exists x; rewrite hx.
+ move=> o c ih t.
  case heq: (safety_cond_type tin c) => [t1|] //=; case: ifP => // hsub [<-].
  have [x1 ->] := ih _ heq.
  have [y hy] := of_val_subctype_ok x1 hsub.
  by rewrite /= hy /=; eexists.
+ move=> o c1 ih1 c2 ih2 t.
  case heq1: (safety_cond_type tin c1) => [t1|] //=; case heq2: (safety_cond_type tin c2) => [t2|] //=.
  case: ifP => // /andP [hsub1 hsub2] [<-].
  have [x1 ->] := ih1 _ heq1; have [x2 ->] := ih2 _ heq2.
  have [y1 hy1] := of_val_subctype_ok x1 hsub1.
  have [y2 hy2] := of_val_subctype_ok x2 hsub2.
  by rewrite /= hy1 /= hy2 /=; eexists.
move=> o c1 ih1 c2 ih2 c3 ih3 t.
case heq1: (safety_cond_type tin c1) => [t1|] //=; case heq2: (safety_cond_type tin c2) => [t2|] //=.
case heq3: (safety_cond_type tin c3) => [t3|] //=.
case: ifP => // hsub [<-].
have [x1 hx1] := ih1 _ heq1; have [x2 hx2] := ih2 _ heq2.
have [x3 hx3] := ih3 _ heq3.
move: hsub x1 x2 x3 hx1 hx2 hx3; case: o => len /=; rewrite !andbT.
all: move=> /and3P [/eqP <- /eqP <- /eqP <-] x1 x2 x3 -> -> ->.
all: by rewrite /= to_arrK /=; eexists.
Qed.

(* -------------------------------------------------------------------- *)
(* The translation of the previous conditions of the descriptors
   ([sc_of_safe_cond]) preserves their check, on arguments typed as the
   descriptor declares them. *)

(* A word argument that a condition reads is among the arguments. *)
Lemma to_word_nth_lt ws (vs : values) k (w : word ws) :
  to_word ws (nth undef_b vs k) = ok w -> (k < size vs)%nat.
Proof. by case: ltnP => // hk; rewrite nth_default. Qed.

(* The division condition, on the words its arguments truncate to: it is the
   previous [X86Division] on these words. *)
Lemma safety_cond_holds_x86_division_check sz sg (vs : values) (hi lo dv : word sz) :
  to_word sz (nth undef_b vs 0) = ok hi ->
  to_word sz (nth undef_b vs 1) = ok lo ->
  to_word sz (nth undef_b vs 2) = ok dv ->
  safety_cond_holds vs (sc_x86_division sz sg)
  = check_safe_cond [:: Vword hi; Vword lo; Vword dv ] (X86Division sz sg).
Proof.
move=> h0 h1 h2; rewrite /safety_cond_holds /sc_x86_division /= /wdwordu /wdwords.
case: sg => /=;
  rewrite /sc_and /sc_not /sc_or /sc_neqi /sc_lti /sc_addi /sc_muli /sc_divi /sc_toint /=
          h0 h1 h2 /= !truncate_word_u /=.
+ by rewrite !negb_or !Z.gtb_ltb.
by rewrite !negb_or !Z.gtb_ltb.
Qed.

(* When the division condition evaluates, its three arguments are words. *)
Lemma sem_x86_division_ok sz sg (vs : values) v :
  sem_safety_cond vs (sc_x86_division sz sg) = ok v ->
  exists hi lo dv,
    [/\ to_word sz (nth undef_b vs 0) = ok hi
      , to_word sz (nth undef_b vs 1) = ok lo
      & to_word sz (nth undef_b vs 2) = ok dv ].
Proof.
rewrite /sc_x86_division; case: sg => /=.
all: rewrite /sc_and /sc_not /sc_or /sc_neqi /sc_lti /sc_addi /sc_muli /sc_divi /sc_toint /=.
1: t_xrbindP=> ? ? dv hdv ? ? ? ? ? ? ? ? ? ? ? hi hhi ? ? ? ? ? lo hlo *.
2: t_xrbindP=> ? ? dv hdv ? ? ? ? ? ? ? ? ? ? hi hhi ? ? ? ? ? lo hlo *.
all: by exists hi, lo, dv.
Qed.

(* The check of a previous condition is the value of its translation, when
   the translation evaluates (which [safety_cond_type_ok] gives on typed
   arguments). *)
Lemma check_safe_cond_of_safe_cond (vs : values) (c : safe_cond) (bb : bool) :
  sem_safety_cond vs (sc_of_safe_cond c) = ok (Vbool bb) ->
  check_safe_cond vs c = bb.
Proof.
elim: c bb => [ws k | sz sg | ws i j k | ws k z | ws z k | ws k1 k2 z | ws len k | | ws k | k c ih] bb /=.
- (* NotZero *)
  rewrite /sc_not_zero /sc_neqi /sc_toint /=.
  by t_xrbindP=> _ x hx <- /= z1 [<-] <-; rewrite hx /= wunsigned_eqb0.
- (* X86Division *)
  move=> h.
  have [hi [lo [dv [h0 h1 h2]]]] := sem_x86_division_ok h.
  have := safety_cond_holds_x86_division_check sg h0 h1 h2.
  rewrite /safety_cond_holds h => -> /=.
  have := to_word_nth_lt h2.
  case: vs h0 h1 h2 {h} => [|v0 [|v1 [|v2 vs]]] //= h0 h1 h2 _.
  by rewrite h0 h1 h2 /= !truncate_word_u /= take0.
- (* InRangeMod32 *)
  rewrite /sc_in_range_mod32 /sc_in_range /sc_and /sc_lei /sc_modi /sc_toint /=.
  t_xrbindP=> _ _ _ x hx <- /= z3 [<-] <- /= z4 [<-] <- _ _ _ x' hx' <- /= z9 [<-] <- /= z10 [<-] <-.
  move=> /= z11 [<-] z12 [<-] <-.
  by move: hx'; rewrite hx => -[<-].
- (* ULt *)
  rewrite /sc_ult /sc_lti /sc_toint /=.
  by t_xrbindP=> _ x hx <- /= z2 [<-] <-; rewrite hx.
- (* UGe *)
  rewrite /sc_uge /sc_lei /sc_toint /=.
  by t_xrbindP=> _ x hx <- /= z2 [<-] <-; rewrite hx.
- (* UaddLe *)
  rewrite /sc_uadd_le /sc_lei /sc_addi /sc_toint /=.
  by t_xrbindP=> _ _ x1 hx1 <- _ x2 hx2 <- /= z5 [<-] z6 [<-] <- /= z7 [<-] <-; rewrite hx1 hx2.
- (* AllInit *)
  rewrite /sc_all_init /sc_is_arr_init /= (arr_sizeE U8) wsize8 Z.mul_1_l.
  by t_xrbindP=> _ t ht <- <-; rewrite ht /= all_init_getE.
- (* ScFalse *)
  by move=> [->].
- (* IsZero *)
  rewrite /sc_is_zero /sc_eqi /sc_toint /=.
  by t_xrbindP=> _ x hx <- /= z1 [<-] <-; rewrite hx /= wunsigned_eqb0.
(* Guarded *)
rewrite /sc_guarded /sc_or /sc_not /=.
t_xrbindP=> _ b hb <- v2 hv2 /= z2 [<-] z3 hz3 <-.
have ? := to_boolI hz3; subst v2.
rewrite hb /= (ih _ hv2).
by case: b {hb}.
Qed.

(* The safety check of an instruction is unchanged by the translation. *)
Lemma check_safeE tin (vs : values) (safe : seq safe_cond) (err : error) :
  List.Forall2 (fun t v => exists x : sem_t t, v = to_val x) tin vs ->
  all (safety_cond_wt tin) (map sc_of_safe_cond safe) ->
  check_safe vs (map sc_of_safe_cond safe) err
  = (if all (check_safe_cond vs) safe then ok tt else Error err).
Proof.
move=> hall hwt; rewrite /check_safe.
suff -> : all (safety_cond_holds vs) (map sc_of_safe_cond safe) = all (check_safe_cond vs) safe by [].
elim: safe hwt => //= c safe ih /andP [/eqP hty hwt].
have [bb hbb] := safety_cond_type_ok hall hty.
by rewrite (ih hwt) /safety_cond_holds hbb (check_safe_cond_of_safe_cond hbb).
Qed.
