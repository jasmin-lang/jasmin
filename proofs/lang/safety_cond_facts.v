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
  sem_prod_eq tin (@mk_sem_op _ tin t [::] err f) (sem_prod_ok tin f).
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
(* ** Checking the conditions                                            *)

Lemma check_safe_ok {sm : SemMode} vs safe err :
  all (safety_cond_holds vs) safe -> check_safe vs safe err = ok tt.
Proof. by rewrite /check_safe => ->; case: is_total. Qed.

(* -------------------------------------------------------------------- *)
(* ** Conditions on truncated arguments                                  *)

(* Interpreting a well-typed condition on the arguments or on their truncation
   at [tin] gives the same result (up to truncation of the result). *)
Lemma sem_safety_cond_truncate tin vs vs' :
  mapM2 ErrType truncate_val tin vs = ok vs' ->
  forall c t, safety_cond_type tin c = Some t ->
  match sem_safety_cond vs c with
  | Ok v => exists2 v'', sem_safety_cond vs' c = ok v'' & truncate_val t v = ok v''
  | Error e => sem_safety_cond vs' c = Error e
  end.
Proof.
move=> /mapM2_Forall3 htr c.
elim: c => /=.
1,2: by move=> x t [<-]; eexists.
+ move=> n t; case: ifP => // hn [<-]; eexists; first reflexivity.
  by apply: (Forall3_nth htr).
+ move=> o c ih t; case heq: (safety_cond_type tin c) => [t1|] //; case: ifP => // hsub [<-].
  have {ih} := ih _ heq; case: (sem_safety_cond vs c) => [v | e] /=; last by move=> ->.
  move=> [v'' -> htr'] /=; rewrite (of_val_truncate_val hsub htr').
  by case: (of_val _ v) => //= x; eexists; first reflexivity; apply truncate_val_to_val.
+ move=> o c1 ih1 c2 ih2 t.
  case heq1: (safety_cond_type tin c1) => [t1|] //; case heq2: (safety_cond_type tin c2) => [t2|] //.
  case: ifP => // /andP [hsub1 hsub2] [<-].
  have {ih1} := ih1 _ heq1; case: (sem_safety_cond vs c1) => [v1 | e] /=; last by move=> ->.
  move=> [v1'' -> htr1] /=.
  have {ih2} := ih2 _ heq2; case: (sem_safety_cond vs c2) => [v2 | e] /=; last by move=> ->.
  move=> [v2'' -> htr2] /=.
  rewrite (of_val_truncate_val hsub1 htr1) (of_val_truncate_val hsub2 htr2).
  case: (of_val _ v1) => //= x1; case: (of_val _ v2) => //= x2.
  by eexists; first reflexivity; apply truncate_val_to_val.
move=> o c1 ih1 c2 ih2 c3 ih3 t.
case heq1: (safety_cond_type tin c1) => [t1|] //; case heq2: (safety_cond_type tin c2) => [t2|] //.
case heq3: (safety_cond_type tin c3) => [t3|] //.
case: ifP => // hsub [<-].
have {ih1} := ih1 _ heq1; case: (sem_safety_cond vs c1) => [v1 | e] /=; last by move=> ->.
move=> [v1'' -> htr1] /=.
have {ih2} := ih2 _ heq2; case: (sem_safety_cond vs c2) => [v2 | e] /=; last by move=> ->.
move=> [v2'' -> htr2] /=.
have {ih3} := ih3 _ heq3; case: (sem_safety_cond vs c3) => [v3 | e] /=; last by move=> ->.
move=> [v3'' -> htr3] /=.
move: hsub; case: o => len /=; rewrite andbT => /and3P [/eqP ? /eqP ? /eqP ?]; subst t1 t2 t3.
all: move: htr1 htr2 htr3 => /truncate_val_typeE [a -> ->] /truncate_val_typeE [i2 -> ->]
       /truncate_val_typeE [i3 -> ->] /=.
all: by rewrite to_arrK /=; eexists.
Qed.

Lemma safety_cond_holds_truncate tin vs vs' c :
  mapM2 ErrType truncate_val tin vs = ok vs' ->
  safety_cond_wt tin c ->
  safety_cond_holds vs' c = safety_cond_holds vs c.
Proof.
move=> htr /eqP hwt; have := sem_safety_cond_truncate htr hwt.
rewrite /safety_cond_holds; case: (sem_safety_cond vs c) => [v | e] //=; last by move=> ->.
by move=> [v'' -> /truncate_val_typeE [b -> ->]].
Qed.

Lemma all_safety_cond_holds_truncate tin vs vs' safe :
  mapM2 ErrType truncate_val tin vs = ok vs' ->
  all (safety_cond_wt tin) safe ->
  all (safety_cond_holds vs') safe = all (safety_cond_holds vs) safe.
Proof.
move=> htr; elim: safe => //= c safe ih /andP [hc hall].
by rewrite (safety_cond_holds_truncate htr hc) ih.
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

(* -------------------------------------------------------------------- *)
(* ** The conditions of the array accesses                               *)

Lemma safety_cond_holds_arr_aligned al aa ws k (vs : values) (i : Z) :
  nth undef_b vs k = Vint i ->
  safety_cond_holds vs (sc_arr_aligned al aa ws k) = is_aligned_if al (i * mk_scale aa ws)%Z ws.
Proof.
move=> h; rewrite /sc_arr_aligned.
case: ifPn => [ | ]; last first.
+ rewrite negb_or => /andP [hal haa].
  case: al hal => [// | _]; case: aa haa => [_ | //].
  rewrite /safety_cond_holds /sc_eqi /sc_modi /sc_arr_scaled /sc_muli /= h /=.
  by rewrite is_alignE WArray.p_to_zE.
case: al => [_ | ] /=; first by [].
by move=> /eqP ->; rewrite WArray.is_align_scale.
Qed.

Lemma safety_cond_holds_arr_in_bound len aa ws k size (vs : values) (i : Z) :
  nth undef_b vs k = Vint i ->
  safety_cond_holds vs (sc_arr_in_bound len aa ws k size)
  = ((0 <=? i * mk_scale aa ws) && (i * mk_scale aa ws + size <=? len))%Z.
Proof.
by move=> h;
  rewrite /safety_cond_holds /sc_arr_in_bound /sc_and /sc_lei /sc_addi /sc_arr_scaled
          /sc_muli /= h.
Qed.

Lemma safety_cond_holds_arr_init len aa ws ka k size (vs : values)
    (a : WArray.array len) (i : Z) :
  nth undef_b vs ka = Varr a ->
  nth undef_b vs k = Vint i ->
  safety_cond_holds vs (sc_arr_init len aa ws ka k size)
  = all (WArray.is_init a) (ziota (i * mk_scale aa ws)%Z size).
Proof.
move=> ha hi.
by rewrite /safety_cond_holds /sc_arr_init /sc_is_arr_init /sc_arr_scaled /sc_muli /=
           ha hi /= arr_sizeE wsize8 Z.mul_1_l to_arrK.
Qed.

(* A partial access succeeds exactly when its conditions hold, and it then
   returns what the total access returns. *)
Lemma getE (len : Z) al aa ws (a : WArray.array len) (i : Z) w :
  WArray.get (sm := partial) al aa ws a i = ok w
  <-> check_safe_seq [:: Varr a; Vint i] (sc_get len al aa ws) = ok tt
      /\ WArray.get (sm := total) al aa ws a i = ok w.
Proof.
rewrite /WArray.get.
have hvc : (check_safe_seq [:: Varr a; Vint i] (sc_get len al aa ws) = ok tt)
           <-> validr a al (i * mk_scale aa ws)%Z ws.
+ rewrite /check_safe_seq /sc_get /= /assert
          (@safety_cond_holds_arr_aligned al aa ws 1 [:: Varr a; Vint i] i erefl)
          (@safety_cond_holds_arr_in_bound len aa ws 1 (wsize_size ws) [:: Varr a; Vint i] i erefl)
          (@safety_cond_holds_arr_init len aa ws 0 1 (wsize_size ws) [:: Varr a; Vint i] a i
             erefl erefl)
          WArray.validr_validw_init WArray.validw_in_range /WArray.in_range.
  by case: is_aligned_if; case: (0 <=? i * mk_scale aa ws)%Z;
     case: (i * mk_scale aa ws + wsize_size ws <=? len)%Z; case: all.
split.
+ by move=> /read_partialE [] /hvc hch ->.
by move=> [] /hvc hval hr; apply/read_partialE.
Qed.

Lemma setE (len : Z) al aa ws (a : WArray.array len) (i : Z) (v : word ws) a' :
  WArray.set (sm := partial) a al aa i v = ok a'
  <-> check_safe_seq [:: Varr a; Vint i; Vword v] (sc_set len al aa ws) = ok tt
      /\ WArray.set (sm := total) a al aa i v = ok a'.
Proof.
rewrite /WArray.set.
have hvc : (check_safe_seq [:: Varr a; Vint i; Vword v] (sc_set len al aa ws) = ok tt)
           <-> validw a al (i * mk_scale aa ws)%Z ws.
+ rewrite /check_safe_seq /sc_set /= /assert
          (@safety_cond_holds_arr_aligned al aa ws 1 [:: Varr a; Vint i; Vword v] i erefl)
          (@safety_cond_holds_arr_in_bound len aa ws 1 (wsize_size ws)
             [:: Varr a; Vint i; Vword v] i erefl)
          WArray.validw_in_range /WArray.in_range.
  by case: is_aligned_if; case: (0 <=? i * mk_scale aa ws)%Z;
     case: (i * mk_scale aa ws + wsize_size ws <=? len)%Z.
split.
+ by move=> /write_partialE [] /hvc hch ->.
by move=> [] /hvc hval hr; apply/write_partialE.
Qed.

Lemma get_subE (lena : Z) aa ws n (a : WArray.array lena) (i : Z) b :
  WArray.get_sub (sm := partial) aa ws n a i = ok b
  <-> check_safe_seq [:: Varr a; Vint i] (sc_get_sub lena aa ws n) = ok tt
      /\ WArray.get_sub (sm := total) aa ws n a i = ok b.
Proof.
rewrite /WArray.get_sub /check_safe_seq /sc_get_sub /= /assert
        (@safety_cond_holds_arr_in_bound lena aa ws 1 (arr_size ws n) [:: Varr a; Vint i] i erefl).
by case: (_ && _); split => // -[].
Qed.

Lemma set_subE (lena : Z) aa ws n (a : WArray.array lena) (i : Z)
    (b : WArray.array (arr_size ws n)) a' :
  WArray.set_sub (sm := partial) aa a i b = ok a'
  <-> check_safe_seq [:: Varr a; Vint i; Varr b] (sc_set_sub lena aa ws n) = ok tt
      /\ WArray.set_sub (sm := total) aa a i b = ok a'.
Proof.
rewrite /WArray.set_sub /check_safe_seq /sc_set_sub /= /assert
        (@safety_cond_holds_arr_in_bound lena aa ws 1 (arr_size ws n)
           [:: Varr a; Vint i; Varr b] i erefl).
by case: (_ && _); split => // -[].
Qed.
