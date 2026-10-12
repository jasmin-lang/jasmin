(* * Syntax and semantics of the Jasmin source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import xseq.
Require Export warray_ word sem_type.
Import Utf8.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

(* ----------------------------------------------------------- *)

Definition is_undef_t (t: ctype) := [|| t == cbool, t == cint | t == cword U8].

Lemma is_undef_tE t : is_undef_t t -> [\/ t = cbool, t = cint | t = cword U8].
Proof. by case/or3P => /eqP; firstorder. Qed.

Definition undef_t t := if is_cword t then cword U8 else t.
Arguments undef_t _ : clear implicits.

Lemma is_undef_t_undef_t t : is_not_carr t -> is_undef_t (undef_t t).
Proof. by case: t. Qed.

Lemma subctype_undef_tP t1 t2 :
  subctype (undef_t t1) t2 <-> undef_t t1 = undef_t t2.
Proof. by case: t1 => [ | | len1 | ws1]; case: t2 => [ | | len2 | ws2] //=; split => /eqP. Qed.

Lemma undef_t_subctype ty : subctype (undef_t ty) ty.
Proof. by rewrite subctype_undef_tP. Qed.
#[global] Hint Resolve undef_t_subctype : core.

(* ** Values
  * -------------------------------------------------------------------- *)

Variant value : Type :=
  | Vbool  :> bool -> value
  | Vint   :> Z    -> value
  | Varr   : forall len, WArray.array len -> value
  | Vword  : forall s, word s -> value
  | Vundef : forall (t:ctype), is_undef_t t -> value.
Arguments Vundef _ _ : clear implicits.

Notation undef_b := (Vundef cbool erefl).
Notation undef_i := (Vundef cint erefl).
Notation undef_w := (Vundef (cword U8) erefl).

Definition undef_v t (h: is_not_carr t) :=
  Vundef (undef_t t) (is_undef_t_undef_t h).
Arguments undef_v _ _ : clear implicits.

Definition undef_addr t :=
  match t with
  | carr n => Varr (WArray.empty n)
  | t0 => undef_v t0 erefl
  end.

Definition values := seq value.

Definition is_defined v := if v is Vundef _ _ then false else true.

(* ** Type of values
  * -------------------------------------------------------------------- *)

Definition type_of_val v :=
  match v with
  | Vbool _ => cbool
  | Vint  _ => cint
  | Varr n _ => carr n
  | Vword s _ => cword s
  | Vundef t _ => t
  end.

Definition check_ty_val (ty:ctype) (v:value) :=
  subctype ty (type_of_val v).

Definition is_word v := is_cword (type_of_val v).

Definition DB wdb v :=
  ~~wdb || (is_defined v || (type_of_val v == cbool)).

(* ** Test for extension of values
  * -------------------------------------------------------------------- *)

Definition value_uincl (v1 v2:value) :=
  match v1, v2 with
  | Vbool b1, Vbool b2 => b1 = b2
  | Vint n1, Vint n2   => n1 = n2
  | Varr n1 t1, Varr n2 t2 => WArray.uincl t1 t2
  | Vword sz1 w1, Vword sz2 w2 => word_uincl w1 w2
  | Vundef t _, _ => subctype t (type_of_val v2)
  | _, _ => False
  end.

Definition values_uincl := List.Forall2 value_uincl.

Lemma value_uinclE v1 v2 :
  value_uincl v1 v2 →
  match v1 with
  | Varr n1 t1 => exists2 t2, v2 = @Varr n1 t2 & WArray.uincl t1 t2
  | Vword sz1 w1 => exists sz2 w2, v2 = @Vword sz2 w2 /\ word_uincl w1 w2
  | Vundef t _ => subctype t (type_of_val v2)
  | _ => v2 = v1
  end.
Proof.
  case: v1 => >; case: v2 => > //= h; subst; eauto.
  have ?:= WArray.uincl_len h; subst; eauto.
Qed.

Lemma value_uincl_refl v: value_uincl v v.
Proof. by case: v => //=. Qed.
#[global]Hint Resolve value_uincl_refl : core.

Lemma value_uincl_subctype v1 v2 :
  value_uincl v1 v2 ->
  subctype (type_of_val v1) (type_of_val v2).
Proof.
  case: v1 => [||||t h] > /value_uinclE; try by move=> ->.
  + by case=> ?->.
  by move=> [? [? [-> ]]] /= /andP [].
Qed.

Lemma value_uincl_trans v2 v1 v3 :
  value_uincl v1 v2 -> value_uincl v2 v3 -> value_uincl v1 v3.
Proof.
  case: v1 => > /value_uinclE; try by move=> -> /value_uinclE ->.
  + by move=> [? -> /WArray.uincl_trans h] /value_uinclE [? -> /h].
  + by move=> [? [? [-> /word_uincl_trans h]]] /value_uinclE [? [? [-> /h]]].
  by move=> h /value_uincl_subctype; apply: subctype_trans.
Qed.

Lemma values_uincl_refl {va} : values_uincl va va.
Proof. apply (List_Forall2_refl va value_uincl_refl). Qed.
#[global]Hint Resolve values_uincl_refl : core.

(* ** Conversions between values and sem_t
  * -------------------------------------------------------------------- *)

Definition to_bool v :=
  match v with
  | Vbool b => ok b
  | Vundef cbool _ => undef_error
  | _ => type_error
  end.

Lemma to_boolI x b : to_bool x = ok b → x = b.
Proof. by case: x => //= => [? [->] | []]. Qed.

Definition to_int v :=
  match v with
  | Vint i => ok i
  | Vundef cint _ => undef_error
  | _ => type_error
  end.

Lemma to_intI v n: to_int v = ok n → v = n.
Proof. by case: v => //= [? [<-] | [] ]. Qed.

Definition to_arr len v : exec (sem_t (carr len)) :=
  match v with
  | Varr len' t => WArray.cast len t
  | _ => type_error
  end.

Lemma to_arrI n v t : to_arr n v = ok t -> v = Varr t.
Proof.
  case: v => //= n' t' /[dup] /WArray.cast_len ?; subst n'.
  by rewrite WArray.castK => -[<-].
Qed.

Definition to_word s v : exec (word s) :=
  match v with
  | Vword s' w => truncate_word s w
  | Vundef (cword s') _ => undef_error
  | _ => type_error
  end.

Notation to_pointer := (to_word Uptr).

Lemma to_wordI sz v w : to_word sz v = ok w ->
  exists sz' (w': word sz'), v = Vword w' /\ truncate_word sz w' = ok w.
Proof. by case: v => //=; eauto; case => //. Qed.

(* ----------------------------------------------------------------------- *)

Definition of_val t : value -> exec (sem_t t) :=
  match t return value -> exec (sem_t t) with
  | cbool => to_bool
  | cint => to_int
  | carr n => to_arr n
  | cword s => to_word s
  end.

Lemma of_val_typeE t v v' : of_val t v = ok v' ->
  match t, v' with
  | carr len, vt => v = Varr vt
  | cword ws, vt => exists ws' (w: word ws'),
    v = Vword w /\ truncate_word ws w = ok vt
  | cbool, vt => v = vt
  | cint, vt => v = vt
  end.
Proof.
  case: t v' => /= >.
  + exact: to_boolI.
  + exact: to_intI.
  + exact: to_arrI.
  exact: to_wordI.
Qed.

Lemma of_valE t v v' : of_val t v = ok v' ->
  match v with
  | Vbool b => exists h: t = cbool, eq_rect _ _ v' _ h = b
  | Vint i => exists h: t = cint, eq_rect _ _ v' _ h = i
  | Varr len a => exists (h: t = carr len), eq_rect _ _ v' _ h = a
  | Vword ws w => exists ws' (h: t = cword ws') w',
    truncate_word ws' w = ok w' /\ eq_rect _ _ v' _ h = w'
  | Vundef t h => False
  end.
Proof.
  by case: t v' => > /of_val_typeE; try (simpl=> ->; exists erefl; eauto);
    simpl=> > [? [? [-> ]]]; eexists; exists erefl; eauto.
Qed.

(* can be use to shorten proofs drastically, see psem/vuincl_sem_sop1 *)
Lemma of_value_uincl_te ty v v' vt :
  value_uincl v v' -> of_val ty v = ok vt ->
  match ty as ty return sem_t ty -> Prop with
  | carr n => fun vt =>
    exists2 vt', of_val (carr n) v' = ok vt' & WArray.uincl vt vt'
  | _ => fun _ => of_val ty v' = ok vt
  end vt.
Proof.
  case: v => > /value_uinclE + /of_valE //; try (by move=> -> [? ]; subst=> /= ->).
  + by move: vt => + [? -> +] [?] => vt ??; subst => /=; rewrite WArray.castK; eauto.
  move: vt => + [? [? [-> +]]] [? [? [? []]]]; subst=> /= _ ++ ->.
  exact: word_uincl_truncate.
Qed.

(* ----------------------------------------------------------------------- *)

Definition to_val t : sem_t t -> value :=
  match t return sem_t t -> value with
  | cbool => Vbool
  | cint => Vint
  | carr n  => @Varr n
  | cword s => @Vword s
  end.

Definition oto_val t : sem_ot t -> value :=
  match t return sem_ot t -> value with
  | cbool => fun ob => if ob is Some b then Vbool b else undef_b
  | x => @to_val x
  end.

Definition val_uincl (t1 t2:ctype) (v1:sem_t t1) (v2:sem_t t2) :=
  value_uincl (to_val v1) (to_val v2).

Lemma val_uincl_refl t v: @val_uincl t t v v.
Proof. by rewrite /val_uincl. Qed.
#[global]
Hint Resolve val_uincl_refl : core.

Lemma val_uincl_of_val ty v v' vt :
  value_uincl v v' -> of_val ty v = ok vt ->
  exists2 vt', of_val ty v' = ok vt' & val_uincl vt vt'.
Proof.
  case: v => > /value_uinclE + /of_valE //;
    try (by move=> -> [? ]; subst => /= ->; eauto).
  + by move=> [???] [??]; subst => /=; rewrite WArray.castK; eauto.
  move: vt => + [? [? [-> +]]] [s [x [? []]]]; subst=> /= _ ++ ->.
  move=> /word_uincl_truncate h/h{h} ->; eauto.
Qed.

(* ** Values implicit downcast (upcast is explicit because of signedness)
  * -------------------------------------------------------------------- *)

Definition truncate_val (ty: ctype) (v: value) : exec value :=
  of_val ty v >>= λ x, ok (to_val x).

(* ----------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------- *)

Fixpoint list_ltuple (ts:list ctype) : sem_tuple ts -> values :=
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

(* ----------------------------------------------------------------------- *)

Definition app_sopn := app_sopn of_val.

Arguments app_sopn {A} ts _ _.

Definition app_sopn_v tin tout (semi: sem_prod tin (exec (sem_tuple tout))) vs :=
  Let t := app_sopn _ semi vs in
  ok (list_ltuple t).

Lemma vuincl_sopn T ts o vs vs' (v: T) :
  all is_not_carr ts -> values_uincl vs vs' ->
  app_sopn ts o vs = ok v -> app_sopn ts o vs' = ok v.
Proof.
  elim: ts o vs vs' => /= [ | t ts Hrec] o [] //.
  + by move => vs' _ /List_Forall2_inv_l -> ->; eauto using List_Forall2_refl.
  move => n vs vs'' /andP [] ht hts /List_Forall2_inv_l [v'] [vs'] [->] {vs''} [/value_uinclE hv hvs].
  t_xrbindP; case: t o ht => [ | | // | sz ] o _ + /of_val_typeE;
    try by simpl=> ??; subst; subst=> /(Hrec _ _ _ hts hvs).
  simpl=> ? [? [? [? /word_uincl_truncate h]]]; subst.
  by move: hv => [? [? [? /h]]]; subst => /= -> /(Hrec _ _ _ hts hvs).
Qed.

Lemma vuincl_app_sopn_v_eq tin tout (semi: sem_prod tin (exec (sem_tuple tout))) :
  all is_not_carr tin -> forall vs vs' v, values_uincl vs vs' ->
  app_sopn_v semi vs = ok v -> app_sopn_v semi vs' = ok v.
Proof.
  rewrite /app_sopn_v => hall vs vs' v hu; t_xrbindP => v' h1 h2.
  by rewrite (vuincl_sopn hall hu h1) /= h2.
Qed.

Lemma vuincl_app_sopn_v tin tout (semi: sem_prod tin (exec (sem_tuple tout))) :
  all is_not_carr tin ->
  forall vs vs' v, values_uincl vs vs' ->
  app_sopn_v semi vs = ok v ->
  exists2 v' : values, app_sopn_v semi vs' = ok v' & values_uincl v v'.
Proof.
  move=> /vuincl_app_sopn_v_eq h ?? v /h{}h/h{}h.
  by exists v => //; exact: List_Forall2_refl.
Qed.

Section FORALL.
  Context  (T:Type) (P:T -> Prop).

  Definition mk_forall (l:seq ctype) : sem_prod l (exec T) -> Prop :=
    sem_forall (fun o => forall t, o = ok t -> P t) l.

  Lemma mk_forallP l f vargs t : @mk_forall l f -> app_sopn l f vargs = ok t -> P t.
  Proof.
    elim: l vargs f => [ | a l hrec] [ | v vs] //= f hall; first by apply hall.
    by t_xrbindP => w _;apply: hrec.
  Qed.

  Context (P2:T -> T -> Prop).

  Fixpoint mk_forall_ex (l:seq ctype) : sem_prod l (exec T) -> sem_prod l (exec T) -> Prop :=
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

  Fixpoint mk_forall2 (l:seq ctype) : sem_prod l (exec T) -> sem_prod l (exec T) -> Prop :=
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

Fixpoint sc_needed_args (sc : safe_cond) : nat :=
  match sc with
  | NotZero _ k | InRangeMod32 _ _ _ k | AllInit _ _ k | ULt _ k _ | UGe _ _ k
  | IsZero _ k => S k
  | UaddLe _ k1 k2 _ => S (if ssrnat.leq k1 k2 then k2 else k1)
  | X86Division sz sign => 3
  | ScFalse => 0
  | Guarded k sc => ssrnat.maxn (S k) (sc_needed_args sc)
  end.

(* The conditions of an instruction, decided on the values of its arguments:
   a condition is vacuously true when the argument it speaks about cannot be
   read at the expected type. *)
Fixpoint check_safe_cond (vs : values) (sc : safe_cond) : bool :=
  match sc with
  | NotZero ws k =>
    if to_word ws (nth undef_b vs k) is Ok w then w != 0%w else true
  | X86Division sz sign =>
    if mapM (to_word sz) (take 3 vs) is Ok [:: hi; lo; dv] then
      match sign with
      | Signed =>
        let dd := wdwords hi lo in
        let dv := wsigned dv in
        let q  := (Z.quot dd dv)%Z in
        let ov := (q <? wmin_signed sz)%Z || (q >? wmax_signed sz)%Z in
        ~~ ((dv == 0)%Z || ov)
      | Unsigned =>
        let dd := wdwordu hi lo in
        let dv := wunsigned dv in
        let q  := (dd  /  dv)%Z in
        let ov := (q >? wmax_unsigned sz)%Z in
        ~~ ((dv == 0)%Z || ov)
      end
    else true
  | InRangeMod32 ws i j k =>
    if to_word ws (nth undef_b vs k) is Ok w
    then (i <=? (wunsigned w) mod 32)%Z && ((wunsigned w) mod 32 <=? j)%Z
    else true
  | ULt ws k z =>
    if to_word ws (nth undef_b vs k) is Ok w then (wunsigned w <? z)%Z else true
  | UGe ws z k =>
    if to_word ws (nth undef_b vs k) is Ok w then (z <=? wunsigned w)%Z else true
  | UaddLe ws k1 k2 z =>
    if to_word ws (nth undef_b vs k1) is Ok w1 then
      if to_word ws (nth undef_b vs k2) is Ok w2
      then (wunsigned w1 + wunsigned w2 <=? z)%Z else true
    else true
  | AllInit ws n k =>
    if to_arr (arr_size ws n) (nth undef_b vs k) is Ok t
    then all (fun i => is_ok (WArray.get Unaligned AAscale ws t i)) (ziota 0 n)
    else true
  | ScFalse => false
  | IsZero ws k =>
    if to_word ws (nth undef_b vs k) is Ok w then w == 0%w else true
  | Guarded k sc =>
    if to_bool (nth undef_b vs k) is Ok true then check_safe_cond vs sc else true
  end.

Definition value_eqb (v1 v2:value) :=
  match v1, v2 with
  | Vbool b1, Vbool b2 => b1 == b2
  | Vint n1, Vint n2   => n1 == n2
  | Vword sz1 w1, Vword sz2 _ =>
    if sz1 == sz2 then
      match to_word sz1 v2 with
      | Ok w2 => w1 == w2
      | _ => false
      end
    else false
  | Vundef t1 _, Vundef t2 _ => t1 == t2
  | _, _ => false
  end.


