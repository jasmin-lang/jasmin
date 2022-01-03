(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

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

Definition undef_b := Vundef sbool refl_equal.
Definition undef_w ws := Vundef (sword ws) refl_equal.

Definition values := seq value.

Definition to_bool v :=
  match v with
  | Vbool b        => ok b
  | Vundef sbool _ => undef_error
  | _              => type_error
  end.

Definition to_int v :=
  match v with
  | Vint z        => ok z
  | Vundef sint _ => undef_error
  | _             => type_error
  end.

Definition truncate_word (s s':wsize) (w:word s') : exec (word s) :=
   if (s <= s')%CMP then ok (zero_extend s w) else type_error.

Lemma truncate_word_u s (a : word s): truncate_word s a = ok a.
Proof. by rewrite /truncate_word cmp_le_refl zero_extend_u. Qed.

Lemma truncate_wordP s1 s2 (w1:word s1) (w2:word s2) :
  truncate_word s1 w2 = ok w1 →
  (s1 <= s2)%CMP /\ w1 = zero_extend s1 w2.
Proof. by rewrite /truncate_word;case:ifP => // Hle []. Qed.

Lemma truncate_word_errP s1 s2 (w: word s2) e :
  truncate_word s1 w = Error e →
  e = ErrType ∧ (s2 < s1)%CMP.
Proof.
by rewrite /truncate_word; case: ifP => // /negbT; rewrite cmp_nle_lt => ? [].
Qed.

Definition to_word (s: wsize) (v: value) : exec (word s) :=
  match v with
  | Vword s' w          => truncate_word s w
  | Vundef (sword s') _ => Error (if (s <= s')%CMP then ErrAddrUndef else ErrType)
  | _                   => type_error
  end.

Notation to_pointer := (to_word Uptr).

Definition to_arr len v : exec (sem_t (sarr len)) :=
  match v with
  | Varr len' t => WArray.cast len t
  | _ => type_error
  end.

Definition type_of_val (v:value) : stype :=
  match v with
  | Vbool _     => sbool
  | Vint  _     => sint
  | Varr n _    => sarr n
  | Vword s _   => sword s
  | Vundef t _  => vundef_type t
  end.

Definition of_val t : value -> exec (sem_t t) :=
  match t return value -> exec (sem_t t) with
  | sbool   => to_bool
  | sint    => to_int
  | sarr n  => to_arr n
  | sword s => to_word s
  end.

Definition to_val t : sem_t t -> value :=
  match t return sem_t t -> value with
  | sbool   => Vbool
  | sint    => Vint
  | sarr n  => @Varr n
  | sword s => @Vword s
  end.

Definition truncate_val (ty: stype) (v: value) : exec value :=
  of_val ty v >>= λ x, ok (to_val x).

Lemma type_of_to_val t (s: sem_t t) : type_of_val (to_val s) = t.
Proof. by case: t s. Qed.

Definition oto_val t : sem_ot t -> value :=
  match t return sem_ot t -> value with
  | sbool => fun ob => if ob is Some b then Vbool b else undef_b
  | x     => @to_val x
  end.

Lemma type_of_oto_val t (s: sem_ot t) : type_of_val (oto_val s) = t.
Proof. by case: t s => //= -[]. Qed.

(* -------------------------------------------------------------------- *)
Definition subtype (t t': stype) :=
  match t with
  | sword w => if t' is sword w' then (w ≤ w')%CMP else false
  | sarr n =>
    if t' is sarr n' then (n <=? n')%Z else false
  | _ => t == t'
  end.

Lemma subtypeE ty ty' :
  subtype ty ty' →
  match ty' with
  | sword sz' => ∃ sz, ty = sword sz ∧ (sz ≤ sz')%CMP
  | sarr n'   => ∃ n, ty = sarr n ∧ (n <= n')%Z
  | _         => ty = ty'
end.
Proof.
  destruct ty; try by move/eqP => <-.
  + by case: ty'=> //= p' /ZleP ?; eauto.
  by case: ty' => //; eauto.
Qed.

Lemma subtypeEl ty ty' :
  subtype ty ty' →
  match ty with
  | sword sz => ∃ sz', ty' = sword sz' ∧ (sz ≤ sz')%CMP
  | sarr n   => ∃ n', ty' = sarr n' ∧ (n <= n')%Z
  | _        => ty' = ty
  end.
Proof.
  destruct ty; try by move/eqP => <-.
  + by case: ty'=> //= p' /ZleP ?; eauto.
  by case: ty' => //; eauto.
Qed.

Lemma subtype_refl x : subtype x x.
Proof. case: x => //= ?;apply Z.leb_refl. Qed.
Hint Resolve subtype_refl : core.

Lemma subtype_trans y x z : subtype x y -> subtype y z -> subtype x z.
Proof.
  case: x => //= [/eqP<-|/eqP<-|n1|sx] //.
  + case: y => //= n2 /ZleP h1;case: z => //= n3 /ZleP h2.
    by apply /ZleP;apply: Z.le_trans h1 h2.
  case: y => //= sy hle;case: z => //= sz;apply: cmp_le_trans hle.
Qed.

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

Lemma value_uincl_int1 z v : value_uincl (Vint z) v -> v = Vint z.
Proof. by case: v => //= ? ->. Qed.

Lemma value_uincl_int ve ve' z :
  value_uincl ve ve' -> to_int ve = ok z -> ve = z /\ ve' = z.
Proof. by case: ve => // [ b' /value_uincl_int1 -> [->]| []//]. Qed.

Lemma value_uincl_bool1 b v : value_uincl (Vbool b) v -> v = Vbool b.
Proof. by case: v => //= ? ->. Qed.

Lemma value_uincl_bool ve ve' b :
  value_uincl ve ve' -> to_bool ve = ok b -> ve = b /\ ve' = b.
Proof. by case: ve => // [ b' /value_uincl_bool1 -> [->]| []//]. Qed.

Lemma value_uincl_word ve ve' sz (w: word sz) :
  value_uincl ve ve' →
  to_word sz ve  = ok w →
  to_word sz ve' = ok w.
Proof.
case: ve ve' => //=;last by case.
move => sz' w' [] // sz1 w1 /andP [] hle /eqP -> /truncate_wordP [] hle'.
by rewrite zero_extend_idem // => -> /=; rewrite /truncate_word (cmp_le_trans hle' hle).
Qed.

Lemma value_uincl_arr ve ve' len (t: WArray.array len) :
  value_uincl ve ve' →
  to_arr len ve  = ok t →
  exists2 t', to_arr len ve' = ok t' & WArray.uincl t t'.
Proof.
case: ve ve' => //=. 
by move=> len' a [] // len1 a1 hle /(WArray.uincl_cast hle) [] a2' [] ??; exists a2'.
Qed.

Lemma value_uincl_undef v ty h : value_uincl v (Vundef ty h) -> exists ty' h', v = Vundef ty' h'.
Proof. case: v => //; eauto. Qed.

Lemma value_uincl_zero_ext sz sz' (w':word sz') : (sz ≤ sz')%CMP ->
  value_uincl (Vword (zero_extend sz w')) (Vword w').
Proof. apply word_uincl_zero_ext. Qed.

(* ------------------------------------------------------------------------------- *) 
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
