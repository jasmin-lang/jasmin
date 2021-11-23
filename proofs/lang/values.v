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

Definition vundef_type (t:stype) :=
  match t with
  | sword _ => sword8
  | sarr _  => sarr 1
  | _       => t
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

(* FIXME : move this in types.v *)
Definition curry A B (n: nat) (f: seq (sem_t A) → B) : sem_prod (nseq n A) B :=
  (fix loop n :=
   match n return seq (sem_t A) → sem_prod (nseq n A) B with
   | 0 => f
   | n'.+1 => λ acc a, loop n' (a :: acc)
   end) n [::].
