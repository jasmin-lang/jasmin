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
Require Export array expr gen_map low_memory.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module WArray.

  Definition arr_size (ws:wsize) (s:positive)  := 
     (wsize_size ws * s)%Z.

  Record array (s:positive)  := 
    { arr_data : Mz.t u8 }.

  Definition empty (s:positive) : array s := 
    {| arr_data := Mz.empty _ |}.

  Local Notation pointer := [eqType of Z].

  Definition add x y := (x + y)%Z.
  Definition sub x y := (x - y)%Z.

  Section CM.
    Variable (s:positive).

    Definition uget (m:array s) (i:pointer) := 
      odflt 0%R (Mz.get m.(arr_data) i).
 
    Definition uset (m:array s) (i:pointer) (v:u8) : array s := 
      {| arr_data := Mz.set m.(arr_data) i v |}.

    Definition in_range (p:pointer) (ws:wsize) := 
      ((0 <=? p) && (p + wsize_size ws <=? s))%Z.

    Lemma in_rangeP p ws: 
      reflect (0 <= p /\ p + wsize_size ws <= s)%Z (in_range p ws).
    Proof.
      rewrite /in_range; case: andP => h; constructor; move: h; rewrite !zify; Psatz.nia.
    Qed.

    Definition validw (m:array s) (p:pointer) (ws:wsize) : exec unit := 
      assert (in_range p ws) ErrOob.

    Definition validr (m:array s) (p:pointer) (ws:wsize) := 
      Let _ := validw m p ws in
      assert (all (fun i => Mz.get m.(arr_data) (p+i)%Z != None) (ziota 0 (wsize_size ws))) 
             ErrAddrInvalid.

    Lemma add_sub p k: add p (sub k p) = k.
    Proof. rewrite /add /sub; ring. Qed.

    Lemma sub_add m p sw i t: validw m p sw = ok t -> (0 <= i < wsize_size sw)%Z -> sub (add p i) p = i.
    Proof. move=> ?;rewrite /add /sub => _; ring. Qed.

    Lemma add_0 p: add p 0 = p.
    Proof. rewrite /add; ring. Qed.

    Lemma validw_uset m p v p' sw: validw (uset m p v) p' sw = validw m p' sw.
    Proof. done. Qed.

    Lemma validw8 m2 m1 p sw i t: 
      (0 <= i < wsize_size sw)%Z ->
      validw m1 p sw = ok t -> validw m2 (add p i) U8 = ok tt.
    Proof.
      move=> hi;rewrite /validw /assert; case: in_rangeP => // h1 _. 
      by case: in_rangeP => //; rewrite /wsize_size /add; Psatz.nia.
    Qed.

    Lemma validrP m p sw i t:
      validr m p sw = ok t ->
      (0 <= i < wsize_size sw)%Z ->  
      validr m (add p i) U8 = ok t.
    Proof.
      rewrite /validr /assert /=; t_xrbindP.
      case: allP => //= hin ? hv [<-] hi.
      by rewrite Z.add_0_r (validw8 _ hi hv) hin // in_ziota !zify.
    Qed.

    Lemma validw_validr m p sw i v t k:
      validw m p sw = ok t -> 
      (0 <= i < wsize_size sw)%Z ->
      validr (uset m (add p i) v) k U8 = if add p i == k then ok t else validr m k U8.
    Proof.
      case: t; rewrite /validr /= Z.add_0_r /validw /assert /add.
      case: in_rangeP => //= hw _ hi.
      case: in_rangeP; rewrite /= /wsize_size => h.
      + by rewrite Mz.setP !andbT; case: (_ =P k). 
      case: eqP => //; Psatz.nia.
    Qed.

    Lemma usetP m z1 z2 v:
      uget (uset m z1 v) z2 = if z1 == z2 then v else uget m z2.
    Proof. by rewrite /uget /uset /= Mz.setP; case: eqP. Qed.

    Global Instance array_CM : coreMem (array s) pointer := 
      CoreMem add_sub sub_add add_0 validw_uset 
        validrP validw_validr usetP.
 
  End CM.

  Definition get len ws (a:array len) (p:Z) :=
    CoreMem.read a (p * wsize_size ws)%Z ws.
 
  Definition set {len ws} (a:array len) p (v:word ws) : exec (array len) :=   
    CoreMem.write a (p * wsize_size ws)%Z v.

  Definition cast len len' (a:array len) : result error (array len') :=
    if (len' <=? len)%Z then ok {| arr_data := a.(arr_data) |}
    else type_error.

  Definition uincl {len1 len2} (a1 : array len1) (a2 : array len2) :=
    (len1 <= len2)%Z ∧
    ∀ i v, (0 <= i < Zpos len1)%Z -> 
       Mz.get a1.(arr_data) i = Some v → Mz.get a2.(arr_data) i = Some v.

  Lemma uincl_validw {len1 len2} (a1 : array len1) (a2 : array len2) ws i t :
    uincl a1 a2 -> validw a1 i ws = ok t -> validw a2 i ws = ok tt.
  Proof.
    move=> [h1 h2]; rewrite /validw => /assertP/in_rangeP hi.
    case: in_rangeP => //; nia.
  Qed.

  Lemma uincl_validr {len1 len2} (a1 : array len1) (a2 : array len2) ws i t :
    uincl a1 a2 -> validr a1 i ws = ok t -> validr a2 i ws = ok tt.
  Proof.
    move=> [h1 h2]; rewrite /validr /validw; t_xrbindP => t1. 
    case: in_rangeP => //= hi1 _ {t1} /assertP /allP h.
    case: in_rangeP => //= hi2; last by nia.
    case: allP => // -[] k hk; have := h _ hk.
    move: hk; rewrite in_ziota !zify Z.add_0_l => hk.
    by case: Mz.get (h2 (i+k)%Z) => //= v /(_ _ _ erefl) -> //; nia.
  Qed.

  Lemma uincl_get {len1 len2} (a1 : array len1) (a2 : array len2) ws i w :
    uincl a1 a2 ->
    get ws a1 i = ok w ->
    get ws a2 i = ok w.
  Proof.
    rewrite /get /CoreMem.read /=; t_xrbindP => hu t hr.
    have -> := uincl_validr hu hr => /= <-; do 2 f_equal.
    rewrite /CoreMem.uread; apply eq_map_ziota; rewrite Z.add_0_l => k hk /=.
    rewrite /add /uget; case: hu => h1 /(_ (i * wsize_size ws + k)%Z).
    have := validrP hr hk; rewrite /validr /= Z.add_0_r; t_xrbindP => ? _ /assertP.
    case: Mz.get => //= v _ /(_ v _ erefl) -> //.
    by move: hr; rewrite /validr /validw; case: in_rangeP => //= ? _; nia.
  Qed.
 
  Lemma uincl_set {ws len1 len2} (a1 a1': array len1) (a2: array len2) i (w:word ws) :
    uincl a1 a2 ->
    set a1 i w = ok a1' ->
    exists a2', set a2 i w = ok a2' /\ uincl a1' a2'.
  Proof.
    rewrite /set /CoreMem.write /= => hu; t_xrbindP => ? hw1.
    have hw2 := uincl_validw hu hw1.
    rewrite hw2 => <-; eexists;split;first reflexivity.
    case: hu => h1 h2; split => // k v hk hg1.
    have := (CoreMem.uwrite_uget (CM := array_CM _) w k hw2).
    have := (CoreMem.uwrite_uget (CM := array_CM _) w k hw1).
    rewrite /= /uget hg1 /sub /= => ->.
    have := CoreMem.uwrite_validr8 (CM := array_CM _) w k hw2.
    have := CoreMem.uwrite_validr8 (CM := array_CM _) w k hw1.
    rewrite /= /validr /sub /= Z.add_0_r.
    case: ifPn; rewrite !zify => ?.
    + by t_xrbindP => ? _ _ ? _; case: Mz.get => //= ?? ->.
    rewrite /validw; case: in_rangeP; rewrite /wsize_size /=; last by nia.
    case: in_rangeP; rewrite /wsize_size /= !andbT; last by nia.
    move=> _ _; rewrite hg1 /=.
    have := h2 k _ hk; case: Mz.get => //= v1 /(_ _ erefl) -> _ /=.
    by case: Mz.get => //= ? _ ->.
  Qed.

  Lemma uincl_refl len (a: array len) : uincl a a.
  Proof. by split => //;apply Z.le_refl. Qed.

  Lemma uincl_trans {len1 len2 len3} 
    (a2: array len2) (a1: array len1) (a3: array len3) :
    uincl a1 a2 -> uincl a2 a3 -> uincl a1 a3. 
  Proof.
    move=> [l1 h1] [l2 h2]; split; first by lia.
    move=> ????;apply h2;first by lia.
    by apply h1.
  Qed.
 
  Lemma set_get8 len (m m':array len) p ws (v: word ws) k :    
    set m p v = ok m' ->
    get U8 m' k= 
      let i := (k - p * wsize_size ws)%Z in
       if ((0 <=? i) && (i <? wsize_size ws))%Z then ok (LE.wread8 v i)
       else get U8 m k.
  Proof. 
    move=> hs; have := CoreMem.write_read8 k hs.
    by rewrite /get wsize8 !Z.mul_1_r.  
  Qed.

  Lemma set_zget8 len (m m':array len) p ws (v: word ws) k :    
    (0 <= k < len)%Z ->
    set m p v = ok m' ->
    Mz.get m'.(arr_data) k= 
      let i := (k - p * wsize_size ws)%Z in
       if ((0 <=? i) && (i <? wsize_size ws))%Z then Some (LE.wread8 v i)
       else Mz.get m.(arr_data) k.
  Proof.
    move=> hk; rewrite /set /CoreMem.write; t_xrbindP => ? /= hw <-.
    have /= := CoreMem.uwrite_uget (CM := array_CM _) v k hw.
    have /= := CoreMem.uwrite_validr8 (CM := array_CM _) v k hw.
    move: hw => /assertP/in_rangeP => hw.
    rewrite /validr /= /sub /validw /uget.
    case: in_rangeP; last by rewrite wsize8; nia.
    case: ifPn; rewrite !zify wsize8 Z.add_0_r => ? _ /=.
    + by case: Mz.get => //= ? _ ->.
    by case: Mz.get => /=; case: Mz.get =>//= ??? ->.
  Qed.

  Lemma set_validr_eq len (m m':array len) p ws (v: word ws) :
    set m p v = ok m' ->
    validr m' (p * wsize_size ws)%Z ws = ok tt.
  Proof.
    move=> hset; have := set_zget8 _ hset; move: hset.
    rewrite /set /CoreMem.write /validr /=; t_xrbindP => ? hw1 <-.
    move: (hw1); rewrite /validw; t_xrbindP => /assertP /dup [] /in_rangeP hp -> /= hz.
    case: allP => //= -[] k; rewrite in_ziota !zify Z.add_0_l => hk.
    rewrite hz; last by nia.
    case: ifPn => //=; rewrite !zify; nia.
  Qed.

  Lemma setP_eq len (m m':array len) p ws (v: word ws) :
    set m p v = ok m' ->
    get ws m' p = ok v.
  Proof.
    move=> h1;have := CoreMem.writeP_eq h1.
    rewrite /get /CoreMem.read /= (set_validr_eq h1) /= => ->.
    by rewrite LE.decodeK.
  Qed.

  Lemma set_validr_neq len (m m':array len) p1 p2 ws (v: word ws) :
    p1 != p2 -> 
    set m p1 v = ok m' ->
    validr m' (p2 * wsize_size ws)%Z ws = validr m (p2 * wsize_size ws)%Z ws.
  Proof.
    move=> /eqP hp hset; have := set_zget8 _ hset; move: hset.
    rewrite /set /CoreMem.write /validr /=; t_xrbindP => ? hw1 <-.
    move: (hw1); rewrite /validw => /assertP /in_rangeP hp1 hz.
    case: in_rangeP => hp2 //=; f_equal.
    apply all_ziota => i hi; rewrite hz; last by nia.
    by case: ifPn => //=; rewrite !zify; nia.
  Qed.

  Lemma setP_neq len (m m':array len) p1 p2 ws (v: word ws) :
    p1 != p2 ->
    set m p1 v = ok m' -> 
    get ws m' p2 = get ws m p2.
  Proof.
    move=> hp h1;have := CoreMem.writeP_neq h1.
    rewrite /get /CoreMem.read /= (set_validr_neq hp h1) /= => -> //.
    rewrite /CoreMem.disjoint_range /= /add => ??; move/eqP : hp; nia.
  Qed.

  Lemma setP len (m m':array len) p1 p2 ws (v: word ws) :
    set m p1 v = ok m' -> 
    get ws m' p2 = if p1 == p2 then ok v else get ws m p2.
  Proof. by case: eqP => [<- | /eqP];[ apply setP_eq | apply setP_neq]. Qed.

  Definition filter (m : Mz.t u8) p := 
    Mz.fold (fun k e m => if (k <? p)%Z then Mz.set m k e else m) m (Mz.empty _).

  Definition inject len len' (a:array len) : array len' :=
    if (len <? len')%Z then {| arr_data := filter a.(arr_data) len |}
    else {| arr_data := a.(arr_data) |}.

  Lemma zget_inject len (a:array len) (p:positive) i: 
    (0 <= i < p)%Z ->
    Mz.get (WArray.arr_data (WArray.inject p a)) i = 
    if (i <? len)%Z then Mz.get (WArray.arr_data a) i else None.
  Proof.
    rewrite /inject; case: a => a /=.
    case: ZltP; last by case: ZltP => //=; lia.
    rewrite /= /filter Mz.foldP => hlen hi.
    have -> : forall els m,
     (forall kv, List.In kv els -> Mz.get a kv.1 = Some kv.2) ->
     Mz.get (foldl
        (λ (a0 : Mz.t u8) (kv : Mz.K.t * u8),
          if (kv.1 <? len)%Z then Mz.set a0 kv.1 kv.2 else a0) m els) i =
      if (i \in map fst els) && (i <? len)%Z then Mz.get a i 
      else Mz.get m i.
    + elim => //= -[i1 v1] els hrec m hin; rewrite hrec; last by move=> ? h;apply hin;auto.
      rewrite /= in_cons orbC;case: andP => [[] -> -> //| hn].
      rewrite orbC; case: eqP => /=. 
      + move=> ->;case: ifP => // ?; rewrite Mz.setP_eq.
        by rewrite (hin (i1,v1));auto.
      move=> /eqP /negbTE hne; move /andP/negbTE: hn => ->.
      by case: ifPn => //; rewrite Mz.setP eq_sym hne.
    + case heq: (i \in _) => //=; rewrite Mz.get0; case:ifP => //= ?.
      case heq1: Mz.get => [w|//].
      by move: heq1 => /(Mz.elementsP (i, w) a) -/(map_f fst); rewrite heq.
    by move=> kv;apply Mz.elementsIn.
  Qed.

  Lemma get_bound ws len (t:array len) i w :
    get ws t i = ok w -> 
    (0 <= i * wsize_size ws /\ (i + 1) * wsize_size ws <= len)%Z.
  Proof.
    rewrite /get /CoreMem.read /= /validr /validw; t_xrbindP => ?? /assertP /in_rangeP; nia.
  Qed.     

  Lemma set_bound ws len (a t:array len) i (w:word ws) :
    set a i w = ok t -> 
    (0 <= i * wsize_size ws /\ (i+1) * wsize_size ws <= len)%Z.
  Proof.
    rewrite /set /CoreMem.write /= /validw; t_xrbindP => ? /assertP /in_rangeP; nia.
  Qed.

  Lemma get_uget len (t:array len) i v :
    get U8 t i = ok v -> uget t i = v.
  Proof.
    rewrite /get /CoreMem.read /=; t_xrbindP => ?? <-.
    by rewrite CoreMem.uread8_get wsize8 Z.mul_1_r.
  Qed.

  Lemma get_get8 ws len (t:WArray.array len) i w k :
    get ws t i = ok w -> 
    (0 <= k < wsize_size ws)%Z ->
    exists v, get U8 t (i * wsize_size ws + k) = ok v.
  Proof.
    rewrite /get /CoreMem.read /= /validr /validw; t_xrbindP.
    move=> ?? /assertP /in_rangeP h1 /assertP /allP h2 ? hk /=.
    rewrite wsize8 Z.mul_1_r Z.add_0_r.
    have -> /= : in_range len (i * wsize_size ws + k)%Z U8.
    + by rewrite /in_range !zify wsize8; nia.
    rewrite h2 /=; first by eauto.
    by rewrite in_ziota !zify.
  Qed.

  Lemma get0 (n:positive) off : (0 <= off ∧ off < n)%Z -> 
    get U8 (empty n) off = Error ErrAddrInvalid.
  Proof.
    rewrite /get /CoreMem.read /= /validr /validw /= /in_range wsize8 Z.mul_1_r.
    case: andP => //; rewrite !zify; lia.
  Qed.

End WArray.
Hint Resolve WArray.uincl_refl.

(* ** Values
  * -------------------------------------------------------------------- *)

Variant value : Type :=
  | Vbool  :> bool -> value
  | Vint   :> Z    -> value
  | Varr   : forall len, WArray.array len -> value
  | Vword  : forall s, word s -> value
  | Vundef : stype -> value.

Definition undef_b := Vundef sbool.

Definition values := seq value.

Definition undef_error {t} := @Error error t ErrAddrUndef.

Definition to_bool v :=
  match v with
  | Vbool b      => ok b
  | Vundef sbool => undef_error
  | _            => type_error
  end.

Definition to_int v :=
  match v with
  | Vint z      => ok z
  | Vundef sint => undef_error
  | _           => type_error
  end.

Definition truncate_word (s s':wsize) (w:word s') : exec (word s) := 
   if (s <= s')%CMP then ok (zero_extend s w) else type_error.

Definition to_word (s: wsize) (v: value) : exec (word s) :=
  match v with
  | Vword s' w        => truncate_word s w
  | Vundef (sword s') => Error (if (s <= s')%CMP then ErrAddrUndef else ErrType)
  | _                 => type_error
  end.

Notation to_pointer := (to_word Uptr).

Definition sem_t (t : stype) : Type :=
  match t with
  | sbool    => bool
  | sint     => Z
  | sarr n   => WArray.array n
  | sword s  => word s
  end.

Definition to_arr len v : exec (sem_t (sarr len)) :=
  match v with
  | Varr len' t => WArray.cast len t
  | Vundef (sarr len') =>
    Error (if (len <=? len')%Z then ErrAddrUndef else ErrType)
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
  | Vundef t    => vundef_type t
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
Hint Resolve subtype_refl.

Lemma subtype_trans y x z : subtype x y -> subtype y z -> subtype x z.
Proof.
  case: x => //= [/eqP<-|/eqP<-|n1|sx] //.
  + case: y => //= n2 /ZleP h1;case: z => //= n3 /ZleP h2.
    by apply /ZleP;apply: Z.le_trans h1 h2.
  case: y => //= sy hle;case: z => //= sz;apply: cmp_le_trans hle.
Qed.

Definition check_ty_val (ty:stype) (v:value) :=
  subtype ty (type_of_val v).

(* ** Variable map
 * -------------------------------------------------------------------- *)

Notation vmap     := (Fv.t (fun t => exec (sem_t t))).

Definition undef_addr t :=
  match t return exec (sem_t t) with
  | sbool | sint | sword _ => undef_error
  | sarr n => ok (WArray.empty n)
  end.

Definition vmap0 : vmap :=
  @Fv.empty (fun t => exec (sem_t t)) (fun x => undef_addr x.(vtype)).

Definition on_vu t r (fv: t -> r) (fu:exec r) (v:exec t) : exec r :=
  match v with
  | Ok v => ok (fv v)
  | Error ErrAddrUndef => fu
  | Error e            => Error e
  end.

Lemma on_vuP T R (fv: T -> R) (fu: exec R) (v:exec T) r P:
  (forall t, v = ok t -> fv t = r -> P) ->
  (v = undef_error -> fu = ok r -> P) ->
  on_vu fv fu v = ok r -> P.
Proof. by case: v => [a | []] Hfv Hfu //=;[case; apply: Hfv | apply Hfu]. Qed.

(* An access to a undefined value, leads to an error *)
Definition get_var (m:vmap) x :=
  on_vu (@to_val (vtype x)) undef_error (m.[x]%vmap).

(* Assigning undefined value is allowed only for bool *)
Definition set_var (m:vmap) x v : exec vmap :=
  on_vu (fun v => m.[x<-ok v]%vmap)
        (if is_sbool x.(vtype) then ok m.[x<-undef_addr x.(vtype)]%vmap
         else type_error) 
        (of_val (vtype x) v).

Lemma set_varP (m m':vmap) x v P :
   (forall t, of_val (vtype x) v = ok t -> m.[x <- ok t]%vmap = m' -> P) ->
   ( is_sbool x.(vtype) -> of_val (vtype x) v = undef_error ->
     m.[x<-undef_addr x.(vtype)]%vmap = m' -> P) ->
   set_var m x v = ok m' -> P.
Proof.
  move=> H1 H2;apply on_vuP => //.
  by case:ifPn => // hb herr []; apply : H2.
Qed.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Definition lprod ts tr :=
  foldr (fun t tr => t -> tr) tr ts.

Definition sem_prod ts tr := lprod (map sem_t ts) tr.

Definition sem_shift (shift:forall {s}, word s -> Z -> word s) s (v:word s) (i:u8) :=
  let i :=  wunsigned (wand i (x86_shift_mask s)) in
  shift v i.

Definition sem_shr {s} := @sem_shift (@wshr) s.
Definition sem_sar {s} := @sem_shift (@wsar) s.
Definition sem_shl {s} := @sem_shift (@wshl) s.

Definition sem_vadd (ve:velem) {ws:wsize} := (lift2_vec ve +%R ws).
Definition sem_vsub (ve:velem) {ws:wsize} := (lift2_vec ve (fun x y => x - y)%R ws).
Definition sem_vmul (ve:velem) {ws:wsize} := (lift2_vec ve *%R ws).

Definition sem_vshr (ve:velem) {ws:wsize} (v : word ws) (i:u8) :=  
  lift1_vec ve (fun x => wshr x (wunsigned i)) ws v.

Definition sem_vsar (ve:velem) {ws:wsize} (v : word ws) (i:u8) :=  
  lift1_vec ve (fun x => wsar x (wunsigned i)) ws v.

Definition sem_vshl (ve:velem) {ws:wsize} (v : word ws) (i:u8) :=  
  lift1_vec ve (fun x => wshl x (wunsigned i)) ws v.

Definition sem_sop1_typed (o: sop1) :
  let t := type_of_op1 o in
  sem_t t.1 → sem_t t.2 :=
  match o with
  | Oword_of_int sz => wrepr sz
  | Oint_of_word sz => wunsigned
  | Osignext szo szi => @sign_extend szo szi
  | Ozeroext szo szi => @zero_extend szo szi
  | Onot => negb
  | Olnot sz => wnot
  | Oneg Op_int => Z.opp
  | Oneg (Op_w sz) => (-%R)%R
  end.

Arguments sem_sop1_typed : clear implicits.

Definition sem_sop1 (o: sop1) (v: value) : exec value :=
  let t := type_of_op1 o in
  Let x := of_val _ v in
  ok (to_val (sem_sop1_typed o x)).

Lemma sem_sop1I y x f:
  sem_sop1 f x = ok y →
  exists2 w : sem_t (type_of_op1 f).1,
    of_val _ x = ok w &
    y = to_val (sem_sop1_typed f w).
Proof. by rewrite /sem_sop1; t_xrbindP => w ok_w <-; eauto. Qed.

Definition signed {A:Type} (fu fs:A) s := 
  match s with
  | Unsigned => fu
  | Signed => fs
  end.

Definition mk_sem_divmod sz o (w1 w2: word sz) : exec (word sz) :=
  if ((w2 == 0) || ((wsigned w1 == wmin_signed sz) && (w2 == -1)))%R then type_error
  else ok (o w1 w2).

Definition mk_sem_sop2 (t1 t2 t3: Type) (o:t1 -> t2 -> t3) v1 v2 : exec t3 := 
  ok (o v1 v2).

Definition sem_sop2_typed (o: sop2) :
  let t := type_of_op2 o in
  sem_t t.1.1 → sem_t t.1.2 → exec (sem_t t.2) :=
  match o with
  | Oand => mk_sem_sop2 andb
  | Oor  => mk_sem_sop2 orb

  | Oadd Op_int   => mk_sem_sop2 Z.add
  | Oadd (Op_w s) => mk_sem_sop2 +%R
  | Omul Op_int   => mk_sem_sop2 Z.mul
  | Omul (Op_w s) => mk_sem_sop2 *%R
  | Osub Op_int   => mk_sem_sop2 Z.sub
  | Osub (Op_w s) => mk_sem_sop2 (fun x y =>  x - y)%R
  | Odiv Cmp_int  => mk_sem_sop2 Z.div
  | Odiv (Cmp_w u s) => @mk_sem_divmod s (signed wdiv wdivi u)
  | Omod Cmp_int  => mk_sem_sop2 Z.modulo
  | Omod (Cmp_w u s) => @mk_sem_divmod s (signed wmod wmodi u)

  | Oland s => mk_sem_sop2 wand
  | Olor  s => mk_sem_sop2 wor
  | Olxor s => mk_sem_sop2 wxor
  | Olsr  s => mk_sem_sop2 sem_shr
  | Olsl  s => mk_sem_sop2 sem_shl
  | Oasr  s => mk_sem_sop2 sem_sar

  | Oeq Op_int    => mk_sem_sop2 Z.eqb
  | Oeq (Op_w s)  => mk_sem_sop2 eq_op
  | Oneq Op_int   => mk_sem_sop2 (fun x y => negb (Z.eqb x y))
  | Oneq (Op_w s) => mk_sem_sop2 (fun x y => (x != y))

  (* Fixme use the "new" Z *)
  | Olt Cmp_int   => mk_sem_sop2 Z.ltb
  | Ole Cmp_int   => mk_sem_sop2 Z.leb
  | Ogt Cmp_int   => mk_sem_sop2 Z.gtb
  | Oge Cmp_int   => mk_sem_sop2 Z.geb

  | Olt (Cmp_w u s) => mk_sem_sop2 (wlt u)
  | Ole (Cmp_w u s) => mk_sem_sop2 (wle u)
  | Ogt (Cmp_w u s) => mk_sem_sop2 (fun x y => wlt u y x)
  | Oge (Cmp_w u s) => mk_sem_sop2 (fun x y => wle u y x)
  | Ovadd ve ws     => mk_sem_sop2 (sem_vadd ve)
  | Ovsub ve ws     => mk_sem_sop2 (sem_vsub ve)
  | Ovmul ve ws     => mk_sem_sop2 (sem_vmul ve)
  | Ovlsr ve ws     => mk_sem_sop2 (sem_vshr ve)
  | Ovlsl ve ws     => mk_sem_sop2 (sem_vshl ve)
  | Ovasr ve ws     => mk_sem_sop2 (sem_vsar ve)
  end.

Arguments sem_sop2_typed : clear implicits.

Definition sem_sop2 (o: sop2) (v1 v2: value) : exec value :=
  let t := type_of_op2 o in
  Let x1 := of_val _ v1 in
  Let x2 := of_val _ v2 in
  Let r  := sem_sop2_typed o x1 x2 in
  ok (to_val r).

Lemma sem_sop2I v v1 v2 f:
  sem_sop2 f v1 v2 = ok v →
  ∃ (w1 : sem_t (type_of_op2 f).1.1) (w2 : sem_t (type_of_op2 f).1.2) 
    (w3: sem_t (type_of_op2 f).2),
    [/\ of_val _ v1 = ok w1,
        of_val _ v2 = ok w2,
        sem_sop2_typed f w1 w2 = ok w3 &
        v = to_val w3].
Proof.
  by rewrite /sem_sop2; t_xrbindP => w1 ok_w1 w2 ok_w2 w3 ok_w3 <- {v}; exists w1, w2, w3.
Qed.

Fixpoint app_sopn T ts : sem_prod ts (exec T) → values → exec T :=
  match ts return sem_prod ts (exec T) → values → exec T with
  | [::] => λ (o : exec T) (vs: values), if vs is [::] then o else type_error
  | t :: ts => λ (o: sem_t t → sem_prod ts (exec T)) (vs: values),
    if vs is v :: vs
    then Let v := of_val t v in app_sopn (o v) vs
    else type_error
  end.

Arguments app_sopn {T} ts _ _.

Definition curry A B (n: nat) (f: seq (sem_t A) → B) : sem_prod (nseq n A) B :=
  (fix loop n :=
   match n return seq (sem_t A) → sem_prod (nseq n A) B with
   | 0 => f
   | n'.+1 => λ acc a, loop n' (a :: acc)
   end) n [::].

Definition sem_opN_typed (o: opN) :
  let t := type_of_opN o in
  sem_prod t.1 (exec (sem_t t.2)) :=
  match o with
  | Opack sz pe => curry (A := sint) (sz %/ pe) (λ vs, ok (wpack sz pe vs))
  end.

Definition sem_opN (op: opN) (vs: values) : exec value :=
  Let w := app_sopn _ (sem_opN_typed op) vs in
  ok (to_val w).

Record estate := Estate {
  emem : mem;
  evm  : vmap
}.

Definition on_arr_var A (s:estate) (x:var) (f:forall n, WArray.array n -> exec A) :=
  Let v := get_var s.(evm) x in
  match v with
  | Varr n t => f n t
  | _ => type_error
  end.

Notation "'Let' ( n , t ) ':=' s '.[' x ']' 'in' body" :=
  (@on_arr_var _ s x (fun n (t:WArray.array n) => body)) (at level 25, s at level 0).

Lemma on_arr_varP A (f : forall n, WArray.array n -> exec A) v s x P:
  (forall n t, vtype x = sarr n ->
               get_var (evm s) x = ok (@Varr n t) ->
               f n t = ok v -> P) ->
  on_arr_var s x f = ok v -> P.
Proof.
  rewrite /on_arr_var=> H;apply: rbindP => vx.
  case: x H => -[ | | n | sz ] nx;rewrite /get_var => H;
    case Heq : ((evm s).[_])%vmap => [v' | e] //=.
  + by move=> [<-]. + by case: (e) => // -[<-].
  + by move=> [<-]. + by case: (e) => // -[<-].
  + by move=> [<-]; apply: H => //;rewrite Heq. + by case: (e) => // -[<-].
  + by move=> [<-]. + by case: (e) => // -[<-].
Qed.

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

Definition get_global_value (gd: glob_decls) (g: global) : option Z :=
  assoc gd g.

Definition get_global gd g : exec value :=
  if get_global_value gd g is Some z then 
    ok (Vword (wrepr (size_of_global g) z))
  else type_error.

Lemma get_globalI gd g v :
  get_global gd g = ok v →
  exists2 z : Z, get_global_value gd g = Some z & v = Vword (wrepr (size_of_global g) z).
Proof.
  rewrite /get_global; case: get_global_value => // z [<-];eauto.
Qed.

Definition is_defined (v: value) : bool :=
  if v is Vundef _ then false else true.

Section SEM_PEXPR.

Context (gd: glob_decls).

Fixpoint sem_pexpr (s:estate) (e : pexpr) : exec value :=
  match e with
  | Pconst z => ok (Vint z)
  | Pbool b  => ok (Vbool b)
  | Parr_init n => ok (Varr (WArray.empty n))
  | Pvar v => get_var s.(evm) v
  | Pglobal g => get_global gd g
  | Pget ws x e =>
      Let (n, t) := s.[x] in
      Let i := sem_pexpr s e >>= to_int in
      Let w := WArray.get ws t i in
      ok (Vword w)
  | Pload sz x e =>
    Let w1 := get_var s.(evm) x >>= to_pointer in
    Let w2 := sem_pexpr s e >>= to_pointer in
    Let w  := read_mem s.(emem) (w1 + w2) sz in
    ok (@to_val (sword sz) w)
  | Papp1 o e1 =>
    Let v1 := sem_pexpr s e1 in
    sem_sop1 o v1
  | Papp2 o e1 e2 =>
    Let v1 := sem_pexpr s e1 in
    Let v2 := sem_pexpr s e2 in
    sem_sop2 o v1 v2
  | PappN op es =>
    Let vs := mapM (sem_pexpr s) es in
    sem_opN op vs
  | Pif t e e1 e2 =>
    Let b := sem_pexpr s e >>= to_bool in
    Let v1 := sem_pexpr s e1 >>= truncate_val t in
    Let v2 := sem_pexpr s e2 >>= truncate_val t in
    ok (if b then v1 else v2)
  end.

Definition sem_pexprs s := mapM (sem_pexpr s).

Definition write_var (x:var_i) (v:value) (s:estate) : exec estate :=
  Let vm := set_var s.(evm) x v in
  ok ({| emem := s.(emem); evm := vm |}).

Definition write_vars xs vs s :=
  fold2 ErrType write_var xs vs s.

Definition write_none (s:estate) ty v :=
  on_vu (fun v => s) (if is_sbool ty then ok s else type_error)
          (of_val ty v).

Definition write_lval (l:lval) (v:value) (s:estate) : exec estate :=
  match l with
  | Lnone _ ty => write_none s ty v
  | Lvar x => write_var x v s
  | Lmem sz x e =>
    Let vx := get_var (evm s) x >>= to_pointer in
    Let ve := sem_pexpr s e >>= to_pointer in
    let p := (vx + ve)%R in (* should we add the size of value, i.e vx + sz * se *)
    Let w := to_word sz v in
    Let m :=  write_mem s.(emem) p sz w in
    ok {| emem := m;  evm := s.(evm) |}
  | Laset ws x i =>
    Let (n,t) := s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let v := to_word ws v in
    Let t := WArray.set t i v in
    Let vm := set_var s.(evm) x (@to_val (sarr n) t) in
    ok ({| emem := s.(emem); evm := vm |})
  end.

Definition write_lvals (s:estate) xs vs :=
   fold2 ErrType write_lval xs vs s.

End SEM_PEXPR.

Definition pval t1 t2 (p: sem_t t1 * sem_t t2) :=
  [::to_val p.1; to_val p.2].

Definition SF_of_word sz (w : word sz) :=
  msb w.

Definition PF_of_word sz (w : word sz) :=
  lsb w.

Definition ZF_of_word sz (w : word sz) :=
  w == 0%R.

(* -------------------------------------------------------------------- *)
(*  OF; CF ;SF; PF; ZF  *)
Definition rflags_of_bwop sz (w : word sz) :=
  (*  OF   ; CF   ; SF          ; PF          ; ZF          ] *)
  [:: false; false; SF_of_word w; PF_of_word w; ZF_of_word w].

(* -------------------------------------------------------------------- *)
(*  OF; CF ;SF; PF; ZF  *)
Definition rflags_of_aluop sz (w : word sz) (vu vs : Z) :=
  (*  OF                  ; CF                    *)
  [:: wsigned  w != vs; wunsigned w != vu;
  (*  SF          ; PF          ; ZF          ] *)
      SF_of_word w; PF_of_word w; ZF_of_word w ].

(* -------------------------------------------------------------------- *)
(*  OF; CF ;SF; PF; ZF  *)
Definition rflags_of_mul (ov : bool) :=
  (*  OF      ; CF                    *)
  [:: Vbool ov;  Vbool ov;
  (*  SF      ; PF       ; ZF         *)
     undef_b  ; undef_b   ; undef_b ].

(* -------------------------------------------------------------------- *)

Definition rflags_of_div :=
  (*  OF      ; CF                    *)
  [:: undef_b  ; undef_b  ;
  (*  SF      ; PF       ; ZF         *)
      undef_b  ; undef_b   ; undef_b ].

(* -------------------------------------------------------------------- *)
(*  OF; SF; PF; ZF  *)
Definition rflags_of_aluop_nocf sz (w : word sz) (vs : Z) :=
  (*  OF                  *)
  [:: wsigned   w != vs;
  (*  SF          ; PF          ; ZF          ] *)
      SF_of_word w; PF_of_word w; ZF_of_word w ].

Definition flags_w (bs:seq bool) sz (w: word sz) : exec values :=
  ok ((map Vbool bs) ++ [:: Vword w]).

Definition rflags_of_aluop_w sz (w : word sz) (vu vs : Z) : exec values :=
  flags_w (rflags_of_aluop w vu vs) w.

Definition rflags_of_aluop_nocf_w sz (w : word sz) (vs : Z) : exec values :=
  flags_w (rflags_of_aluop_nocf w vs) w.

Definition rflags_of_bwop_w sz (w : word sz) : exec values :=
  flags_w (rflags_of_bwop w) w.

Definition vbools bs : exec values := ok (List.map Vbool bs).

(* -------------------------------------------------------------------- *)


Definition x86_MOV sz (x: word sz) : exec values :=
  Let _ := check_size_8_64 sz in
  ok [:: Vword x].

Definition x86_MOVSX szo szi (x: word szi) : exec values :=
  Let _ :=
    match szi with
    | U8 => check_size_16_64 szo
    | U16 => check_size_32_64 szo
    | U32 => assert (szo == U64) ErrType
    | _ => type_error
    end in
  ok [:: Vword (sign_extend szo x) ].

Definition x86_MOVZX szo szi (x: word szi) : exec values :=
  Let _ :=
    match szi with
    | U8 => check_size_16_64 szo
    | U16 => check_size_32_64 szo
    | _ => type_error
    end in
  ok [:: Vword (zero_extend szo x) ].

Definition x86_add {sz} (v1 v2 : word sz) :=
  Let _ := check_size_8_64 sz in
  rflags_of_aluop_w
    (v1 + v2)%R
    (wunsigned v1 + wunsigned v2)%Z
    (wsigned   v1 + wsigned   v2)%Z.

Definition x86_sub {sz} (v1 v2 : word sz) :=
  Let _ := check_size_8_64 sz in
  rflags_of_aluop_w
    (v1 - v2)%R
    (wunsigned v1 - wunsigned v2)%Z
    (wsigned   v1 - wsigned   v2)%Z.

Definition x86_mul {sz} (v1 v2: word sz): exec values :=
  Let _  := check_size_16_64 sz in
  let lo := (v1 * v2)%R in
  let hi := wmulhu v1 v2 in
  let ov := wdwordu hi lo in
  let ov := (ov >? wbase sz - 1)%Z in
  ok (rflags_of_mul ov ++ [::Vword hi; Vword lo]).

Definition x86_imul_overflow sz (hi lo: word sz) : bool :=
  let ov := wdwords hi lo in
  (ov <? -wbase sz)%Z || (ov >? wbase sz - 1)%Z.

Definition x86_imul {sz} (v1 v2: word sz) : exec values:=
  Let _  := check_size_16_64 sz in
  let lo := (v1 * v2)%R in
  let hi := wmulhs v1 v2 in
  let ov := x86_imul_overflow hi lo in
  ok (rflags_of_mul ov ++ [::Vword hi; Vword lo]).

Definition x86_imult {sz} (v1 v2: word sz) : exec values:=
  Let _  := check_size_16_64 sz in
  let lo := (v1 * v2)%R in
  let hi := wmulhs v1 v2 in
  let ov := x86_imul_overflow hi lo in
  ok (rflags_of_mul ov ++ [::Vword lo]).

Definition x86_div {sz} (hi lo dv: word sz) : exec values:=
  Let _  := check_size_16_64 sz in
  let dd := wdwordu hi lo in
  let dv := wunsigned dv in
  let q  := (dd  /  dv)%Z in
  let r  := (dd mod dv)%Z in
  let ov := (q >? wmax_unsigned sz)%Z in

  if (dv == 0)%Z || ov then type_error else

  ok (rflags_of_div ++ [:: Vword (wrepr sz q); Vword (wrepr sz r)]).

Definition x86_idiv {sz} (hi lo dv: word sz) : exec values :=
  Let _  := check_size_16_64 sz in
  let dd := wdwords hi lo in
  let dv := wsigned dv in
  let q  := (Z.quot dd dv)%Z in
  let r  := (Z.rem  dd dv)%Z in
  let ov := (q <? wmin_signed sz)%Z || (q >? wmax_signed sz)%Z in

  if (dv == 0)%Z || ov then type_error else

  ok (rflags_of_div ++ [:: Vword (wrepr sz q); Vword (wrepr sz r)]).

Definition x86_cqo {sz} (w:word sz) : exec values := 
  Let _ := check_size_16_64 sz in
  let r : word sz := (if msb w then -1 else 0)%R in
  ok [::Vword r].
  
Definition add_carry sz (x y c: Z) : word sz :=
  wrepr sz (x + y + c).

Definition x86_adc {sz} (v1 v2 : word sz) (c: bool) :=
  Let _  := check_size_8_64 sz in
  let c := Z.b2z c in
  rflags_of_aluop_w
    (add_carry sz (wunsigned v1) (wunsigned v2) c)
    (wunsigned v1 + wunsigned v2 + c)%Z
    (wsigned   v1 + wsigned   v2 + c)%Z.

Definition sub_borrow sz (x y c: Z) : word sz :=
  wrepr sz (x - y - c).

Definition x86_sbb {sz} (v1 v2 : word sz) (c:bool) :=
  Let _  := check_size_8_64 sz in
  let c := Z.b2z c in
  rflags_of_aluop_w
    (sub_borrow sz (wunsigned v1) (wunsigned v2) c)
    (wunsigned v1 - (wunsigned v2 + c))%Z
    (wsigned   v1 - (wsigned   v2 + c))%Z.

Definition x86_neg {sz} (w: word sz) :=
  Let _  := check_size_8_64 sz in
  let vs := (- wsigned w)%Z in
  let v := (- w)%R in
  flags_w
  [:: wsigned   v != vs; (w != 0)%R;
      SF_of_word v; PF_of_word v; ZF_of_word v ]
  v.

Definition x86_inc {sz} (w: word sz) :=
  Let _  := check_size_8_64 sz in
  rflags_of_aluop_nocf_w
    (w + 1)
    (wsigned w + 1)%Z.

Definition x86_dec {sz} (w: word sz) :=
  Let _  := check_size_8_64 sz in
  rflags_of_aluop_nocf_w
    (w - 1)
    (wsigned w - 1)%Z.

Definition x86_setcc (b:bool) : exec values := ok [:: Vword (wrepr U8 (Z.b2z b))].

Definition x86_bt {sz} (x y: word sz) : exec values :=
  Let _  := check_size_8_64 sz in
  ok [:: Vbool (wbit x y) ].

Definition x86_lea {sz} (disp base scale offset: word sz) : exec values :=
  Let _  := check_size_32_64 sz in
  if check_scale (wunsigned scale) then
    ok [::Vword (disp + base + scale * offset)]
  else type_error.

Definition x86_test {sz} (x y: word sz) : exec values :=
  Let _  := check_size_8_64 sz in
  vbools (rflags_of_bwop (wand x y)).

Definition x86_cmp {sz} (x y: word sz) :=
  Let _  := check_size_8_64 sz in
  vbools
    (rflags_of_aluop (x - y)
       (wunsigned x - wunsigned y)%Z (wsigned x - wsigned y)%Z).

Definition x86_and {sz} (v1 v2: word sz) :=
  Let _  := check_size_8_64 sz in
  rflags_of_bwop_w
    (wand v1 v2).

Definition rflags_of_andn sz (w: word sz) :=
  (* OF ; CF ; SF ; PF ; ZF *)
  [:: Vbool false ; Vbool false ; Vbool (SF_of_word w) ; Vundef sbool ; Vbool (ZF_of_word w) ].

Definition x86_andn {sz} (v1 v2: word sz) :=
  Let _  := check_size_32_64 sz in
  let w := wandn v1 v2 in
  ok (rcons (rflags_of_andn w) (Vword w)).

Definition x86_or {sz} (v1 v2: word sz) :=
  Let _  := check_size_8_64 sz in
  rflags_of_bwop_w
    (wor v1 v2).

Definition x86_xor {sz} (v1 v2: word sz) :=
  Let _  := check_size_8_64 sz in
  rflags_of_bwop_w
    (wxor v1 v2).

Definition x86_not {sz} (v: word sz) : exec values:=
  Let _  := check_size_8_64 sz in
  ok [:: Vword (wnot v)].

Definition x86_ror {sz} (v: word sz) (i: u8) : exec values :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    let u := Vundef sbool in
    ok [:: u; u; Vword v]
  else
    let r := wror v (wunsigned i) in
    let CF := msb r in
    let OF :=
        if i == 1%R
        then Vbool (CF != msb v) else Vundef sbool
    in
    ok [:: OF; Vbool CF; Vword r ].

Definition x86_rol {sz} (v: word sz) (i: u8) : exec values :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    let u := Vundef sbool in
    ok [:: u; u; Vword v]
  else
    let r := wrol v (wunsigned i) in
    let CF := lsb r in
    let OF :=
        if i == 1%R
        then Vbool (msb r != CF) else Vundef sbool
    in
    ok [:: OF; Vbool CF; Vword r ].

Definition x86_shl {sz} (v: word sz) (i: u8) : exec values :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    let u := Vundef sbool in
    ok [:: u; u; u; u; u; Vword v]
  else
    let rc := msb (wshl v (wunsigned i - 1)) in
    let r  := wshl v (wunsigned i) in
    let OF :=
      if i == 1%R then Vbool (msb r (+) rc)
      else undef_b in
    let CF := Vbool rc in
    let SF := Vbool (SF_of_word r) in
    let PF := Vbool (PF_of_word r) in
    let ZF := Vbool (ZF_of_word r) in
    ok [:: OF; CF; SF; PF; ZF; Vword r].

Definition x86_shld {sz} (v1 v2: word sz) (i: u8) : exec values :=
  Let _  := check_size_16_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    let u := Vundef sbool in
    ok [:: u; u; u; u; u; Vword v1]
  else
    let rc := msb (wshl v1 (wunsigned i - 1)) in
    let r1 := wshl v1 (wunsigned i) in
    let r2 := wsar v2 (wsize_bits sz - (wunsigned i)) in
    let r  := wor r1 r2 in
    let OF :=
      if i == 1%R then Vbool (msb r (+) rc)
      else undef_b in
    let CF := Vbool rc in
    let SF := Vbool (SF_of_word r) in
    let PF := Vbool (PF_of_word r) in
    let ZF := Vbool (ZF_of_word r) in
    ok [:: OF; CF; SF; PF; ZF; Vword r].

Definition x86_shr {sz} (v: word sz) (i: u8) : exec values :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    let u := Vundef sbool in
    ok [:: u; u; u; u; u; Vword v]
  else
    let rc := lsb (wshr v (wunsigned i - 1)) in
    let r  := wshr v (wunsigned i) in

    let OF :=
      if i == 1%R then Vbool (msb r)
      else undef_b in
    let CF := Vbool rc in
    let SF := Vbool (SF_of_word r) in
    let PF := Vbool (PF_of_word r) in
    let ZF := Vbool (ZF_of_word r) in
    ok [:: OF; CF; SF; PF; ZF; Vword r].

Definition x86_shrd {sz} (v1 v2: word sz) (i: u8) : exec values :=
  Let _  := check_size_16_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    let u := Vundef sbool in
    ok [:: u; u; u; u; u; Vword v1]
  else
    let rc := lsb (wshr v1 (wunsigned i - 1)) in
    let r1 := wshr v1 (wunsigned i) in
    let r2 := wshl v2 (wsize_bits sz - (wunsigned i)) in
    let r  := wor r1 r2 in
    let OF :=
      if i == 1%R then Vbool (msb r (+) msb v1)
      else undef_b in
    let CF := Vbool rc in
    let SF := Vbool (SF_of_word r) in
    let PF := Vbool (PF_of_word r) in
    let ZF := Vbool (ZF_of_word r) in
    ok [:: OF; CF; SF; PF; ZF; Vword r].

Definition x86_sar {sz} (v: word sz) (i: u8) : exec values :=
  Let _ := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    let u := Vundef sbool in
    ok [:: u; u; u; u; u; Vword v]
  else
    let rc := lsb (wsar v (wunsigned i - 1)) in
    let r  := wsar v (wunsigned i) in
    let OF :=
      if i == 1%R then Vbool false
      else undef_b in
    let CF := Vbool rc in
    let SF := Vbool (SF_of_word r) in
    let PF := Vbool (PF_of_word r) in
    let ZF := Vbool (ZF_of_word r) in
    ok [:: OF; CF; SF; PF; ZF; Vword r].

(* ---------------------------------------------------------------- *)
Definition x86_bswap {sz} (v: word sz) : exec values :=
  Let _ := check_size_32_64 sz in
  ok [:: Vword (wbswap v) ].

(* ---------------------------------------------------------------- *)
Definition x86_movd {sz} (v: word sz) : exec values :=
  Let _ := check_size_32_64 sz in
  ok [:: Vword (zero_extend U128 v) ].

(* ---------------------------------------------------------------- *)
Definition x86_u128_binop sz (op: _ → _ → word sz) (v1 v2: word sz) : exec values :=
  Let _ := check_size_128_256 sz in
  ok [:: Vword (op v1 v2) ].

Definition x86_vpand {sz} := x86_u128_binop (@wand sz).
Definition x86_vpandn {sz} := x86_u128_binop (@wandn sz).
Definition x86_vpor {sz} := x86_u128_binop (@wor sz).
Definition x86_vpxor {sz} := x86_u128_binop (@wxor sz).

(* ---------------------------------------------------------------- *)
Definition x86_vpadd (ve: velem) {sz} := x86_u128_binop (lift2_vec ve +%R sz).
Definition x86_vpsub (ve: velem) {sz} := 
  x86_u128_binop (lift2_vec ve (fun x y => x - y)%R sz).

Definition x86_vpmull (ve: velem) {sz} v1 v2 := 
  Let _ := check_size_32_64 ve in
  x86_u128_binop (lift2_vec ve *%R sz) v1 v2.

Definition x86_vpmulu {sz} := x86_u128_binop (@wpmulu sz).

(* ---------------------------------------------------------------- *)
Definition x86_vpextr (ve: wsize) (v: u128) (i: u8) :=
  (* This instruction is valid for smaller ve, but semantics is unusual,
      hence compiler correctness would not be provable. *)
  Let _ := check_size_32_64 ve in
  ok [:: Vword (nth (0%R: word ve) (split_vec ve v) (Z.to_nat (wunsigned i))) ].

(* ---------------------------------------------------------------- *)
Definition x86_vpinsr (ve: velem) (v1: u128) (v2: word ve) (i: u8) : exec values :=
  ok [:: Vword (wpinsr v1 v2 i) ].

Arguments x86_vpinsr : clear implicits.

(* ---------------------------------------------------------------- *)
Definition x86_u128_shift sz' sz (op: word sz' → Z → word sz')
  (v: word sz) (c: u8) : exec values :=
  Let _ := check_size_16_64 sz' in
  Let _ := check_size_128_256 sz in
  ok [:: Vword (lift1_vec sz' (λ v, op v (wunsigned c)) sz v) ].

Arguments x86_u128_shift : clear implicits.

Definition x86_vpsll (ve: velem) {sz} := x86_u128_shift ve sz (@wshl _).
Definition x86_vpsrl (ve: velem) {sz} := x86_u128_shift ve sz (@wshr _).
Definition x86_vpsra (ve: velem) {sz} := x86_u128_shift ve sz (@wsar _).

(* ---------------------------------------------------------------- *)
Definition x86_u128_shift_variable ve sz op v1 v2 : exec values :=
  Let _ := check_size_32_64 ve in
  Let _ := check_size_128_256 sz in
  ok [:: Vword (lift2_vec ve (λ v1 v2, op v1 (wunsigned v2)) sz v1 v2) ].

Arguments x86_u128_shift_variable : clear implicits.

Definition x86_vpsllv ve {sz} := x86_u128_shift_variable ve sz (@wshl _).
Definition x86_vpsrlv ve {sz} := x86_u128_shift_variable ve sz (@wshr _).

(* ---------------------------------------------------------------- *)
Definition x86_vpsxldq sz op (v1: word sz) (v2: u8) :=
  Let _ := check_size_128_256 sz in
  ok [:: @Vword sz (op v1 v2) ].

Definition x86_vpslldq {sz} := x86_vpsxldq (@wpslldq sz).
Definition x86_vpsrldq {sz} := x86_vpsxldq (@wpsrldq sz).

(* ---------------------------------------------------------------- *)
Definition x86_vpshufb {sz} := x86_u128_binop (@wpshufb sz).

(* ---------------------------------------------------------------- *)
Definition x86_vpshuf sz (op: word sz → Z → word sz) (v1: word sz) (v2: u8) : exec values :=
  Let _ := check_size_128_256 sz in
  ok [:: Vword (op v1 (wunsigned v2)) ].

Arguments x86_vpshuf : clear implicits.

Definition x86_vpshufhw {sz} := x86_vpshuf sz (@wpshufhw _).
Definition x86_vpshuflw {sz} := x86_vpshuf sz (@wpshuflw _).
Definition x86_vpshufd {sz} := x86_vpshuf sz (@wpshufd _).

(* ---------------------------------------------------------------- *)
Definition x86_vpunpckh ve {sz} := x86_u128_binop (@wpunpckh sz ve).
Definition x86_vpunpckl ve {sz} := x86_u128_binop (@wpunpckl sz ve).

(* ---------------------------------------------------------------- *)
Definition x86_vpblendd {sz} (v1 v2: word sz) (m: u8) : exec values :=
  Let _ := check_size_128_256 sz in
  ok [:: Vword (wpblendd v1 v2 m) ].

(* ---------------------------------------------------------------- *)
Definition x86_vpbroadcast ve sz (v: word ve) : exec values :=
  Let _ := check_size_128_256 sz in
  ok [:: Vword (wpbroadcast sz v) ].

(* ---------------------------------------------------------------- *)
Definition x86_vextracti128 (v: u256) (i: u8) : exec values :=
  let r := if lsb i then wshr v U128 else v in
  ok [:: Vword (zero_extend U128 r) ].

Definition x86_vinserti128 (v1: u256) (v2: u128) (m: u8) : exec values :=
  ok [:: Vword (winserti128 v1 v2 m) ].

(* ---------------------------------------------------------------- *)
Definition x86_vperm2i128 (v1 v2: u256) (m: u8) : exec values :=
  ok [:: Vword (wperm2i128 v1 v2 m) ].

Definition x86_vpermq (v: u256) (m: u8) : exec values :=
  ok [:: Vword (wpermq v m) ].

(* ---------------------------------------------------------------- *)
Definition x86_adcx {sz:wsize} (w1 w2: word sz) (c:bool) : exec values := 
  Let _ := check_size_32_64 sz in
  ok (@pval sbool (sword sz) (waddcarry w1 w2 c)).

Definition x86_adox {sz} := @x86_adcx sz.

Definition x86_mulx {sz:wsize} (w1 w2: word sz) : exec values := 
  Let _ := check_size_32_64 sz in
  ok (@pval (sword sz) (sword sz) (wumul w1 w2)).

(* ---------------------------------------------------------------- *)
Definition is_word (sz: wsize) (v: value) : exec unit :=
  match v with
  | Vword _ _
  | Vundef (sword _)
    => ok tt
  | _ => type_error end.

Lemma is_wordI sz v u :
  is_word sz v = ok u →
  subtype (vundef_type (sword sz)) (type_of_val v).
Proof. case: v => // [ sz' w | [] // ] _; exact: wsize_le_U8. Qed.

(* ---------------------------------------------------------------- *)
Notation app_b   o := (app_sopn [:: sbool] o).
Notation app_w sz o := (app_sopn [:: sword sz] o).
Notation app_ww sz o := (app_sopn [:: sword sz; sword sz] o).
Notation app_w8 sz o := (app_sopn [:: sword sz; sword U8] o).
Notation app_www sz o := (app_sopn [:: sword sz; sword sz; sword sz] o).
Notation app_ww8 sz o := (app_sopn [:: sword sz; sword sz; sword U8] o).
Notation app_wwb sz o := (app_sopn [:: sword sz; sword sz; sbool] o).
Notation app_bww o := (app_sopn [:: sbool; sword; sword] o).
Notation app_w4 sz o  := (app_sopn [:: sword sz; sword sz; sword sz; sword sz] o).

Definition exec_sopn (o:sopn) :  values -> exec values :=
  match o with
  | Omulu sz => app_ww sz (fun x y => ok (@pval (sword sz) (sword sz) (wumul x y)))
  | Oaddcarry sz => app_wwb sz (fun x y c => ok (@pval sbool (sword sz) (waddcarry x y c)))
  | Osubcarry sz => app_wwb sz (fun x y c => ok (@pval sbool (sword sz) (wsubcarry x y c)))
  | Oset0 sz => 
    if (sz <= U64)%CMP then 
      app_sopn [::]
        (let vf := Vbool false in
         ok [:: vf; vf; vf; vf; Vbool true; @Vword sz 0%R])
    else 
      app_sopn [::] (ok [:: @Vword sz 0%R])

  (* Low level x86 operations *)
  | Ox86_MOV sz => app_w sz (@x86_MOV sz)
  | Ox86_MOVSX sz sz' => app_w sz' (@x86_MOVSX sz sz')
  | Ox86_MOVZX sz sz' => app_w sz' (@x86_MOVZX sz sz')
  | Ox86_MOVZX32 => app_w U32 (λ x : u32, ok [:: Vword (zero_extend U64 x) ])
  | Ox86_CMOVcc sz => (fun v => match v with
    | [:: v1; v2; v3] =>
      Let _ := check_size_16_64 sz in
      Let b := to_bool v1 in
      Let w2 := to_word sz v2 in
      Let w3 := to_word sz v3 in
      if b then (ok [:: Vword w2])
      else (ok [:: Vword w3])
    | _ => type_error end)
  | Ox86_ADD sz => app_ww sz x86_add
  | Ox86_SUB sz => app_ww sz x86_sub
  | Ox86_MUL sz => app_ww sz x86_mul
  | Ox86_IMUL sz => app_ww sz x86_imul
  | Ox86_IMULt sz => app_ww sz x86_imult
  | Ox86_IMULtimm sz => app_ww sz x86_imult
  | Ox86_DIV sz => app_www sz x86_div
  | Ox86_IDIV sz => app_www sz x86_idiv
  | Ox86_CQO sz => app_w sz x86_cqo
  | Ox86_ADC sz => app_wwb sz x86_adc
  | Ox86_SBB sz => app_wwb sz x86_sbb
  | Ox86_NEG sz => app_w sz x86_neg
  | Ox86_INC sz => app_w sz x86_inc
  | Ox86_DEC sz => app_w sz x86_dec
  | Ox86_SETcc => app_b x86_setcc
  | Ox86_BT sz => app_ww sz x86_bt
  | Ox86_LEA sz => app_w4 sz x86_lea
  | Ox86_TEST sz => app_ww sz x86_test
  | Ox86_CMP sz => app_ww sz x86_cmp
  | Ox86_AND sz => app_ww sz x86_and
  | Ox86_ANDN sz => app_ww sz x86_andn
  | Ox86_OR sz => app_ww sz x86_or
  | Ox86_XOR sz => app_ww sz x86_xor
  | Ox86_NOT sz => app_w sz x86_not
  | Ox86_ROL sz => app_w8 sz x86_rol
  | Ox86_ROR sz => app_w8 sz x86_ror
  | Ox86_SHL sz => app_w8 sz x86_shl
  | Ox86_SHR sz => app_w8 sz x86_shr
  | Ox86_SAR sz => app_w8 sz x86_sar
  | Ox86_SHLD sz => app_ww8 sz x86_shld
  | Ox86_SHRD sz => app_ww8 sz x86_shrd
  | Ox86_ADCX sz => app_wwb sz x86_adcx
  | Ox86_ADOX sz => app_wwb sz x86_adox
  | Ox86_MULX sz => app_ww sz x86_mulx
  | Ox86_BSWAP sz => app_w sz x86_bswap
  | Ox86_MOVD sz => app_w sz x86_movd
  | Ox86_VMOVDQU sz => app_sopn [:: sword sz ] (λ x,
                                                Let _ := check_size_128_256 sz in
                                                ok [:: Vword x])
  | Ox86_VPAND sz => app_ww sz x86_vpand
  | Ox86_VPANDN sz => app_ww sz x86_vpandn
  | Ox86_VPOR sz => app_ww sz x86_vpor
  | Ox86_VPXOR sz => app_ww sz x86_vpxor
  | Ox86_VPADD ve sz => app_ww sz (x86_vpadd ve)
  | Ox86_VPSUB ve sz => app_ww sz (x86_vpsub ve)
  | Ox86_VPMULL ve sz => app_ww sz (x86_vpmull ve)
  | Ox86_VPMULU sz => app_ww sz x86_vpmulu
  | Ox86_VPEXTR ve => app_w8 U128 (x86_vpextr ve)
  | Ox86_VPINSR ve => app_sopn [:: sword128 ; sword ve ; sword8 ] (x86_vpinsr ve)
  | Ox86_VPSLL ve sz => app_w8 sz (x86_vpsll ve)
  | Ox86_VPSRL ve sz => app_w8 sz (x86_vpsrl ve)
  | Ox86_VPSRA ve sz => app_w8 sz (x86_vpsra ve)
  | Ox86_VPSLLV ve sz => app_ww sz (x86_vpsllv ve)
  | Ox86_VPSRLV ve sz => app_ww sz (x86_vpsrlv ve)
  | Ox86_VPSLLDQ sz => app_w8 sz x86_vpslldq
  | Ox86_VPSRLDQ sz => app_w8 sz x86_vpsrldq
  | Ox86_VPSHUFB sz => app_ww sz x86_vpshufb
  | Ox86_VPSHUFHW sz => app_w8 sz x86_vpshufhw
  | Ox86_VPSHUFLW sz => app_w8 sz x86_vpshuflw
  | Ox86_VPSHUFD sz => app_w8 sz x86_vpshufd
  | Ox86_VPUNPCKH ve sz => app_ww sz (x86_vpunpckh ve)
  | Ox86_VPUNPCKL ve sz => app_ww sz (x86_vpunpckl ve)
  | Ox86_VPBLENDD sz => app_ww8 sz x86_vpblendd
  | Ox86_VPBROADCAST ve sz => app_w ve (x86_vpbroadcast sz)
  | Ox86_VBROADCASTI128 => app_w U128 (x86_vpbroadcast U256)
  | Ox86_VEXTRACTI128 => app_w8 U256 x86_vextracti128
  | Ox86_VINSERTI128 => app_sopn [:: sword256 ; sword128 ; sword8 ] x86_vinserti128
  | Ox86_VPERM2I128 => app_ww8 U256 x86_vperm2i128
  | Ox86_VPERMQ => app_w8 U256 x86_vpermq
  end.

Ltac app_sopn_t := 
  match goal with
  | |- forall (_:wsize), _     => move=> ?;app_sopn_t
  | |- forall (_:velem), _     => move=> ?;app_sopn_t
  | |- forall (_:value), _     => move=> ?;app_sopn_t
  | |- forall (_:seq value), _ => move=> ?;app_sopn_t
  | |- (match ?vs with
       | [::] => type_error
       | _ :: _ => _ end = ok _) -> _ =>
    case: vs => // ??; app_sopn_t
  | |- ((Let _ := _ in _) = ok _) -> _ =>
    t_xrbindP => ??;app_sopn_t
  | |- (match ?vs with
       | [::] => _ 
       | _ :: _ => _ end = ok _) -> _ =>
       case: vs => //; app_sopn_t 
  | |- _ = ok ?a -> _ => move => /(@ok_inj _ _ _ _); app_sopn_t
  | |- ?a = ?b -> _ => (move => ?; subst a || subst b); app_sopn_t
  | _ => idtac
  end.

Lemma sopn_toutP o vs vs' : exec_sopn o vs = ok vs' ->
  List.map type_of_val vs' = sopn_tout o.
Proof.
  rewrite /exec_sopn ;case: o => /=; app_sopn_t => //;
  try (by apply: rbindP => _ _; app_sopn_t).  
  + by case:ifP => ?; case: vs => // -[<-].
  + by move=> ???? w2 w3; case: ifP => ? [<-].
  + by rewrite /x86_div;t_xrbindP => ??;case: ifP => // ? [<-].
  + by rewrite /x86_idiv;t_xrbindP => ??;case: ifP => // ? [<-].
  + by rewrite /x86_lea;t_xrbindP => ??;case: ifP => // ? [<-].
  + by rewrite /x86_ror;t_xrbindP => ??;case: ifP => // ? [<-] //; case:ifP.
  + by rewrite /x86_rol;t_xrbindP => ??;case: ifP => // ? [<-] //; case:ifP.
  + by rewrite /x86_shl;t_xrbindP => ??;case: ifP => // ? [<-] //; case:ifP.
  + by rewrite /x86_shr;t_xrbindP => ??;case: ifP => // ? [<-] //; case:ifP.
  + by rewrite /x86_sar;t_xrbindP => ??;case: ifP => // ? [<-] //; case:ifP.
  + by rewrite /x86_shld;t_xrbindP => ??;case: ifP => // ? [<-] //; case:ifP.
  + by rewrite /x86_shrd;t_xrbindP => ??;case: ifP => // ? [<-] //; case:ifP.
  by rewrite /x86_vpmull;t_xrbindP => ?? //;apply: rbindP => _ _; app_sopn_t.
Qed.

Section SEM.

Variable P:prog.

Notation gd := (p_globs P).

Definition sem_range (s : estate) (r : range) :=
  let: (d,pe1,pe2) := r in
  Let i1 := sem_pexpr gd s pe1 >>= to_int in
  Let i2 := sem_pexpr gd s pe2 >>= to_int in
  ok (wrange d i1 i2).

Definition sem_sopn gd o m lvs args :=
  sem_pexprs gd m args >>= exec_sopn o >>= write_lvals gd m lvs.

Inductive sem : estate -> cmd -> estate -> Prop :=
| Eskip s :
    sem s [::] s

| Eseq s1 s2 s3 i c :
    sem_I s1 i s2 -> sem s2 c s3 -> sem s1 (i::c) s3

with sem_I : estate -> instr -> estate -> Prop :=
| EmkI ii i s1 s2:
    sem_i s1 i s2 ->
    sem_I s1 (MkI ii i) s2

with sem_i : estate -> instr_r -> estate -> Prop :=
| Eassgn s1 s2 (x:lval) tag ty e v v':
    sem_pexpr gd s1 e = ok v ->
    truncate_val ty v = ok v' →
    write_lval gd x v' s1 = ok s2 ->
    sem_i s1 (Cassgn x tag ty e) s2

| Eopn s1 s2 t o xs es:
    sem_sopn gd o s1 xs es = ok s2 ->
    sem_i s1 (Copn xs t o es) s2

| Eif_true s1 s2 e c1 c2 :
    sem_pexpr gd s1 e = ok (Vbool true) ->
    sem s1 c1 s2 ->
    sem_i s1 (Cif e c1 c2) s2

| Eif_false s1 s2 e c1 c2 :
    sem_pexpr gd s1 e = ok (Vbool false) ->
    sem s1 c2 s2 ->
    sem_i s1 (Cif e c1 c2) s2

| Ewhile_true s1 s2 s3 s4 a c e c' :
    sem s1 c s2 ->
    sem_pexpr gd s2 e = ok (Vbool true) ->
    sem s2 c' s3 ->
    sem_i s3 (Cwhile a c e c') s4 ->
    sem_i s1 (Cwhile a c e c') s4

| Ewhile_false s1 s2 a c e c' :
    sem s1 c s2 ->
    sem_pexpr gd s2 e = ok (Vbool false) ->
    sem_i s1 (Cwhile a c e c') s2

| Efor s1 s2 (i:var_i) d lo hi c vlo vhi :
    sem_pexpr gd s1 lo = ok (Vint vlo) ->
    sem_pexpr gd s1 hi = ok (Vint vhi) ->
    sem_for i (wrange d vlo vhi) s1 c s2 ->
    sem_i s1 (Cfor i (d, lo, hi) c) s2

| Ecall s1 m2 s2 ii xs f args vargs vs :
    sem_pexprs gd s1 args = ok vargs ->
    sem_call s1.(emem) f vargs m2 vs ->
    write_lvals gd {|emem:= m2; evm := s1.(evm) |} xs vs = ok s2 ->
    sem_i s1 (Ccall ii xs f args) s2

with sem_for : var_i -> seq Z -> estate -> cmd -> estate -> Prop :=
| EForDone s i c :
    sem_for i [::] s c s

| EForOne s1 s1' s2 s3 i w ws c :
    write_var i (Vint w) s1 = ok s1' ->
    sem s1' c s2 ->
    sem_for i ws s2 c s3 ->
    sem_for i (w :: ws) s1 c s3

with sem_call : mem -> funname -> seq value -> mem -> seq value -> Prop :=
| EcallRun m1 m2 fn f vargs vargs' s1 vm2 vres vres' :
    get_fundef (p_funcs P) fn = Some f ->
    mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
    write_vars f.(f_params) vargs (Estate m1 vmap0) = ok s1 ->
    sem s1 f.(f_body) (Estate m2 vm2) ->
    mapM (fun (x:var_i) => get_var vm2 x) f.(f_res) = ok vres ->
    mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
    sem_call m1 fn vargs'  m2 vres'.

(* -------------------------------------------------------------------- *)
(* The generated scheme is borring to use *)
(*
Scheme sem_Ind    := Induction for sem      Sort Prop
with sem_i_Ind    := Induction for sem_i    Sort Prop
with sem_I_Ind    := Induction for sem_I    Sort Prop
with sem_for_Ind  := Induction for sem_for  Sort Prop
with sem_call_Ind := Induction for sem_call Sort Prop.
*)

Section SEM_IND.
  Variables
    (Pc   : estate -> cmd -> estate -> Prop)
    (Pi_r : estate -> instr_r -> estate -> Prop)
    (Pi : estate -> instr -> estate -> Prop)
    (Pfor : var_i -> seq Z -> estate -> cmd -> estate -> Prop)
    (Pfun : mem -> funname -> seq value -> mem -> seq value -> Prop).

  Definition sem_Ind_nil : Prop :=
    forall s : estate, Pc s [::] s.

  Definition sem_Ind_cons : Prop :=
    forall (s1 s2 s3 : estate) (i : instr) (c : cmd),
      sem_I s1 i s2 -> Pi s1 i s2 -> sem s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.

  Hypotheses
    (Hnil: sem_Ind_nil)
    (Hcons: sem_Ind_cons)
  .

  Definition sem_Ind_mkI : Prop :=
    forall (ii : instr_info) (i : instr_r) (s1 s2 : estate),
      sem_i s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.

  Hypothesis HmkI : sem_Ind_mkI.

  Definition sem_Ind_assgn : Prop :=
    forall (s1 s2 : estate) (x : lval) (tag : assgn_tag) ty (e : pexpr) v v',
      sem_pexpr gd s1 e = ok v ->
      truncate_val ty v = ok v' →
      write_lval gd x v' s1 = Ok error s2 ->
      Pi_r s1 (Cassgn x tag ty e) s2.

  Definition sem_Ind_opn : Prop :=
    forall (s1 s2 : estate) t (o : sopn) (xs : lvals) (es : pexprs),
      sem_sopn gd o s1 xs es = Ok error s2 ->
      Pi_r s1 (Copn xs t o es) s2.

  Definition sem_Ind_if_true : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
      sem_pexpr gd s1 e = ok (Vbool true) ->
      sem s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.

  Definition sem_Ind_if_false : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
      sem_pexpr gd s1 e = ok (Vbool false) ->
      sem s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.

  Definition sem_Ind_while_true : Prop :=
    forall (s1 s2 s3 s4 : estate) a (c : cmd) (e : pexpr) (c' : cmd),
      sem s1 c s2 -> Pc s1 c s2 ->
      sem_pexpr gd s2 e = ok (Vbool true) ->
      sem s2 c' s3 -> Pc s2 c' s3 ->
      sem_i s3 (Cwhile a c e c') s4 -> Pi_r s3 (Cwhile a c e c') s4 -> Pi_r s1 (Cwhile a c e c') s4.

  Definition sem_Ind_while_false : Prop :=
    forall (s1 s2 : estate) a (c : cmd) (e : pexpr) (c' : cmd),
      sem s1 c s2 -> Pc s1 c s2 ->
      sem_pexpr gd s2 e = ok (Vbool false) ->
      Pi_r s1 (Cwhile a c e c') s2.

  Hypotheses
    (Hasgn: sem_Ind_assgn)
    (Hopn: sem_Ind_opn)
    (Hif_true: sem_Ind_if_true)
    (Hif_false: sem_Ind_if_false)
    (Hwhile_true: sem_Ind_while_true)
    (Hwhile_false: sem_Ind_while_false)
  .

  Definition sem_Ind_for : Prop :=
    forall (s1 s2 : estate) (i : var_i) (d : dir) (lo hi : pexpr) (c : cmd) (vlo vhi : Z),
      sem_pexpr gd s1 lo = ok (Vint vlo) ->
      sem_pexpr gd s1 hi = ok (Vint vhi) ->
      sem_for i (wrange d vlo vhi) s1 c s2 ->
      Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.

  Definition sem_Ind_for_nil : Prop :=
    forall (s : estate) (i : var_i) (c : cmd),
      Pfor i [::] s c s.

  Definition sem_Ind_for_cons : Prop :=
    forall (s1 s1' s2 s3 : estate) (i : var_i) (w : Z) (ws : seq Z) (c : cmd),
      write_var i w s1 = Ok error s1' ->
      sem s1' c s2 -> Pc s1' c s2 ->
      sem_for i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.

  Hypotheses
    (Hfor: sem_Ind_for)
    (Hfor_nil: sem_Ind_for_nil)
    (Hfor_cons: sem_Ind_for_cons)
  .

  Definition sem_Ind_call : Prop :=
    forall (s1 : estate) (m2 : mem) (s2 : estate)
           (ii : inline_info) (xs : lvals)
           (fn : funname) (args : pexprs) (vargs vs : seq value),
      sem_pexprs gd s1 args = Ok error vargs ->
      sem_call (emem s1) fn vargs m2 vs -> Pfun (emem s1) fn vargs m2 vs ->
      write_lvals gd {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
      Pi_r s1 (Ccall ii xs fn args) s2.

  Definition sem_Ind_proc : Prop :=
    forall (m1 m2 : mem) (fn:funname) (f : fundef) (vargs vargs': seq value)
           (s1 : estate) (vm2 : vmap) (vres vres': seq value),
      get_fundef (p_funcs P) fn = Some f ->
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
      sem s1 (f_body f) {| emem := m2; evm := vm2 |} ->
      Pc s1 (f_body f) {| emem := m2; evm := vm2 |} ->
      mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
      mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
      Pfun m1 fn vargs' m2 vres'.

  Hypotheses
    (Hcall: sem_Ind_call)
    (Hproc: sem_Ind_proc)
  .

  Fixpoint sem_Ind (e : estate) (l : cmd) (e0 : estate) (s : sem e l e0) {struct s} :
    Pc e l e0 :=
    match s in (sem e1 l0 e2) return (Pc e1 l0 e2) with
    | Eskip s0 => Hnil s0
    | @Eseq s1 s2 s3 i c s0 s4 =>
        @Hcons s1 s2 s3 i c s0 (@sem_I_Ind s1 i s2 s0) s4 (@sem_Ind s2 c s3 s4)
    end

  with sem_i_Ind (e : estate) (i : instr_r) (e0 : estate) (s : sem_i e i e0) {struct s} :
    Pi_r e i e0 :=
    match s in (sem_i e1 i0 e2) return (Pi_r e1 i0 e2) with
    | @Eassgn s1 s2 x tag ty e1 v v' h1 h2 h3 => @Hasgn s1 s2 x tag ty e1 v v' h1 h2 h3
    | @Eopn s1 s2 t o xs es e1 => @Hopn s1 s2 t o xs es e1
    | @Eif_true s1 s2 e1 c1 c2 e2 s0 =>
      @Hif_true s1 s2 e1 c1 c2 e2 s0 (@sem_Ind s1 c1 s2 s0)
    | @Eif_false s1 s2 e1 c1 c2 e2 s0 =>
      @Hif_false s1 s2 e1 c1 c2 e2 s0 (@sem_Ind s1 c2 s2 s0)
    | @Ewhile_true s1 s2 s3 s4 a c e1 c' h1 h2 h3 h4 =>
      @Hwhile_true s1 s2 s3 s4 a c e1 c' h1 (@sem_Ind s1 c s2 h1) h2 h3 (@sem_Ind s2 c' s3 h3) 
          h4 (@sem_i_Ind s3 (Cwhile a c e1 c') s4 h4)
    | @Ewhile_false s1 s2 a c e1 c' s0 e2 =>
      @Hwhile_false s1 s2 a c e1 c' s0 (@sem_Ind s1 c s2 s0) e2
    | @Efor s1 s2 i0 d lo hi c vlo vhi e1 e2 s0 =>
      @Hfor s1 s2 i0 d lo hi c vlo vhi e1 e2 s0
        (@sem_for_Ind i0 (wrange d vlo vhi) s1 c s2 s0)
    | @Ecall s1 m2 s2 ii xs f13 args vargs vs e2 s0 e3 =>
      @Hcall s1 m2 s2 ii xs f13 args vargs vs e2 s0
        (@sem_call_Ind (emem s1) f13 vargs m2 vs s0) e3
    end

  with sem_I_Ind (e : estate) (i : instr) (e0 : estate) (s : sem_I e i e0) {struct s} :
    Pi e i e0 :=
    match s in (sem_I e1 i0 e2) return (Pi e1 i0 e2) with
    | @EmkI ii i0 s1 s2 s0 => @HmkI ii i0 s1 s2 s0 (@sem_i_Ind s1 i0 s2 s0)
    end

  with sem_for_Ind (v : var_i) (l : seq Z) (e : estate) (l0 : cmd) (e0 : estate)
         (s : sem_for v l e l0 e0) {struct s} : Pfor v l e l0 e0 :=
    match s in (sem_for v0 l1 e1 l2 e2) return (Pfor v0 l1 e1 l2 e2) with
    | EForDone s0 i c => Hfor_nil s0 i c
    | @EForOne s1 s1' s2 s3 i w ws c e1 s0 s4 =>
      @Hfor_cons s1 s1' s2 s3 i w ws c e1 s0 (@sem_Ind s1' c s2 s0)
         s4 (@sem_for_Ind i ws s2 c s3 s4)
    end

  with sem_call_Ind (m : mem) (f13 : funname) (l : seq value) (m0 : mem)
         (l0 : seq value) (s : sem_call m f13 l m0 l0) {struct s} : Pfun m f13 l m0 l0 :=
    match s with
    | @EcallRun m1 m2 fn f vargs vargs' s1 vm2 vres vres' Hget Hctin Hw Hsem Hvres Hctout =>
       @Hproc m1 m2 fn f vargs vargs' s1 vm2 vres vres' Hget Hctin Hw Hsem (sem_Ind Hsem) Hvres Hctout
    end.

End SEM_IND.

Lemma of_val_undef t t':
  of_val t (Vundef t') =
    Error (if subtype t t' then ErrAddrUndef else ErrType).
Proof.
  by case: t t' => //= [  [] |  [] | p| s []] // [].
Qed.

Lemma of_val_undef_ok t t' v:
  of_val t (Vundef t') <> ok v.
Proof. by rewrite of_val_undef. Qed.

Lemma of_varr t n (a:WArray.array n) z :
  of_val t (Varr a) = ok z -> subtype t (sarr n).
Proof.
  by case: t z => //= n' z; rewrite /WArray.cast; case: ifP.
Qed.

Lemma of_vword t s (w: word s) z :
  of_val t (Vword w) = ok z -> exists s', (s' <= s)%CMP /\ t = sword s'.
Proof.
  case: t z => //= s' w'.
  exists s';split => //=.
  by move: H; rewrite /truncate_word;  case: (s' <= s)%CMP => //=.
Qed.

Lemma of_vint t n z :
  of_val t (Vint n) = ok z -> t = sint.
Proof.
  case: t z => //= s' w'.
Qed.

End SEM.
