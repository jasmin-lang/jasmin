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
Require Export ZArith Setoid Morphisms.
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Psatz xseq.
Require Export utils array gen_map type word low_memory.
Import Utf8 ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.
Module WArray.

  Definition arr_size (ws:wsize) (s:positive)  :=
    wsize_size ws * s.

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

Hint Resolve WArray.uincl_refl : core.
