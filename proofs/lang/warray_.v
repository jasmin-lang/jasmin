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

Variant arr_access := 
  | AAdirect
  | AAscale.

Scheme Equality for arr_access.

Lemma arr_access_eq_axiom : Equality.axiom arr_access_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_arr_access_dec_bl.
  by apply: internal_arr_access_dec_lb.
Qed.

Definition arr_access_eqMixin     := Equality.Mixin arr_access_eq_axiom.
Canonical  arr_access_eqType      := Eval hnf in EqType arr_access arr_access_eqMixin.

Local Open Scope Z_scope.

Definition arr_size (ws:wsize) (len:positive)  := 
   (wsize_size ws * len).

Lemma arr_sizeE ws len : arr_size ws len = (wsize_size ws * len).
Proof. done. Qed.

Lemma ge0_arr_size ws len : 0 <= arr_size ws len.
Proof. rewrite arr_sizeE; have := wsize_size_pos ws; nia. Qed.

Opaque arr_size.

Definition mk_scale (aa:arr_access) ws := 
  if aa is AAscale then wsize_size ws else 1.

Module WArray.

  Record array (s:positive)  :=
    { arr_data : Mz.t u8 }.

  Definition empty (s:positive) : array s :=
    {| arr_data := Mz.empty _ |}.

  Local Notation pointer := [eqType of Z].

  Local Instance PointerZ : pointer_op pointer.
    refine {|
        add x y := (x + y)%Z;
        sub x y := (x - y)%Z;
      |}.
  Proof.
    - abstract (move => /= ??; ring).
    - abstract (move => /= ?; ring).
  Defined.

  Lemma addE x y : add x y = (x + y)%Z.
  Proof. by []. Qed.

  Lemma subE x y : sub x y = (x - y)%Z.
  Proof. by []. Qed.

  Global Opaque PointerZ.

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

    Definition is_align (p:pointer) ws := (p mod wsize_size ws == 0)%Z.

    Lemma is_align8 (p:pointer) : is_align p U8.
    Proof. by rewrite /is_align /wsize_size Z.mod_1_r. Qed.

    Lemma is_align_scale (p:pointer) ws : is_align (p * mk_scale AAscale ws)%Z ws.
    Proof. by rewrite /is_align /mk_scale /= Z_mod_mult. Qed.

    Definition validw (m:array s) (p:pointer) (ws:wsize) : exec unit := 
      Let _ := assert (in_range p ws) ErrOob in
      assert (is_align p ws) ErrAddrInvalid.

    Definition validr (m:array s) (p:pointer) (ws:wsize) :=
      Let _ := validw m p ws in
      assert (all (fun i => Mz.get m.(arr_data) (p+i)%Z != None) (ziota 0 (wsize_size ws)))
             ErrAddrInvalid.

    Lemma sub_add m p sw i t: validw m p sw = ok t -> (0 <= i < wsize_size sw)%Z -> sub (add p i) p = i.
    Proof. rewrite addE subE => _ _; ring. Qed.

    Lemma validw_uset m p v p' sw: validw (uset m p v) p' sw = validw m p' sw.
    Proof. done. Qed.

    Lemma validw8 m2 m1 p sw i t:
      (0 <= i < wsize_size sw)%Z ->
      validw m1 p sw = ok t -> validw m2 (add p i) U8 = ok tt.
    Proof.
      move=> hi;rewrite /validw /assert is_align8; case: in_rangeP => // h1 _. 
      by case: in_rangeP => //; rewrite /wsize_size addE; Psatz.nia.
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
      case: t; rewrite /validr /= Z.add_0_r /validw /assert /add is_align8.
      case: in_rangeP => //= hw _ hi.
      case: in_rangeP; rewrite /= /wsize_size => h.
      + by rewrite Mz.setP !andbT; case: (_ =P k). 
      case: eqP => //; Psatz.nia.
    Qed.

    Lemma usetP m z1 z2 v:
      uget (uset m z1 v) z2 = if z1 == z2 then v else uget m z2.
    Proof. by rewrite /uget /uset /= Mz.setP; case: eqP. Qed.

    Global Instance array_CM : coreMem PointerZ (array s) :=
      CoreMem sub_add validw_uset
        validrP validw_validr usetP.

  End CM.

  Definition get len (aa:arr_access) ws (a:array len) (p:Z) :=
    CoreMem.read a (p * mk_scale aa ws)%Z ws.
 
  Definition set {len ws} (a:array len) aa p (v:word ws) : exec (array len) :=   
    CoreMem.write a (p * mk_scale aa ws)%Z v.

  Definition get_sub_data (aa:arr_access) ws len (a:Mz.t u8) p := 
     let size := arr_size ws len in 
     let start := (p * mk_scale aa ws)%Z in
     foldr (fun i data => 
       match Mz.get a (start + i) with
       | None => Mz.remove data i
       | Some w => Mz.set data i w
       end) (Mz.empty _) (ziota 0 size).


  Definition get_sub lena (aa:arr_access) ws len (a:array lena) p  : exec (array (Z.to_pos (arr_size ws len))) := 
     let size := arr_size ws len in 
     let start := (p * mk_scale aa ws)%Z in
     if (0 <=? start) && (start + size <=? lena) then
       ok (Build_array (Z.to_pos size) (get_sub_data aa ws len (arr_data a) p))
     else Error ErrOob.

  Definition set_sub_data (aa:arr_access) ws len (a:Mz.t u8) p (b:Mz.t u8) := 
    let size := arr_size ws len in 
    let start := (p * mk_scale aa ws)%Z in
    foldr (fun i data => 
      match Mz.get b i with
      | None => Mz.remove data (start + i)
      | Some w => Mz.set data (start + i) w
      end) a (ziota 0 size).

  Definition set_sub lena (aa:arr_access) ws len (a:array lena) p (b:array (Z.to_pos (arr_size ws len))) : exec (array lena) := 
    let size := arr_size ws len in 
    let start := (p * mk_scale aa ws)%Z in
    if (0 <=? start) && (start + size <=? lena) then
      ok (Build_array lena (set_sub_data aa ws len (arr_data a) p (arr_data b)))
    else Error ErrOob.

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
    move=> [h1 h2]; rewrite /validw; t_xrbindP => tt1 /assertP /in_rangeP hi. 
    case: (is_align i ws) => //= _; case: in_rangeP => //; nia.
  Qed.

  Lemma uincl_validr {len1 len2} (a1 : array len1) (a2 : array len2) ws i t :
    uincl a1 a2 -> validr a1 i ws = ok t -> validr a2 i ws = ok tt.
  Proof.
    move=> [h1 h2]; rewrite /validr /validw; t_xrbindP => t1 t2. 
    case: in_rangeP => //= hi1 _ {t2} /assertP -> /= /assertP /allP h.
    case: in_rangeP => //= hi2; last by nia.
    case: allP => // -[] k hk; have := h _ hk.
    move: hk; rewrite in_ziota !zify Z.add_0_l => hk.
    by case: Mz.get (h2 (i+k)%Z) => //= v /(_ _ _ erefl) -> //; nia.
  Qed.

  Lemma uincl_get {len1 len2} (a1 : array len1) (a2 : array len2) aa ws i w :
    uincl a1 a2 ->
    get aa ws a1 i = ok w ->
    get aa ws a2 i = ok w.
  Proof.
    rewrite /get /CoreMem.read /=; t_xrbindP => hu t hr.
    have -> := uincl_validr hu hr => /= <-; do 2 f_equal.
    rewrite /CoreMem.uread; apply eq_map_ziota; rewrite Z.add_0_l => k hk /=.
    rewrite /add /uget; case: hu => h1 /(_ (i * mk_scale aa ws + k)%Z).
    have := validrP hr hk; rewrite /validr /= Z.add_0_r; t_xrbindP => ? _ /assertP.
    case: Mz.get => //= v _ /(_ v _ erefl) -> //.
    by move: hr; rewrite /validr /validw; case: in_rangeP => //= ? _; nia.
  Qed.
 
  Lemma uincl_set {ws len1 len2} (a1 a1': array len1) (a2: array len2) aa i (w:word ws) :
    uincl a1 a2 ->
    set a1 aa i w = ok a1' ->
    exists a2', set a2 aa i w = ok a2' /\ uincl a1' a2'.
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
    rewrite is_align8 /= => _ _; rewrite hg1 /=.
    have := h2 k _ hk; case: Mz.get => //= v1 /(_ _ erefl) -> _ /=.
    by case: Mz.get => //= ? _ ->.
  Qed.

  Lemma uincl_refl len (a: array len) : uincl a a.
  Proof. by split => //; reflexivity. Qed.

  Lemma uincl_trans {len1 len2 len3} 
    (a2: array len2) (a1: array len1) (a3: array len3) :
    uincl a1 a2 -> uincl a2 a3 -> uincl a1 a3. 
  Proof.
    move=> [l1 h1] [l2 h2]; split; first by lia.
    move=> ????;apply h2;first by lia.
    by apply h1.
  Qed.
 
  Lemma mk_scale_U8 aa : mk_scale aa U8 = 1%Z.
  Proof. by rewrite /mk_scale wsize8; case aa. Qed.

  Lemma set_get8 len (m m':array len) aa p ws (v: word ws) k :    
    set m aa p v = ok m' ->
    get AAscale U8 m' k = 
      let i := (k - p * mk_scale aa ws)%Z in
       if ((0 <=? i) && (i <? wsize_size ws))%Z then ok (LE.wread8 v i)
       else get AAscale U8 m k.
  Proof. 
    by move=> hs; have := CoreMem.write_read8 k hs; rewrite /get mk_scale_U8 Z.mul_1_r. 
  Qed.

  Lemma set_zget8 len (m m':array len) aa p ws (v: word ws) k :    
    (0 <= k < len)%Z ->
    set m aa p v = ok m' ->
    Mz.get m'.(arr_data) k= 
      let i := (k - p * mk_scale aa ws)%Z in
       if ((0 <=? i) && (i <? wsize_size ws))%Z then Some (LE.wread8 v i)
       else Mz.get m.(arr_data) k.
  Proof.
    move=> hk; rewrite /set /CoreMem.write; t_xrbindP => ? /= hw <-.
    have /= := CoreMem.uwrite_uget (CM := array_CM _) v k hw.
    have /= := CoreMem.uwrite_validr8 (CM := array_CM _) v k hw.
    move: hw; rewrite /validr /validw; t_xrbindP => t1 /assertP/in_rangeP hw /assertP hal.
    rewrite is_align8  /= /sub /validw /uget.
    case: in_rangeP; last by rewrite wsize8; nia.
    case: ifPn; rewrite !zify wsize8 Z.add_0_r => ? _ /=.
    + by case: Mz.get => //= ? _ ->.
    by case: Mz.get => /=; case: Mz.get =>//= ??? ->.
  Qed.

  Lemma set_validr_eq len (m m':array len) aa p ws (v: word ws) :
    set m aa p v = ok m' ->
    validr m' (p * mk_scale aa ws)%Z ws = ok tt.
  Proof.
    move=> hset; have := set_zget8 _ hset; move: hset.
    rewrite /set /CoreMem.write /validr /=; t_xrbindP => ? hw1 <-.
    move: (hw1); rewrite /validw; t_xrbindP => t1 /assertP /dup [] /in_rangeP hp -> -> hz /=.
    case: allP => //= -[] k; rewrite in_ziota !zify Z.add_0_l => hk.
    rewrite hz; last by nia.
    case: ifPn => //=; rewrite !zify; nia.
  Qed.

  Lemma setP_eq len (m m':array len) aa p ws (v: word ws) :
    set m aa p v = ok m' ->
    get aa ws m' p = ok v.
  Proof.
    move=> h1;have := CoreMem.writeP_eq h1.
    rewrite /get /CoreMem.read /= (set_validr_eq h1) /= => ->.
    by rewrite LE.decodeK.
  Qed.

  Lemma mk_scale_bound aa ws : (1 <= mk_scale aa ws <= wsize_size ws)%Z.
  Proof. rewrite /mk_scale; have := wsize_size_pos ws; case:aa; lia. Qed.

  Lemma set_validr_neq len (m m':array len) p1 p2 ws (v: word ws) :
    p1 != p2 -> 
    set m AAscale p1 v = ok m' ->
    validr m' (p2 * mk_scale AAscale ws)%Z ws = validr m (p2 * mk_scale AAscale ws)%Z ws.
  Proof.
    move=> /eqP hp hset; have := set_zget8 _ hset; move: hset.
    rewrite /set /CoreMem.write /validr /=; t_xrbindP => ? hw1 <-.
    move: (hw1); rewrite /validw /validr; t_xrbindP => t1 /assertP /in_rangeP hp1. 
    rewrite !is_align_scale => /= _ hz.
    case: in_rangeP => hp2 //=; f_equal.
    apply all_ziota => i hi; rewrite hz; last by nia.
    case: ifPn => //=; rewrite !zify;  nia.
  Qed.

  Lemma setP_neq len (m m':array len) p1 p2 ws (v: word ws) :
    p1 != p2 ->
    set m AAscale p1 v = ok m' -> 
    get AAscale ws m' p2 = get AAscale ws m p2.
  Proof.
    move=> hp h1;have := CoreMem.writeP_neq h1.
    rewrite /get /CoreMem.read /= (set_validr_neq hp h1) /= => -> //.
    move: hp => /eqP hp ????; rewrite !addE; nia.
  Qed.

  Lemma setP len (m m':array len) p1 p2 ws (v: word ws) :
    set m AAscale p1 v = ok m' -> 
    get AAscale ws m' p2 = if p1 == p2 then ok v else get AAscale ws m p2.
  Proof. by case: eqP => [<- | /eqP];[ apply setP_eq | apply setP_neq]. Qed.

  Definition filter (m : Mz.t u8) p := 
    Mz.fold (fun k e m => if (k <? p)%Z then Mz.set m k e else m) m (Mz.empty _).

  Definition inject len len' (a:array len) : array len' :=
    if (len <? len')%Z then {| arr_data := filter a.(arr_data) len |}
    else {| arr_data := a.(arr_data) |}.

  Lemma zget_inject len (a:array len) (p:positive) i: 
    (0 <= i < p)%Z ->
    Mz.get (arr_data (inject p a)) i = 
    if (i <? len)%Z then Mz.get (arr_data a) i else None.
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

  Lemma get_bound ws len aa (t:array len) i w :
    get aa ws t i = ok w -> 
    [/\ 0 <= i * mk_scale aa ws,
        i * mk_scale aa ws + wsize_size ws <= len &
        is_align (i * mk_scale aa ws) ws]%Z.
  Proof.
    rewrite /get /CoreMem.read /= /validr /validw; t_xrbindP => ??? /assertP /in_rangeP ? /assertP ->. 
    have := mk_scale_bound aa ws => *;split => //; nia.
  Qed.     

  Lemma set_bound ws len aa (a t:array len) i (w:word ws) :
    set a aa i w = ok t -> 
    [/\ 0 <= i * mk_scale aa ws,
        i * mk_scale aa ws +  wsize_size ws <= len &
        is_align (i * mk_scale aa ws) ws]%Z.
  Proof.
    rewrite /set /CoreMem.write /= /validw /validr; t_xrbindP => ?? /assertP /in_rangeP ? /assertP ->.
    have := mk_scale_bound aa ws => *; split => //;nia.
  Qed.

  Lemma get_uget len aa (t:array len) i v :
    get aa U8 t i = ok v -> uget t i = v.
  Proof.
    rewrite /get /CoreMem.read mk_scale_U8 /=; t_xrbindP => ?? <-.
    by rewrite CoreMem.uread8_get Z.mul_1_r.
  Qed.

  Lemma get_get8 ws len (t:array len) aa aa' i w k :
    get aa ws t i = ok w -> 
    (0 <= k < wsize_size ws)%Z ->
    exists v, get aa' U8 t (i * mk_scale aa ws + k) = ok v.
  Proof.
    rewrite /get /CoreMem.read /= /validr /validw; t_xrbindP.
    move=> ??? /assertP /in_rangeP h1 /assertP ha /assertP /allP h2 ? hk /=.
    rewrite is_align8 mk_scale_U8 Z.mul_1_r Z.add_0_r /=.
    have -> /= : in_range len (i * mk_scale aa ws + k)%Z U8.
    + by rewrite /in_range !zify wsize8; nia.
    rewrite h2 /=; first by eauto.
    by rewrite in_ziota !zify.
  Qed.

  Lemma get0 (n:positive) aa off : (0 <= off ∧ off < n)%Z -> 
    get aa U8 (empty n) off = Error ErrAddrInvalid.
  Proof.
    rewrite /get /CoreMem.read /= /validr /validw /= /in_range mk_scale_U8 wsize8 Z.mul_1_r is_align8.
    case: andP => //; rewrite !zify; lia.
  Qed.

  Lemma set_sub_data_zget8 aa ws a len p t k: 
    Mz.get (@set_sub_data aa ws len a p t) k = 
      let i := (k - p * mk_scale aa ws)%Z in
      if (0 <=? i) && (i <? arr_size ws len) then Mz.get t i 
      else Mz.get a k.
  Proof.
    rewrite /set_sub_data. 
    elim /natlike_ind: (arr_size ws len) a; last by apply ge0_arr_size.
    + move=> data; rewrite ziota0 /=; case: andP => // -[]; rewrite !zify; lia.
    move=> sz hsz ih data; rewrite ziotaS_cat // foldr_cat Z.add_0_l /= ih.
    case: ifPn; rewrite !zify => h3; case: ifPn; rewrite !zify => h4 //.
    + nia. 
    + case heq: (Mz.get t) => [w|].
      + rewrite Mz.setP; case: eqP => [<- | ?]; last nia.
        rewrite -heq; f_equal; ring. 
      rewrite Mz.removeP; case eqP => [<- | ?]; last nia.
      rewrite -heq; f_equal; ring.
    case heq: (Mz.get t) => [w|].
    + rewrite Mz.setP; case: eqP => [? | //]; lia.
    rewrite Mz.removeP; case eqP => [? | //]; lia.
  Qed.

  Lemma set_sub_zget8 aa ws lena a len p t a' k: 
    @set_sub lena aa ws len a p t = ok a' -> 
    Mz.get (WArray.arr_data a') k = 
      let i := (k - p * mk_scale aa ws)%Z in
      if (0 <=? i) && (i <? arr_size ws len) then Mz.get (arr_data t) i 
      else Mz.get (arr_data a) k.
  Proof.
    rewrite /set_sub; case: andP => // -[h1 h2] [<-] /=.
    by rewrite set_sub_data_zget8.
  Qed.

  Lemma get_sub_data_zget8 aa ws a len p k: 
    Mz.get (get_sub_data aa ws len a p) k = 
      let start := (p * mk_scale aa ws)%Z in
      if (0 <=? k) && (k <? arr_size ws len) then Mz.get a (start + k) 
      else None.
  Proof.
    rewrite /get_sub_data -(Mz.get0 u8 k).
    elim /natlike_ind: (arr_size ws len) (Mz.empty u8); last by apply ge0_arr_size.
    + move => b; rewrite ziota0 /=; case: andP => //; rewrite !zify; lia.
    move=> sz hsz ih b; rewrite ziotaS_cat // foldr_cat Z.add_0_l /= ih.
    case: ifPn; rewrite !zify => h3; case: ifPn; rewrite !zify => h4 //.
    + nia. 
    + case heq: (Mz.get a) => [w|].
      + by rewrite Mz.setP; case: eqP => [<- | ]; [rewrite heq | nia].
      by rewrite Mz.removeP; case: eqP => [<- | ]; [rewrite heq | nia].
    case heq: (Mz.get a) => [w|].
    + by rewrite Mz.setP; case: eqP => //; nia.
    by rewrite Mz.removeP; case: eqP => //; nia.
  Qed.

  Lemma get_sub_zget8 aa ws lena a len p a' k: 
    @get_sub lena aa ws len a p = ok a' -> 
    Mz.get (WArray.arr_data a') k = 
      let start := (p * mk_scale aa ws)%Z in
      if (0 <=? k) && (k <? arr_size ws len) then Mz.get (WArray.arr_data a) (start + k) 
      else None.
  Proof.
    rewrite /get_sub; case: andP => // -[h1 h2] [<-] /=.
    by rewrite get_sub_data_zget8.
  Qed.

  Lemma uincl_get_sub {len1 len2} (a1 : array len1) (a2 : array len2) 
      aa ws len i t1 :
    uincl a1 a2 ->
    get_sub aa ws len a1 i = ok t1 ->
    exists2 t2, get_sub aa ws len a2 i = ok t2 & uincl t1 t2.
  Proof. 
    move=> [hlen hget]; rewrite /get_sub; case: ifP => //.
    rewrite !zify => hlen1 [<-] {t1}.
    case:ifPn; rewrite !zify => hlen2; last by lia.
    eexists; first reflexivity; split; first lia.
    move=> k w /= hk.
    rewrite !get_sub_data_zget8 /=; case:ifP => //; rewrite !zify => ?.
    apply hget; lia.
  Qed.

  Lemma uincl_set_sub {ws len1 len2 len} (a1 a1': array len1) (a2: array len2) aa i 
        (t1 t2:array (Z.to_pos (arr_size ws len))) :
    uincl a1 a2 -> uincl t1 t2 ->
    set_sub aa a1 i t1 = ok a1' ->
    exists2 a2', set_sub aa a2 i t2 = ok a2' & uincl a1' a2'.
  Proof.
    move=> [hlen1 hget1] [hlen2 hget2].    
    rewrite /set_sub; case: ifP => //; rewrite !zify => h [<-].
    case: ifPn => //; rewrite !zify => h'; last by lia.
    eexists; first reflexivity; split; first lia.
    by move=> k w /= hk; rewrite !set_sub_data_zget8 /=; case:ifPn; rewrite !zify => ?; auto.
  Qed.

  Definition all_defined (p : positive) (a : array p) :=
    all (fun i => Mz.get a.(arr_data) i != None) (ziota 0 p).

  Lemma all_definedP (p : positive) (a : array p) : reflect (forall i , (0 <= i < p) -> Mz.get a.(arr_data) i <> None) (all_defined a).
  Proof.
    apply: (iffP allP).
    + move=> def_a i [le0i ltip]; apply/eqP/def_a.
      by rewrite in_ziota /= -(rwP andP) -!lteZP.
    + move => def_a i.
      rewrite in_ziota /= => /andP [] /leZP le0i /ltZP ltip.
      by apply/eqP/def_a.
  Qed.
  
  Definition copy (p : positive) : array p -> array p :=
    λ a, a.

  Lemma uincl_equal (p : positive) (z z' : array p):
    WArray.uincl z z' -> all_defined z -> z = z'.
  Proof.
    move => [_ Hu] Had.
    have Hget := (all_definedP _ Had).
    (*I still don't know how to transform the equality into an equality for all i between 0 and p.*)
    have Heq : ∀ i : Z, Mz.get (arr_data z) i = Mz.get (arr_data z') i ; last first.
    + by admit.
    move => i.
    have Hui := (Hu i). (*Any easier way to specialize Hu?*)
    have Hgeti := (Hget i).
    case : (Z_le_gt_dec 0 i) ; last first.
    + by admit.
    case : (Z_lt_ge_dec i p) ; last first.
    + by admit.
    move => ltip le0i.
    have Hgetiz : Mz.get (arr_data z) i ≠ None by apply Hgeti.
    have Huiz : ∀ v : u8, Mz.get (arr_data z) i = Some v → Mz.get (arr_data z') i = Some v by move => v ; apply Hui.
    move : Hgetiz Huiz.
    clear Hu Had Hget Hui Hgeti le0i ltip.
    case : (Mz.get (arr_data z) i) ; last by rewrite //=.
    by move => v _ <-.
  Admitted.


End WArray.

Hint Resolve WArray.uincl_refl.
