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

  (* We set the priority to 1, so that memory_model.Pointer is selected by
     default.
  *)
  Instance PointerZ : pointer_op pointer | 1.
  Proof.
    refine {| add x y := (x + y)%Z
            ; sub x y := (x - y)%Z
            ; p_to_z x := x        |}.
    - abstract (move => /= ??; ring).
    - abstract (move => /= ???; ring).
    - abstract (move => /= ?; ring).
  Defined.

  Lemma addE x y : add x y = (x + y)%Z.
  Proof. by []. Qed.

  Lemma subE x y : sub x y = (x - y)%Z.
  Proof. by []. Qed.

  Lemma p_to_zE x : p_to_z x = x.
  Proof. by []. Qed.

  Global Opaque PointerZ.

  Section WITH_POINTER_DATA.
  Context {pd: PointerData}.

  Lemma is_align_scale (p:pointer) ws : is_align (p * mk_scale AAscale ws)%Z ws.
  Proof. by rewrite /is_align /mk_scale /= Z_mod_mult. Qed.

  Lemma arr_is_align i ws :
    is_align (wrepr Uptr i) ws = is_align i ws.
  Proof.
    by rewrite /is_align p_to_zE memory_model.p_to_zE wunsigned_repr mod_wbase_wsize_size.
  Qed.

  Section CM.
    Variable (s:positive).

    Definition in_bound (_:array s) p := (0 <=? p) && (p <? s).
   
    Lemma in_boundP m p : reflect (0 <= p < s) (in_bound m p).
    Proof. by apply (iffP andP); rewrite !zify. Qed.

    Definition is_init (m:array s) (i:pointer) :=
      match Mz.get m.(arr_data) i with 
      | Some _ => true 
      | None   => false
      end.

    Definition get8 (m:array s) (i:pointer) :=
      Let _ := assert (in_bound m i) ErrOob in
      Let _ := assert (is_init m i) ErrAddrUndef in
      ok (odflt 0%R (Mz.get m.(arr_data) i)).

    Definition set8 (m:array s) (i:pointer) (v:u8) : result _ (array s):=
      Let _ := assert (in_bound m i) ErrOob in
      ok {| arr_data := Mz.set m.(arr_data) i v |}.

    Lemma valid8P m p w : reflect (exists m', set8 m p w = ok m') (in_bound m p).
    Proof.
      by (rewrite /set8; case: in_bound => /=; constructor); [eexists; eauto | move=> []].
    Qed.
 
    Lemma get_valid8 m p w : get8 m p = ok w -> in_bound m p.
    Proof. by rewrite /get8; t_xrbindP => _ /assertP. Qed.

    Lemma valid8_set m p w m' p' : set8 m p w = ok m' -> in_bound m' p' = in_bound m p'.
    Proof. by rewrite /set8; t_xrbindP => _ _ <-. Qed.

    Lemma set8P m p w p' m' :
      set8 m p w = ok m' ->
      get8 m' p' = if p == p' then ok w else get8 m p'.
    Proof.
      rewrite /get8 /set8 => /dup[] /valid8_set ->; t_xrbindP => _ /assertP hb <-.
      case heq: in_bound => //=; last by case: eqP => // h;move: heq; rewrite -h hb.
      by rewrite /is_init /= Mz.setP; case: eqP.
    Qed.

    Global Instance array_CM : coreMem pointer (array s) :=
      CoreMem set8P valid8P get_valid8 valid8_set.

    Definition in_range (p:pointer) (ws:wsize) :=
      ((0 <=? p) && (p + wsize_size ws <=? s))%Z.

    Lemma in_rangeP p ws:
      reflect (0 <= p /\ p + wsize_size ws <= s)%Z (in_range p ws).
    Proof.
      rewrite /in_range; case: andP => h; constructor; move: h; rewrite !zify; Psatz.nia.
    Qed.

    Lemma validw_in_range m p ws : validw m p ws = (is_align p ws && in_range p ws).
    Proof.
      apply (sameP (validwP m p ws)).
      apply (iffP andP).
      + move=> [] ? /in_rangeP ?;split => // k hk.
        by rewrite -valid8_validw /valid8 /= /in_bound !zify !addE; Psatz.lia.
      move=> [] ? h; split => //; apply /in_rangeP.
      move: (wsize_size_pos ws) (h 0) (h (wsize_size ws - 1)).
      by rewrite add_0 addE -!valid8_validw /array_CM /valid8 /in_bound !zify; Psatz.lia.
    Qed.

  End CM.

  Definition get len (aa:arr_access) ws (a:array len) (p:Z) :=
    CoreMem.read a (p * mk_scale aa ws)%Z ws.
 
  Definition set {len ws} (a:array len) aa p (v:word ws) : exec (array len) :=   
    CoreMem.write a (p * mk_scale aa ws)%Z v.

  Definition fcopy ws len (a t: WArray.array len) i j := 
    foldM (fun i t => 
             Let w := get AAscale ws a i in set t AAscale i w) t
          (ziota i j).

  Definition copy ws p (a:array (Z.to_pos (arr_size ws p))) := 
    fcopy ws a (WArray.empty _) 0 p.

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
    (len1 <= len2)%Z /\
    ∀ i w, read a1 i U8 = ok w -> read a2 i U8 = ok w.

  Lemma uincl_refl len (a: array len) : uincl a a.
  Proof. by split => //; reflexivity. Qed.

  Lemma uincl_trans {len1 len2 len3} 
    (a2: array len2) (a1: array len1) (a3: array len3) :
    uincl a1 a2 -> uincl a2 a3 -> uincl a1 a3. 
  Proof.
    move=> [l1 h1] [l2 h2]; split; first by lia.
    by move=> ?? /h1 /h2.
  Qed.

  End WITH_POINTER_DATA.

  Lemma castK len (a:array len) : WArray.cast len a = ok a.
  Proof. by rewrite /cast Z.leb_refl; case: a. Qed.

  Lemma cast_len len1 len2 (t2:WArray.array len2) t1: WArray.cast len1 t2 = ok t1 -> len1 <= len2.
  Proof. by rewrite /cast; case: ZleP. Qed.

  Lemma cast_empty len1 len2 : 
    WArray.cast len1 (empty len2) = if len1 <=? len2 then ok (empty len1) else type_error.
  Proof. by rewrite /WArray.cast. Qed.

  Lemma cast_empty_ok len1 len2 t: 
    WArray.cast len1 (empty len2) = ok t -> t = empty len1.
  Proof. by move=> /dup[]/cast_len/ZleP; rewrite cast_empty => -> [<-]. Qed.

  Lemma cast_get8 len1 len2 (m : array len2) m' :
    cast len1 m = ok m' ->
    forall k,
      read m' k U8 = 
        if k <? len1 then read m k U8 else Error ErrOob.
  Proof.
    rewrite /cast; case: ZleP => // hle [<-] k.
    rewrite -!get_read8 /memory_model.get /= /get8 /is_init /in_bound /=.
    by case: ZleP => /=; case: ZltP => //=; case: ZltP => //; lia.
  Qed.

  Lemma cast_uincl len1 len2 (t2 : WArray.array len2) t1 : 
    cast len1 t2 = ok t1 -> uincl t1 t2.
  Proof.
    move=> hc; split; first by apply: cast_len hc.
    by move=> i w; rewrite (cast_get8 hc); case: ifP.
  Qed.

  Lemma uincl_cast len1 len2 (a1: array len1) (a2:array len2) len a1' : 
    uincl a1 a2 ->
    cast len a1 = ok a1' ->
    exists a2', cast len a2 = ok a2' /\ uincl a1' a2'.
  Proof.
    move=> [hle hu] hc.
    have:= (cast_get8 hc). have:= @cast_get8 len len2 a2.
    move: hc; rewrite /cast; case: ZleP => // hle1 _. 
    case: ZleP => hle2 hg2 hg1; last lia.
    eexists;split; first by eauto.
    split; first by lia.
    by move=> ??; rewrite hg1 hg2 //; case: ifP => // _ /hu.
  Qed.

  Lemma mk_scale_U8 aa : mk_scale aa U8 = 1%Z.
  Proof. by rewrite /mk_scale wsize8; case aa. Qed.

  Lemma get8_read len (m : array len) aa k :
    get aa U8 m k = read m k U8.
  Proof. by rewrite /get mk_scale_U8 Z.mul_1_r. Qed.

  Lemma set_get8 len (m m':array len) aa p ws (v: word ws) :
    set m aa p v = ok m' ->
    forall k,
      read m' k U8 = 
        let i := (k - p * mk_scale aa ws)%Z in
         if ((0 <=? i) && (i <? wsize_size ws))%Z then ok (LE.wread8 v i)
         else read m k U8.
  Proof. by apply: write_read8. Qed.

  Lemma setP len (m m':array len) p1 p2 ws (v: word ws) :
    set m AAscale p1 v = ok m' -> 
    get AAscale ws m' p2 = if p1 == p2 then ok v else get AAscale ws m p2.
  Proof. 
    rewrite /set /get; case:eqP => [<- | hne hw]; first by apply writeP_eq.
    apply: (CoreMem.writeP_neq hw); move=> ??; rewrite !addE /mk_scale;nia. 
  Qed.

  Lemma setP_eq len (m m':array len) p1 ws (v: word ws) :
    set m AAscale p1 v = ok m' -> 
    get AAscale ws m' p1 = ok v.
  Proof. by move=> /setP ->; rewrite eqxx. Qed.

  Lemma setP_neq len (m m':array len) p1 p2 ws (v: word ws) :
    p1 != p2 ->
    set m AAscale p1 v = ok m' -> 
    get AAscale ws m' p2 = get AAscale ws m p2.
  Proof. by move=> /negPf h /setP ->; rewrite h. Qed.

  Lemma mk_scale_bound aa ws : (1 <= mk_scale aa ws <= wsize_size ws)%Z.
  Proof. rewrite /mk_scale; have := wsize_size_pos ws; case:aa; lia. Qed.
 
  Lemma get_bound ws len aa (t:array len) i w :
    get aa ws t i = ok w -> 
    [/\ 0 <= i * mk_scale aa ws,
        i * mk_scale aa ws + wsize_size ws <= len &
        is_align (i * mk_scale aa ws) ws]%Z.
  Proof.
    move=> hg; assert (h := readV hg); move: h.
    by rewrite validw_in_range => /andP [] ? /in_rangeP [].
  Qed.

  Lemma set_bound ws len aa (a t:array len) i (w:word ws) :
    set a aa i w = ok t -> 
    [/\ 0 <= i * mk_scale aa ws,
        i * mk_scale aa ws +  wsize_size ws <= len &
        is_align (i * mk_scale aa ws) ws]%Z.
  Proof.
    move=> hs; have : validw a (i * mk_scale aa ws) ws by apply /(writeV w); exists t.
    by rewrite validw_in_range => /andP [] ? /in_rangeP [].
  Qed.

  Lemma get_empty (n:positive) off : 
    read (empty n) off U8 = if (0 <=? off) && (off <? n) then Error ErrAddrUndef else Error ErrOob.
  Proof.
    by rewrite -get_read8 /memory_model.get /= /get8 /in_bound /is_init /=; case: ifP.
  Qed.

  Lemma get0 (n:positive) off : (0 <= off ∧ off < n)%Z -> 
    read (empty n) off U8 = Error ErrAddrUndef.
  Proof. by rewrite get_empty => -[/ZleP -> /ZltP ->]. Qed.

  Lemma uincl_empty len len' (t:array len') : 
    Zpos len <= len' -> uincl (empty len) t.
  Proof.  
    split; first Psatz.lia.
    by move=> i w; rewrite get_empty; case: ifP.
  Qed.

  Lemma uincl_validw {len1 len2} (a1 : array len1) (a2 : array len2) ws i :
    uincl a1 a2 -> validw a1 i ws -> validw a2 i ws.
  Proof.
    move=> [h1 _]; rewrite !validw_in_range => /andP [] -> /= /in_rangeP ?; apply /in_rangeP; lia.
  Qed.

  Lemma uincl_get {len1 len2} (a1 : array len1) (a2 : array len2) aa ws i w :
    uincl a1 a2 ->
    get aa ws a1 i = ok w ->
    get aa ws a2 i = ok w.
  Proof.
    rewrite /get => -[_ hu] hr; have {hr}[ha hr] := read_read8 hr.
    by rewrite (read8_read (v:=w)) ?ha // => k /hr /hu.
  Qed.
  
  Lemma uincl_set {ws len1 len2} (a1 a1': array len1) (a2: array len2) aa i (w:word ws) :
    uincl a1 a2 ->
    set a1 aa i w = ok a1' ->
    exists a2', set a2 aa i w = ok a2' /\ uincl a1' a2'.
  Proof.
    rewrite /set; set k := _ * _ => hu hw1. 
    have /(writeV w) [a2' hw2]: validw a2 k ws by apply /(uincl_validw hu) /(writeV w); exists a1'.
    exists a2'; split => //.
    case: hu => hle hu; split => //.
    move=> j wj; rewrite (write_read8 hw1) (write_read8 hw2) /=.
    by case:ifP => // _; apply: hu.
  Qed.

  Lemma fcopy_uincl ws len (a t1 t2 a1 : array len) i j: 
    uincl t1 t2 -> 
    fcopy ws a t1 i j = ok a1 -> 
    exists2 a2, fcopy ws a t2 i j = ok a2 & uincl a1 a2.
  Proof.
    rewrite /fcopy; elim: (ziota i j) t1 t2 => {i j} [ | i il hrec] t1 t2 hu /=.
    + by move=> [<-]; exists t2.
    t_xrbindP => t1' w -> hset hfold /=.    
    by have [t2' [-> /hrec ]] /= := uincl_set hu hset; apply.
  Qed.

  Lemma uincl_copy ws p a1 a2 a1' :
     uincl a1 a2 -> 
     @copy ws p a1 = ok a1' ->
     @copy ws p a2 = ok a1'.
  Proof.
    move=> hu; rewrite /copy /fcopy.
    elim: ziota (empty _) => [ | i il hrec] a //=.
    t_xrbindP => a' w /(uincl_get hu) -> /= ->; apply: hrec.
  Qed.

  Lemma set_sub_data_get8 aa ws a len p t k: 
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

  Lemma set_sub_get8 aa ws lena a len p t a' : 
    @set_sub lena aa ws len a p t = ok a' -> 
    forall k,
      read a' k U8 = 
        let i := (k - p * mk_scale aa ws)%Z in
        if (0 <=? i) && (i <? arr_size ws len) then read t i U8
        else read a k U8.
  Proof.
    rewrite /set_sub; case: andP => // -[/ZleP h1 /ZleP h2] [<-] /= k.
    rewrite -!get_read8 /memory_model.get /= /get8 /is_init /in_bound set_sub_data_get8 /=.
    case: andP; rewrite !zify //= => ?; case: andP; rewrite !zify //= => ?; lia.
  Qed.

  Lemma set_sub_bound aa ws lena a len p t a' :
    @set_sub lena aa ws len a p t = ok a' ->
    0 <= p * mk_scale aa ws /\ p * mk_scale aa ws + arr_size ws len <= lena.
  Proof. by rewrite /set_sub; case: ifP => //; rewrite !zify. Qed.

  Lemma get_sub_data_get8 aa ws a len p k: 
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

  Lemma get_sub_get8 aa ws lena a len p a' : 
    @get_sub lena aa ws len a p = ok a' -> 
    forall k,
      read a' k U8 = 
        let start := (p * mk_scale aa ws)%Z in
        if (0 <=? k) && (k <? arr_size ws len) then read a (start + k) U8
        else Error ErrOob.
  Proof.
    rewrite /get_sub; case: andP => // -[/ZleP h1 /ZleP h2] [<-] /= k.
    rewrite -!get_read8 /memory_model.get /= /get8 /is_init /in_bound get_sub_data_get8 /=.
    case: andP; rewrite !zify //= => ?; case: andP; rewrite !zify //= => ?; lia.
  Qed.

  Lemma get_sub_bound aa ws lena a len p a' :
    @get_sub lena aa ws len a p = ok a' ->
    0 <= p * mk_scale aa ws /\ p * mk_scale aa ws + arr_size ws len <= lena.
  Proof. by rewrite /get_sub; case: ifP => //; rewrite !zify. Qed.

  Lemma uincl_get_sub {len1 len2} (a1 : array len1) (a2 : array len2) 
      aa ws len i t1 :
    uincl a1 a2 ->
    get_sub aa ws len a1 i = ok t1 ->
    exists2 t2, get_sub aa ws len a2 i = ok t2 & uincl t1 t2.
  Proof. 
    move=> [hlen hu] hget.
    have := get_sub_get8 hget.
    have := @get_sub_get8 aa ws len2 a2 len i _.
    move: hget; rewrite /get_sub; case: andP => // -[/ZleP h1 /ZleP h2] [_].
    case: andP; rewrite !zify => h3; last by lia.
    move=> /(_ _ refl_equal) hr2 hr1; eexists => //; split; first by lia.
    by move=> k w; rewrite hr1 hr2; case: ifP => // ? /hu.
  Qed.

  Lemma uincl_set_sub {ws len1 len2 len} (a1 a1': array len1) (a2: array len2) aa i 
        (t1 t2:array (Z.to_pos (arr_size ws len))) :
    uincl a1 a2 -> uincl t1 t2 ->
    set_sub aa a1 i t1 = ok a1' ->
    exists2 a2', set_sub aa a2 i t2 = ok a2' & uincl a1' a2'.
  Proof.
    move=> [hlen1 hget1] [hlen2 hget2] hset.
    have := set_sub_get8 hset.
    have := @set_sub_get8 aa ws len2 a2 len i _.
    move: hset; rewrite /set_sub; case: andP => // -[/ZleP h1 /ZleP h2] [_].
    case: andP; rewrite !zify => h3; last by lia.
    move=> /(_ _ _ refl_equal) hr2 hr1; eexists => //; split; first by lia.
    by move=> k w; rewrite hr1 hr2; case: ifP => // [ ? /hget2| ? /hget1].
  Qed.

End WArray.

Hint Resolve WArray.uincl_refl : core.
