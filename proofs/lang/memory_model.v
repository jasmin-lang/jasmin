(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq div eqtype.
From mathcomp Require Import ssralg word_ssrZ.
Require Import strings word utils.
Import Utf8 ZArith Lia.
Import ssrring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

(* LittleEndian *)
Module LE.

  Definition encode sz (w: word sz) : seq u8 := split_vec U8 w.
  Definition decode sz (n: seq u8)  : word sz := make_vec sz n.

  Lemma size_encode sz (w: word sz) :
    size (encode w) = Z.to_nat (wsize_size sz).
  Proof.
    by rewrite /encode /split_vec size_map size_iota => {w}; case: sz.
  Qed.

  Lemma decodeK sz (w: word sz) :
    decode sz (encode w) = w.
  Proof. by rewrite /decode /encode make_vec_split_vec. Qed.

  Lemma decode_inj sz (bs bs': seq u8) :
    size bs = size bs' →
    size bs = Z.to_nat (wsize_size sz) →
    decode sz bs = decode sz bs' →
    bs = bs'.
  Proof.
    by move => eqsz hsz /make_vec_inj; apply.
  Qed.

  Definition wread8 ws (v:word ws) (k:Z) :=
    nth 0%R (encode v) (Z.to_nat k).

  Lemma encode8E (w: u8): encode w = [:: w].
  Proof.
    have {2}<-:= decodeK w.
    rewrite /encode /decode /make_vec /split_vec divnn modnn /= mul0n.
    by rewrite Z.lor_0_r /wrepr word.ureprK.
  Qed.

  Lemma encodeE s (w:word s) : encode w = [seq wread8 w k | k <- ziota 0 (wsize_size s)].
  Proof.
    symmetry; apply (eq_from_nth (x0 := 0%R)).
    + by rewrite size_map size_ziota size_encode.
    move=> i; rewrite size_map size_ziota => hi.
    by rewrite (nth_map 0%Z) ?size_ziota // nth_ziota // Z.add_0_l /wread8 Nat2Z.id.
  Qed.

  Lemma read0 ws x :
    wread8 (ws := ws) 0 x = 0%R.
  Proof.
    rewrite /LE.wread8 /LE.encode /split_vec.
    case: (Nat.le_gt_cases (ws %/ U8 + ws %% U8) (Z.to_nat x)) => h0.
    - rewrite nth_default; first done.
      rewrite size_map size_iota.
      by apply/leP.
    rewrite (nth_map O); first last.
    - rewrite size_iota.
      by apply/ltP.
    rewrite /word.subword -word.urepr_word word.urepr_lsr Z.shiftr_0_l.
    exact/eqP.
  Qed.

End LE.

Section POINTER.

Context (pointer: eqType).

Class pointer_op (pointer: eqType) : Type := PointerOp {

  add : pointer -> Z -> pointer;
  sub : pointer -> pointer -> Z;
  p_to_z : pointer -> Z; 

  add_sub : forall p k, add p (sub k p) = k;
  sub_add : forall p k, 0 <= k < wsize_size U256 -> sub (add p k) p = k; 
  add_0   : forall p, add p 0 = p;

}.

Context {Pointer: pointer_op pointer}.

Definition is_align (p:pointer) (sz:wsize) := 
  (p_to_z p mod wsize_size sz == 0)%Z.

Lemma is_align8 p : is_align p U8.
Proof. by rewrite /is_align Zmod_1_r. Qed.

Class coreMem (core_mem: Type) := CoreMem {
  get : core_mem -> pointer -> exec u8;
  set : core_mem -> pointer -> u8 -> exec core_mem;
  valid8 : core_mem -> pointer -> bool;
  setP : 
    forall m p w p' m',
      set m p w = ok m' ->
      get m' p' = if p == p' then ok w else get m p';
  valid8P : forall m p w, reflect (exists m', set m p w = ok m') (valid8 m p);
  get_valid8 : forall m p w, get m p = ok w -> valid8 m p; 
  valid8_set : forall m p w m' p', set m p w = ok m' -> valid8 m' p' = valid8 m p';
}.

End POINTER.

(* -------------------------------------------------------------------- *)

(** This type describes whether a memory access must check for alignment.
  With Unaligned, there are no particular constraints.
  With Aligned, the pointer must be a multiple of the size of the access. *)
Variant aligned := Unaligned | Aligned.

Scheme Equality for aligned.

Lemma aligned_eq_axiom : Equality.axiom aligned_beq.
Proof.
  exact: (eq_axiom_of_scheme internal_aligned_dec_bl internal_aligned_dec_lb).
Qed.

Definition aligned_eqMixin     := Equality.Mixin aligned_eq_axiom.
Canonical  aligned_eqType      := Eval hnf in EqType aligned aligned_eqMixin.

Definition aligned_le (x y: aligned) : bool :=
  (x == Unaligned) || (y == Aligned).

(* -------------------------------------------------------------------- *)
Module Export CoreMem.
Section CoreMem.

  Context {pointer: eqType} {Pointer: pointer_op pointer}.
  Context {core_mem: Type} {CM: coreMem pointer core_mem}.

  Definition is_aligned_if (al: aligned) (ptr: pointer) (sz: wsize) : bool :=
    if al is Aligned then is_align ptr sz else true.

  Lemma is_aligned_if_is_align al ptr sz :
    is_align ptr sz → is_aligned_if al ptr sz.
  Proof. by rewrite /is_aligned_if => ->; case: al. Qed.

  Lemma aligned_leP al al' p sz :
    aligned_le al al' →
    is_aligned_if al' p sz →
    is_aligned_if al p sz.
  Proof. by case: al => // /eqP ->. Qed.

  Definition read (m: core_mem) (al: aligned) (ptr: pointer) (sz: wsize) : exec (word sz) :=
    Let _ := assert (is_aligned_if al ptr sz) ErrAddrInvalid in
    Let l := mapM (fun k => get m (add ptr k)) (ziota 0 (wsize_size sz)) in
    ok (LE.decode sz l).

  Definition write (m:core_mem) (al: aligned) (ptr:pointer) (sz:wsize) (w: word sz) : exec core_mem :=
    Let _ := assert (is_aligned_if al ptr sz) ErrAddrInvalid in
    foldM (fun k m => set m (add ptr k) (LE.wread8 w k)) m (ziota 0 (wsize_size sz)).

  Definition validw (m:core_mem) (al: aligned) (ptr:pointer) (sz:wsize) :=
    is_aligned_if al ptr sz && all (fun k => valid8 m (add ptr k)) (ziota 0 (wsize_size sz)).

  Lemma valid8_validw m al p : valid8 m p = validw m al p U8.
  Proof. by rewrite /validw is_aligned_if_is_align ?is_align8 // /= add_0 andbT. Qed.

  Lemma validwP m al p ws :
    reflect (is_aligned_if al p ws ∧ ∀ k, 0 <= k < wsize_size ws -> validw m al (add p k) U8) (validw m al p ws).
  Proof.
    apply (iffP andP).
    + by move=> [? /allP h]; split => // k hk; rewrite -valid8_validw; apply h; rewrite in_ziota !zify.
    by move=> [? h]; split => //;apply/allP => k; rewrite in_ziota !zify (valid8_validw _ al); apply h.
  Qed.

  Lemma validw8_alignment al' m al p :
    validw m al p U8 = validw m al' p U8.
  Proof. by rewrite /validw !is_aligned_if_is_align // is_align8. Qed.

  Lemma read8_alignment al' m al p :
    read m al p U8 = read m al' p U8.
  Proof. by rewrite /read !is_aligned_if_is_align // is_align8. Qed.

  Lemma get_read8 m al p: get m p = read m al p U8.
  Proof.
    rewrite /read is_aligned_if_is_align /= ?is_align8 // /= add_0.
    by case: get => //= w; rewrite -LE.encode8E LE.decodeK.
  Qed.

  Lemma set_write8 m al p w: set m p w = write m al p w.
  Proof.
    rewrite /write is_aligned_if_is_align /= ?is_align8 // /= add_0.
    have := LE.encode8E w; rewrite LE.encodeE /= => -[->].
    by case: set.
  Qed.

  Lemma readE m al p sz :
    read m al p sz =
      Let _ := assert (is_aligned_if al p sz) ErrAddrInvalid in
      Let l := mapM (fun k => read m al (add p k) U8) (ziota 0 (wsize_size sz)) in
      ok (LE.decode sz l).
  Proof.
    by rewrite {1}/read !ziotaE; case: is_aligned_if => //=; f_equal; apply eq_mapM => k _; apply get_read8.
  Qed.

  Lemma write_valid8_eq m m' al p s (v :word s) :
    write m al p v = ok m' ->
    forall p',
    valid8 m' p' = valid8 m p'.
  Proof.
    rewrite /write; t_xrbindP => ? hfold p'; move: m hfold.
    apply ziota_ind => /= [ m [->]//| i l _ hrec m]; t_xrbindP => ? h /hrec ->.
    by apply (valid8_set _ h).
  Qed.

  Lemma write_validw_eq m m' al p s (v :word s) :
    write m al p v = ok m' ->
    forall al' p' s',
    validw m' al' p' s' = validw m al' p' s'.
  Proof.
    by move=> hw al' p' s'; rewrite /validw; f_equal; apply all_ziota => ? _; apply (write_valid8_eq hw).
  Qed.

  Lemma write_read8 m m' al p ws (v: word ws) :
    write m al p v = ok m' ->
    forall al' k, read m' al' k U8 =
      let i := sub k p in
       if (0 <=? i) && (i <? wsize_size ws) then ok (LE.wread8 v i)
       else read m al' k U8.
  Proof.
    rewrite /write; t_xrbindP => _ h al' k; move: h.
    rewrite -(@in_ziota 0 (wsize_size ws)).
    move: m; apply ziota_ind => /=; first by move=> ? [<-].
    move=> i l hi hrec m; t_xrbindP => mi hset /hrec ->.
    rewrite in_cons -!get_read8 (setP _ hset) orbC.
    case: ifP => //= _.
    case: eqP => [<- | hne].
    + rewrite sub_add ?eq_refl //.
      have : wsize_size ws <= wsize_size U256 by case: (ws).
      lia.
    by case: eqP => // heq; case: hne; rewrite -heq add_sub.
  Qed.

  Lemma eq_read m1 m2 al p ws :
    (forall al' i, 0 <= i < wsize_size ws -> read m1 al' (add p i) U8 = read m2 al' (add p i) U8) ->
    read m1 al p ws = read m2 al p ws.
  Proof.
    Opaque Z.to_nat.
    move=> h8; rewrite !readE ziotaE; case: is_aligned_if => //=; f_equal.
    apply eq_mapM => k /mapP[] n; rewrite mem_iota add0n => /andP[] /leP ? /ltP ? ?; subst.
    apply: h8.
    Lia.lia.
  Qed.

  Lemma writeV s (v:word s) m al p:
    reflect (exists m', write m al p v = ok m') (validw m al p s).
  Proof.
    rewrite /write /validw; case: is_aligned_if => //; last by constructor => -[].
    rewrite ziotaE /=.
    elim: iota m => /=; first by move=> ?; constructor; eauto.
    move=> k l hrec m.
    apply (iffP andP).
    + move=> [] /valid8P -/(_ (LE.wread8 v (Z.of_nat k))) [m'] hset hall.
      by rewrite hset;apply/hrec; apply: sub_all hall => i; rewrite (valid8_set _ hset).
    move=> [m'];t_xrbindP => m'' hset hf; split.
    + by apply/valid8P; eexists; eauto.
    apply/sub_all; last by apply/hrec; eexists; eauto.
    by move=> i;rewrite (valid8_set _ hset). 
  Qed.

  Lemma readV m al ptr sz w :
    read m al ptr sz = ok w ->
    validw m al ptr sz.
  Proof.
    move=> h; apply /validwP; move: h; rewrite /read; t_xrbindP => -> l h _; split => //.
    move=> k hk; have {hk}: k \in ziota 0 (wsize_size sz).
    + by rewrite in_ziota !zify.
    rewrite -valid8_validw.
    move: l h;apply ziota_ind => //= i li hi hr ?.
    t_xrbindP => wi hwi; have ?:= get_valid8 hwi.
    by move=> l /hr{hr}hr _; rewrite inE => /orP [/eqP ->| /hr].
  Qed.

  Lemma read8_read m al p s v:
    (forall al' i, 0 <= i < wsize_size s -> read m al' (add p i) U8 = ok (LE.wread8 v i)) ->
    read m al p s = if is_aligned_if al p s then ok v else Error ErrAddrInvalid.
  Proof.
    rewrite readE => h8; case: is_aligned_if => //.
    have -> : mapM (λ k, read m al (add p k) U8) (ziota 0 (wsize_size s)) =
                   ok (map (λ k, LE.wread8 v k) (ziota 0 (wsize_size s))).
    + by apply ziota_ind => //= k l hk ->; rewrite h8.
    by rewrite -{2}(LE.decodeK v) LE.encodeE ziotaE.
  Qed.

  Lemma read_read8 m al p s v:
    read m al p s = ok v ->
    is_aligned_if al p s /\ (forall i, 0 <= i < wsize_size s -> read m al (add p i) U8 = ok (LE.wread8 v i)).
  Proof.
    rewrite readE; t_xrbindP => ha l hl.
    rewrite -{1}(LE.decodeK v) => /LE.decode_inj.
    rewrite -(size_mapM hl) size_ziota LE.size_encode => /(_ refl_equal refl_equal) ?; subst l.
    rewrite LE.encodeE in hl.
    split => // i hi.
    have : i \in ziota 0 (wsize_size s) by rewrite in_ziota !zify.
    move: hl; apply ziota_ind => //= k l hk hrec.
    t_xrbindP => w hw ws hws ??; subst w ws.
    by rewrite inE => /orP [/eqP -> | /(hrec hws)].
  Qed.

  Lemma writeP_eq m m' al p s (v :word s):
    write m al p v = ok m' ->
    read m' al p s = ok v.
  Proof.
    move=> hw. 
    rewrite (read8_read (m:=m') al (v:= v) (p:=p)).
    + by have /validwP [->] : validw m al p s by apply /writeV; eexists; eauto.
    move=> al' k hk.
    rewrite (write_read8 hw) sub_add /=.
    + by case: andP => //; rewrite !zify; lia.
    have : wsize_size s <= wsize_size U256 by case: (s).
    lia.
  Qed.

  Lemma aligned_le_read m p sz v al al' :
    aligned_le al al' →
    read m al' p sz = ok v →
    read m al p sz = ok v.
  Proof. by rewrite /read; t_xrbindP => h /(aligned_leP h) -> ? -> /= ->. Qed.

  Lemma aligned_le_write al al' m p sz (w: word sz) m' :
    aligned_le al al' →
    write m al' p w = ok m' →
    write m al p w = ok m'.
  Proof. by rewrite /write; t_xrbindP => /aligned_leP h /h -> ->. Qed.

  Definition disjoint_range p s p' s' :=
    forall i i', 0 <= i < wsize_size s -> 0 <= i' < wsize_size s' ->
       add p i <> add p' i'.

  Lemma disjoint_range_U8 p sz p' :
    (∀ i, 0 <= i < wsize_size sz → p' ≠ add p i) →
    disjoint_range p sz p' U8.
  Proof.
    move => h i i' i_range.
    change (wsize_size U8) with 1%Z => i'_range.
    have -> : i' = 0 by Lia.lia.
    rewrite {i' i'_range} add_0 => ?.
    exact: (h _ i_range).
  Qed.

  Lemma writeP_neq m m' al p s (v :word s) al' p' s':
    write m al p v = ok m' ->
    disjoint_range p s p' s' ->
    read m' al' p' s' = read m al' p' s'.
  Proof.
    move=> hw hd; apply eq_read => a k hk.
    rewrite (write_read8 hw) /=.
    case: andP => //; rewrite !zify => hin.
    elim: (hd (sub (add p' k) p) k) => //; by rewrite add_sub.
  Qed.

  Lemma disjoint_range_valid_not_valid_U8 m al1 p1 ws1 p2 :
    validw m al1 p1 ws1 ->
    ~ validw m Aligned p2 U8 ->
    disjoint_range p1 ws1 p2 U8.
  Proof.
    move=> /validwP [hal1 hval1] hnval.
    red; rewrite wsize8 => i i' i_range ?.
    have ? : i' = 0 by Lia.lia.
    subst; rewrite add_0.
    move => ?; subst; apply: hnval; apply/validwP; split.
    + by apply is_align8.
    move=> k; rewrite wsize8 => hk; have ->: k = 0%Z by Lia.lia.
    rewrite add_0 (validw8_alignment al1).
    exact: hval1.
  Qed.

  Lemma read_write_any_mem m1 m1' ar aw pr pw szw (vw:word szw) m2 m2':
    read m1 ar pr U8 = read m1' ar pr U8 ->
    write m1 aw pw vw = ok m2 ->
    write m1' aw pw vw = ok m2' ->
    read m2 ar pr U8 = read m2' ar pr U8.
  Proof.
    move=> hr hw hw'.
    by rewrite (write_read8 hw) (write_read8 hw') /=; case: andP.
 Qed.

 Definition disjoint_zrange_ovf p s p' s' : Prop :=
   ∀ i i' : Z, 0 <= i < s → 0 <= i' < s' → add p i ≠ add p' i'.

End CoreMem.
End CoreMem.

(* ** Memory
 * -------------------------------------------------------------------- *)

Section WITH_POINTER_DATA.
Context {pd: PointerData}.

Definition no_overflow (p: pointer) (sz: Z) : bool :=
  (wunsigned p + sz <=? wbase Uptr)%Z.

Definition disjoint_zrange (p: pointer) (s: Z) (p': pointer) (s': Z) :=
  [/\ no_overflow p s,
      no_overflow p' s' &
      wunsigned p + s <= wunsigned p' \/
        wunsigned p' + s' <= wunsigned p]%Z.

Definition disjoint_range p s p' s' :=
  disjoint_zrange p (wsize_size s) p' (wsize_size s').

Definition zbetween (pstk : pointer) (sz : Z) (p : pointer) (sz' : Z) : bool :=
  ((wunsigned pstk <=? wunsigned p) && (wunsigned p + sz' <=? wunsigned pstk + sz))%Z.

Definition between (pstk : pointer)  (sz : Z) (p : pointer) (s : wsize) : bool :=
  zbetween pstk sz p (wsize_size s).

Lemma no_overflow_incl p1 sz1 p2 sz2 :
  zbetween p1 sz1 p2 sz2 ->
  no_overflow p1 sz1 ->
  no_overflow p2 sz2.
Proof. by rewrite /zbetween /no_overflow !zify; lia. Qed.

Lemma zbetween_refl p sz : zbetween p sz p sz.
Proof. by rewrite /zbetween !zify; lia. Qed.

Lemma zbetween_trans p1 sz1 p2 sz2 p3 sz3 :
  zbetween p1 sz1 p2 sz2 ->
  zbetween p2 sz2 p3 sz3 ->
  zbetween p1 sz1 p3 sz3.
Proof.
  rewrite /between => /andP [] /ZleP a /ZleP b /andP [] /ZleP c /ZleP d.
  apply/andP; split; apply/ZleP; lia.
Qed.

Lemma zbetween_le p sz1 sz2 :
  sz2 <= sz1 ->
  zbetween p sz1 p sz2.
Proof. by rewrite /zbetween !zify; lia. Qed.

Lemma between_byte pstk sz b i sz' :
  no_overflow b sz' →
  zbetween pstk sz b sz' →
  0 <= i ∧ i < sz' →
  between pstk sz (b + wrepr Uptr i) U8.
Proof.
  rewrite /zbetween !zify; change (wsize_size U8) with 1 => novf [] lo hi i_range.
  rewrite wunsigned_add; first lia.
  move: (wunsigned_range b); lia.
Qed.

Lemma not_zbetween_neg p1 p2 sz1 sz2 :
  (sz1 <= 0)%Z ->
  (0 < sz2)%Z ->
  ~~ zbetween p1 sz1 p2 sz2.
Proof. by move=> ??; apply /idP; rewrite /zbetween !zify; lia. Qed.

Lemma zbetween_not_disjoint_zrange p1 s1 p2 s2 :
  zbetween p1 s1 p2 s2 ->
  0 < s2 ->
  ~ disjoint_zrange p1 s1 p2 s2.
Proof. by rewrite /zbetween !zify => hb hlt [_ _ ?]; lia. Qed.

Lemma not_between_U8_disjoint_zrange p1 sz1 p2 :
  no_overflow p1 sz1 ->
  ~ between p1 sz1 p2 U8 ->
  disjoint_zrange p1 sz1 p2 (wsize_size U8).
Proof.
  move=> hnover.
  rewrite /between /zbetween wsize8 !zify => hnb.
  split=> //; last by lia.
  rewrite /no_overflow zify.
  have := wunsigned_range p2.
  by lia.
Qed.

Lemma disjoint_zrange_sym p1 sz1 p2 sz2 :
  disjoint_zrange p1 sz1 p2 sz2 ->
  disjoint_zrange p2 sz2 p1 sz1.
Proof.
  rewrite /disjoint_zrange; move=> [*]; split=> //; lia.
Qed.

Lemma disjoint_zrange_incl p1 s1 p2 s2 p1' s1' p2' s2' :
  zbetween p1 s1 p1' s1' ->
  zbetween p2 s2 p2' s2' ->
  disjoint_zrange p1 s1 p2 s2 ->
  disjoint_zrange p1' s1' p2' s2'.
Proof.
  rewrite /zbetween /disjoint_zrange /no_overflow !zify.
  by move=> ?? [/ZleP ? /ZleP ? ?]; split; rewrite ?zify; lia.
Qed.

Lemma disjoint_zrange_incl_l p1 s1 p2 s2 p1' s1' :
  zbetween p1 s1 p1' s1' ->
  disjoint_zrange p1 s1 p2 s2 ->
  disjoint_zrange p1' s1' p2 s2.
Proof. by move=> ?; apply disjoint_zrange_incl=> //; apply zbetween_refl. Qed.

Lemma disjoint_zrange_incl_r p1 s1 p2 s2 p2' s2' :
  zbetween p2 s2 p2' s2' ->
  disjoint_zrange p1 s1 p2 s2 ->
  disjoint_zrange p1 s1 p2' s2'.
Proof. by move=> ?; apply disjoint_zrange_incl=> //; apply zbetween_refl. Qed.

Lemma disjoint_zrange_byte p1 sz1 p2 sz2 i :
  disjoint_zrange p1 sz1 p2 sz2 ->
  0 <= i /\ i < sz2 ->
  disjoint_zrange p1 sz1 (p2 + wrepr _ i) (wsize_size U8).
Proof.
  move=> hd hrange.
  case: (hd) => _ hover _.
  apply: disjoint_zrange_incl_r hd.
  apply: (between_byte hover) => //.
  by apply zbetween_refl.
Qed.

Lemma disjoint_zrange_add p sz p' sz1 sz2 :
  0 < sz ->
  0 <= sz1 ->
  0 < sz2 ->
  no_overflow p' (sz1 + sz2) ->
  disjoint_zrange p sz p' sz1 ->
  disjoint_zrange p sz (p' + wrepr _ sz1) sz2 ->
  disjoint_zrange p sz p' (sz1 + sz2).
Proof.
  move=> hsz hsz1 hsz2 hover' [hover _ hdisj] [_ _ hdisj'].
  split=> //.
  move: hdisj'; rewrite wunsigned_add; first by lia.
  by move: hover'; rewrite /no_overflow zify; have := wunsigned_range p'; lia.
Qed.

Lemma disjoint_zrange_U8 p sz p' sz' :
  0 < sz ->
  0 < sz' ->
  no_overflow p' sz' ->
  (forall k, 0 <= k /\ k < sz' -> disjoint_zrange p sz (p' + wrepr _ k) (wsize_size U8)) ->
  disjoint_zrange p sz p' sz'.
Proof.
  move=> hsz /dup[] /Z.lt_le_incl.
  move: sz'; apply: natlike_ind; first by lia.
  move=> sz' hsz' ih _ hover hdisj.
  have /Z_le_lt_eq_dec [?|?] := hsz'.
  + apply disjoint_zrange_add => //; last by apply hdisj; lia.
    apply ih => //.
    + by move: hover; rewrite /no_overflow !zify; lia.
    by move=> k hk; apply hdisj; lia.
  subst sz'.
  rewrite -(GRing.addr0 p') -wrepr0.
  by apply hdisj; lia.
Qed.

Definition pointer_range (lo hi: pointer) : pred pointer :=
  λ p, (wunsigned lo <=? wunsigned p) && (wunsigned p <? wunsigned hi).

Lemma pointer_rangeP lo hi pr :
  reflect (wunsigned lo <= wunsigned pr < wunsigned hi) (pointer_range lo hi pr).
Proof. by apply: (iffP idP); rewrite /pointer_range !zify. Qed.

Lemma pointer_range_incl_l lo lo' hi pr :
  (wunsigned lo' <= wunsigned lo)%Z ->
  pointer_range lo hi pr ->
  pointer_range lo' hi pr.
Proof. by rewrite /pointer_range !zify; lia. Qed.

Lemma pointer_range_incl_r lo hi hi' pr :
  (wunsigned hi <= wunsigned hi')%Z ->
  pointer_range lo hi pr ->
  pointer_range lo hi' pr.
Proof. by rewrite /pointer_range !zify; lia. Qed.

Lemma pointer_range_between lo hi pr :
  pointer_range lo hi pr = between lo (wunsigned hi - wunsigned lo) pr U8.
Proof.
  rewrite /pointer_range /between /zbetween wsize8.
  by apply /idP/idP; rewrite !zify; lia.
Qed.

(* -------------------------------------------------- *)
(** Pointer arithmetic *)

#[ global ]
Instance Pointer : pointer_op pointer.
Proof.
refine
  {| add p k   := (p + wrepr Uptr k)%R
   ; sub p1 p2 := wunsigned (p1 - p2)%R
   ; p_to_z p  := wunsigned p
  |}.
- abstract (move=> p k; rewrite wrepr_unsigned; ssring).
- abstract (move=> p k => hk;
  rewrite -{2}(@wunsigned_repr_small Uptr k);
    [ f_equal; ssring
    | have := wsize_size_wbase U256;
      have := wbase_m (wsize_le_U8 (@Uptr pd));
      Lia.lia ]).
- abstract (move => p; rewrite wrepr0; ssring).
Defined.

Lemma addE p k : add p k = (p + wrepr Uptr k)%R.
Proof. by []. Qed.

Lemma subE p1 p2 : sub p1 p2 = wunsigned (p1 - p2).
Proof. by []. Qed.

Lemma addC p i j : add (add p i) j = add p (i + j).
Proof. rewrite /= wrepr_add; ssring. Qed.

Lemma p_to_zE p : p_to_z p = wunsigned p.
Proof. done. Qed.

Global Opaque Pointer.

Lemma disjoint_zrange_alt a m b n :
  disjoint_zrange a m b n →
  disjoint_zrange_ovf a m b n.
Proof.
  case => /ZleP ha /ZleP hb D i j hi hj.
  rewrite !addE => K.
  suff : wunsigned a + i = wunsigned b + j by Lia.lia.
  have a_range := wunsigned_range a.
  have b_range := wunsigned_range b.
  do 2 rewrite <-wunsigned_add by Lia.lia.
  by rewrite K.
Qed.

Lemma zbetween_disjoint_zrange_ovf a b p m n s :
  zbetween a n b m → disjoint_zrange_ovf p s a n → disjoint_zrange_ovf p s b m.
Proof.
  rewrite /zbetween /disjoint_zrange_ovf !zify => - [] hlo hhi D i i' hi hi' K.
  set ofs := wunsigned b - wunsigned a.
  have hofs : 0 <= ofs + i' < n by Lia.lia.
  apply: (D _ _ hi hofs).
  rewrite K /ofs !addE wrepr_add wrepr_sub !wrepr_unsigned GRing.addrA.
  f_equal.
  by rewrite GRing.addrC GRing.subrK.
Qed.

Lemma disjoint_range_alt p1 ws1 p2 ws2 :
  disjoint_range p1 ws1 p2 ws2 ->
  CoreMem.disjoint_range p1 ws1 p2 ws2.
Proof.
  case; rewrite /no_overflow !zify => hover1 hover2 hdisj i1 i2 hi1 hi2.
  rewrite !addE => /(f_equal wunsigned).
  have h1 := wunsigned_range p1.
  have h2 := wunsigned_range p2.
  by rewrite !wunsigned_add; lia.
Qed.

Lemma is_align_modE ptr sz : (wunsigned ptr mod wsize_size sz == 0)%Z = is_align ptr sz.
Proof. by rewrite /is_align p_to_zE (rwP eqP). Qed.

Lemma is_align_mod ptr sz : reflect (wunsigned ptr mod wsize_size sz = 0)%Z (is_align ptr sz).
Proof. rewrite -is_align_modE; apply eqP. Qed.

Lemma is_align_addE (ptr1:pointer) sz :
  is_align ptr1 sz ->
  forall ptr2, is_align (ptr1 + ptr2)%R sz = is_align ptr2 sz.
Proof.
  have hn := wsize_size_pos sz.
  move => /is_align_mod h ptr2; rewrite -!is_align_modE.
  by rewrite /wunsigned mathcomp.word.word.addwE -/(wbase Uptr) mod_wbase_wsize_size -Zplus_mod_idemp_l h.
Qed.

Lemma is_align_add (ptr1 ptr2:pointer) sz : 
  is_align ptr1 sz -> is_align ptr2 sz -> is_align (ptr1 + ptr2)%R sz.
Proof. by move=> /is_align_addE ->. Qed.

Lemma is_align_m sz sz' (ptr: pointer) :
  (sz' ≤ sz)%CMP →
  is_align ptr sz →
  is_align ptr sz'.
Proof.
  have wsnz s : wsize_size s ≠ 0.
  - by have := wsize_size_pos s.
  move => /wsize_size_le le /eqP /Z.mod_divide - /(_ (wsnz _)) /(Z.divide_trans _ _ _ le) {le} le.
  by apply/eqP/Z.mod_divide.
Qed.

Lemma is_align_mul sz j : is_align (wrepr Uptr (wsize_size sz * j)) sz.
Proof.
  have hn := wsize_size_pos sz.
  have hnz : wsize_size sz ≠ 0%Z by lia.
  by rewrite /is_align p_to_zE wunsigned_repr mod_wbase_wsize_size Z.mul_comm Z_mod_mult.
Qed.

Lemma is_align_no_overflow ptr sz :
  is_align ptr sz → no_overflow ptr (wsize_size sz).
Proof.
  rewrite /no_overflow /is_align p_to_zE => /eqP ha; apply/ZleP.
  have hn := wsize_size_pos sz.
  have hnz : wsize_size sz ≠ 0%Z by lia.
  move: (wunsigned ptr) (wunsigned_range ptr) ha => {ptr} ptr.
  have [a ->] := wsize_size_div_wbase sz Uptr.
  move: (wsize_size sz) hn hnz => n hn hnz hr /Zmod_divides [] // q ?; subst ptr.
  cut (q + 1 <= a)%Z; nia.
Qed.

Notation do_align := align_word (only parsing).

Lemma do_align_is_align sz p : is_align (do_align sz p) sz.
Proof. apply align_word_aligned. Qed.

Lemma is_align_array ptr sz j : 
  is_align ptr sz → is_align (wrepr _ (wsize_size sz * j) + ptr)%R sz.
Proof. by move=> hptr; apply is_align_add => //; apply is_align_mul. Qed.

(** Rounds the given size to the next larger-or-equal multiple of [ws] *)
Definition round_ws (ws:wsize) (sz: Z) : Z :=
  (let d := wsize_size ws in
   let: (q, r) := Z.div_eucl sz d in
   if r == 0 then sz else (q + 1) * d)%Z.

Lemma round_ws_aligned ws sz :
  (round_ws ws sz) mod wsize_size ws == 0.
Proof.
  have ws_pos : wsize_size ws ≠ 0 by case: ws.
  apply/eqP; rewrite Z.mod_divide // /round_ws.
  elim_div => z z' /(_ ws_pos) [] ->{sz} D.
  case: eqP => ?.
  - exists z; lia.
  exists (z + 1); lia.
Qed.

Lemma round_ws_range ws sz :
  sz <= round_ws ws sz < sz + wsize_size ws.
Proof.
  have ws_pos := wsize_size_pos ws.
  rewrite /round_ws; elim_div => ? ? [] // -> []; last by lia.
  case: eqP; lia.
Qed.

Lemma round_wsE ws sz : round_ws ws sz =
  if (sz mod wsize_size ws == 0)%Z then sz else sz + wsize_size ws - sz mod wsize_size ws.
Proof.
  have ws_pos: wsize_size ws ≠ 0 by case: ws.
  rewrite /round_ws.
  elim_div => ? ? /(_ ws_pos) [] ->{sz} D.
  case: eqP => ? //.
  by lia.
Qed.

Class memory (mem: Type) (CM: coreMem pointer mem) : Type :=
  Memory {
      stack_root : mem -> pointer
    ; stack_limit : mem -> pointer
    ; frames : mem -> seq pointer
    ; alloc_stack : mem -> wsize -> Z -> Z -> Z -> exec mem (* alignement, size, extra initial size, extra-size *)
    ; free_stack : mem -> mem
    ; init : seq (pointer * Z) → pointer → exec mem

    ; stack_region_is_free : ∀ (m: mem) (p: pointer), wunsigned (stack_limit m) <= wunsigned p < wunsigned (head (stack_root m) (frames m)) → ~~ validw m Aligned p U8
    ; top_stack_below_root: ∀ (m: mem), wunsigned (head (stack_root m) (frames m)) <= wunsigned (stack_root m)
    }.

#[ global ] Arguments Memory {mem CM} _ _ _ _ _ _ _.
#[ global ] Arguments top_stack_below_root {mem CM} _.

Definition top_stack {mem: Type} {CM: coreMem pointer mem} {M: memory CM} (m: mem) : pointer :=
  head (stack_root m) (frames m).

Section SPEC.
  Context mem (CM: coreMem pointer mem) (M: memory CM)
    (m: mem) (ws:wsize) (sz: Z) (ioff:Z) (sz': Z) (m': mem) .
  Let pstk := top_stack m'.

  Definition top_stack_after_alloc (top: pointer) (ws: wsize) (sz: Z) : pointer :=
    do_align ws (top + wrepr Uptr (- sz)).

  Record alloc_stack_spec : Prop := mkASS {
    ass_read_old8 : forall p, validw m Aligned p U8 -> read m Aligned p U8 = read m' Aligned p U8;
    ass_read_new  : forall p, ~validw m Aligned p U8 -> validw m' Aligned p U8 -> read m' Aligned p U8 = Error ErrAddrInvalid;
    ass_valid     : forall p, validw m' Aligned p U8 = validw m Aligned p U8 || between (pstk + wrepr _ ioff) (sz - ioff) p U8;
    ass_align_stk : is_align pstk ws;
    ass_above_limit: wunsigned (stack_limit m) <= wunsigned pstk ∧ wunsigned pstk +  sz + Z.max 0 sz' <= wunsigned (top_stack m);
    ass_ioff      : 0 <= ioff <= sz;
    ass_fresh     : forall al p s, validw m al p s ->
                        (wunsigned p + wsize_size s <= wunsigned pstk \/
                         wunsigned pstk + sz <= wunsigned p)%Z;
    ass_root      : stack_root m' = stack_root m;
    ass_limit     : stack_limit m' = stack_limit m;
    ass_frames    : frames m' = top_stack_after_alloc (top_stack m) ws (sz + sz') :: frames m;
  }.

  Record stack_stable : Prop := mkSS {
    ss_root: stack_root m = stack_root m';
    ss_limit: stack_limit m = stack_limit m';
    ss_frames: frames m = frames m';
  }.

  Record free_stack_spec : Prop := mkFSS {
    fss_read_old8 : forall p, validw m' Aligned p U8 -> read m Aligned p U8 = read m' Aligned p U8;
    fss_valid    : ∀ p, validw m' Aligned p U8 = validw m Aligned p U8 && ~~ pointer_range (top_stack m) (top_stack m') p;
    fss_root : stack_root m' = stack_root m;
    fss_limit : stack_limit m' = stack_limit m;
    fss_frames : frames m' = behead (frames m);
   }.

  Lemma ass_align (ass:alloc_stack_spec) ofs s :
    (s <= ws)%CMP ->
    is_align (pstk + wrepr _ ofs)%R s = is_align (wrepr _ ofs) s.
  Proof.
    by move=> hs; apply/is_align_addE;apply: is_align_m (ass_align_stk ass).
  Qed.

  Lemma ass_add_ioff (ass: alloc_stack_spec) :
    wunsigned (pstk + wrepr _ ioff) = wunsigned pstk + ioff.
  Proof.
    have ? := ass_above_limit ass; have ? := ass_ioff ass.
    rewrite wunsigned_add //.
    assert (h := wunsigned_range (top_stack m)).  assert (h' := wunsigned_range pstk).
    lia.
  Qed.

  Lemma ass_read_old (ass:alloc_stack_spec) al p s : validw m al p s -> read m al p s = read m' al p s.
  Proof.
    move /validwP => [] ha hv; apply eq_read => al' k hk.
    rewrite 2!(read8_alignment Aligned).
    apply: (ass_read_old8 ass).
    rewrite (validw8_alignment al).
    exact: hv.
  Qed.

  Lemma fss_read_old (fss:free_stack_spec) al p s :
    validw m' al p s -> read m al p s = read m' al p s.
  Proof.
    move /validwP => [] ha hv; apply eq_read => al' k hk.
    rewrite 2!(read8_alignment Aligned).
    apply: (fss_read_old8 fss).
    rewrite (validw8_alignment al).
    exact: hv.
  Qed.

  (* ass_fresh using pointer_range *)
  Lemma ass_fresh_alt (ass:alloc_stack_spec) p :
    validw m Aligned p U8 ->
    ~ pointer_range pstk (top_stack m) p.
  Proof.
    move=> hvalid.
    rewrite /pointer_range !zify => hpointer.
    have habove := ass.(ass_above_limit).
    move: hvalid; apply /negP.
    apply stack_region_is_free.
    by rewrite -/(top_stack _); lia.
  Qed.

  (* TODO: we could also prove [no_overflow pstk (sz + Z.max 0 sz')] *)
  Lemma ass_no_overflow (ass:alloc_stack_spec) :
    no_overflow pstk sz.
  Proof.
    rewrite /no_overflow zify.
    assert (hover := wunsigned_range (top_stack m)).
    have := ass.(ass_above_limit).
    by lia.
  Qed.

  (* ass_fresh using disjoint_zrange *)
  Lemma ass_fresh_disjoint_zrange (ass:alloc_stack_spec) p s :
    validw m Aligned p s ->
    disjoint_zrange p (wsize_size s) pstk sz.
  Proof.
    move=> /dup[] /ass.(ass_fresh) hfresh hvalid.
    split=> //.
    + apply is_align_no_overflow.
      by move: hvalid => /validwP [? _].
    by apply (ass_no_overflow ass).
  Qed.

  (* part of ass_above_limit using disjoint_zrange *)
  (* the new frame is disjoint from the rest of the stack *)
  Lemma ass_above_limit_disjoint_zrange (ass:alloc_stack_spec) :
    disjoint_zrange
      pstk (sz + Z.max 0 sz')
      (top_stack m) (wunsigned (stack_root m) - wunsigned (top_stack m)).
  Proof.
    split.
    - rewrite /no_overflow zify.
      have := ass.(ass_above_limit).
      have := [elaborate wunsigned_range (top_stack m)].
      by lia.
    - rewrite /no_overflow zify.
      have := [elaborate wunsigned_range (stack_root m)].
      by lia.
    by left; have := ass.(ass_above_limit); lia.
  Qed.

End SPEC.

#[ global ] Arguments alloc_stack_spec {_ _ _} _ _ _ _ _.
#[ global ] Arguments stack_stable {_ _ _} _ _.
#[ global ] Arguments free_stack_spec {_ _ _} _ _.

Lemma top_stack_after_aligned_alloc p ws sz :
  is_align p ws ->
  top_stack_after_alloc p ws sz = (p + wrepr Uptr (- round_ws ws sz))%R.
Proof.
  rewrite /is_align p_to_zE => /eqP hal.
  rewrite round_wsE.
  rewrite /top_stack_after_alloc.
  apply wunsigned_inj.
  rewrite align_wordE.
  rewrite !wrepr_opp.

  have h: (wunsigned (p - wrepr Uptr sz) mod wsize_size ws = - (sz mod wsize_size ws) mod wsize_size ws)%Z.
  + by rewrite wunsigned_sub_mod Zminus_mod hal Z.sub_0_l wunsigned_repr mod_wbase_wsize_size.

  case: eqP => hsz.
  + by rewrite h Z.mod_opp_l_z // ?Zmod_mod // Z.sub_0_r.
  rewrite Z.mod_opp_l_nz // Zmod_mod // in h.
  rewrite -Z.add_sub_assoc -h.
  rewrite wrepr_add -{1}[p in RHS](GRing.subrK (wrepr Uptr sz)) GRing.addrKA.
  rewrite [RHS]wunsigned_sub //.
  have [hle hlt] := wunsigned_range (p - wrepr Uptr sz).
  have := Z.mod_le _ _ hle (wsize_size_pos ws).
  have := Z_mod_lt (wunsigned (p - wrepr Uptr sz)) (wsize_size ws) ltac:(done).
  by lia.
Qed.

Lemma top_stack_after_alloc_bounded p ws sz :
  0 <= sz ∧ sz <= wunsigned p ->
  wunsigned p - wunsigned (top_stack_after_alloc p ws sz) <= sz + wsize_size ws - 1.
Proof.
  move=> hsz.
  rewrite /top_stack_after_alloc.
  have := align_word_range ws (p + wrepr _ (- sz)).
  rewrite wunsigned_add; first by lia.
  by have := wunsigned_range p; lia.
Qed.

End WITH_POINTER_DATA.

Module Type MemoryT.

Parameter mem : PointerData -> Type.
#[ global ] Arguments mem {_}.

Section WITH_POINTER_DATA.
Context {pd: PointerData}.

#[ global ] Declare Instance CM : coreMem pointer mem.
#[ global ] Declare Instance M : memory CM.

(*Parameter readV : forall m p s v,
  read m p s = ok v -> validw m p s. *)

(* -------------------------------------------------------------------- *)
Parameter alloc_stackP : forall m m' ws sz ioff sz',
  alloc_stack m ws sz ioff sz' = ok m' -> alloc_stack_spec m ws sz ioff sz' m'.

Parameter alloc_stack_complete : forall m ws sz ioff sz',
  let: old_size := wunsigned (stack_root m) - wunsigned (top_stack m) in
  let: max_size := wunsigned (stack_root m) - wunsigned (stack_limit m) in
  let: available := max_size - old_size in
  [&& 0 <=? ioff, ioff <=? sz, 0 <=? sz' &
  if is_align (top_stack m) ws
  then round_ws ws (sz + sz') <=? available (* tight bound *)
  else sz + sz' + wsize_size ws - 1 <=? available (* loose bound, exact behavior is under-specified *)
  ] →
  ∃ m', alloc_stack m ws sz ioff sz' = ok m'.

Parameter write_mem_stable : forall m m' al p s (v:word s),
  write m al p v = ok m' -> stack_stable m m'.

Parameter free_stackP : forall m,
  free_stack_spec m (free_stack m).

End WITH_POINTER_DATA.
End MemoryT.
