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

(* ** Imports and settings *)

From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import strings word utils.
Import Utf8 ZArith.

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
    nth (wrepr U8 0) (encode v) (Z.to_nat k).

  Lemma encode8E (w: u8): encode w = [:: w].
  Proof.
    have {2}<-:= decodeK w.
    rewrite /encode /decode /make_vec /split_vec divnn modnn /= mul0n.
    by rewrite Z.lor_0_r /wrepr word.ureprK.
  Qed.

End LE.

Class pointer_op (pointer: eqType) : Type := PointerOp {
  add : pointer -> Z -> pointer;
  sub : pointer -> pointer -> Z;

  add_sub : forall p k, add p (sub k p) = k;
  add_0   : forall p, add p 0 = p;
}.

Section POINTER.

Context (pointer: eqType) (Pointer: pointer_op pointer).

Class coreMem (core_mem: Type) := CoreMem {
  uget : core_mem -> pointer -> u8;
  uset : core_mem -> pointer -> u8 -> core_mem;

  validr : core_mem -> pointer -> wsize -> exec unit;
  validw : core_mem -> pointer -> wsize -> exec unit;

  sub_add : forall m p s i t,
    validw m p s = ok t -> 0 <= i < wsize_size s -> sub (add p i) p = i;

  validw_uset m p v p' s: validw (uset m p v) p' s = validw m p' s;

  validrP : forall m p s i t,
    validr m p s = ok t ->
    0 <= i < wsize_size s ->
    validr m (add p i) U8 = ok t;

  validw_validr : forall m p s i v t k,
    validw m p s = ok t ->
    0 <= i < wsize_size s ->
    validr (uset m (add p i) v) k U8 = if add p i == k then ok t else validr m k U8;

  setP : forall m z1 z2 v,
    uget (uset m z1 v) z2 = if z1 == z2 then v else uget m z2;

}.

End POINTER.

Module CoreMem.
Section CoreMem.

  Context {pointer: eqType} {Pointer: pointer_op pointer}.
  Context {core_mem: Type} {CM: coreMem Pointer core_mem}.

  Definition uread (m: core_mem) (ptr: pointer) n :=
    map (fun o => uget m (add ptr o)) (ziota 0 n).

  Definition read (m: core_mem) (ptr: pointer) (sz: wsize) : exec (word sz) :=
    Let _ := validr m ptr sz in
    ok (LE.decode sz (uread m ptr (wsize_size sz))).

  Definition uwrite (m: core_mem) (ptr: pointer) (sz: wsize) (w: word sz) :=
    foldl (fun m o => uset m (add ptr o) (LE.wread8 w o)) m (ziota 0 (wsize_size sz)).

  Definition write (m: core_mem) (ptr: pointer) (sz: wsize) (w: word sz) : exec core_mem :=
    Let _ := validw m ptr sz in
    ok (uwrite m ptr w).

  Lemma sub_add_ziota m t p s i:
   validw m p s = ok t -> i \in ziota 0 (wsize_size s) -> sub (add p i) p = i.
  Proof. by move=> hw; rewrite in_ziota !zify; apply: (sub_add hw). Qed.

  Lemma readV m p s: is_ok (read m p s) = is_ok (validr m p s).
  Proof. by rewrite /read; case: validr. Qed.

  Lemma writeV s (v:word s) m p: is_ok (write m p v) = is_ok (validw m p s).
  Proof. by rewrite /write; case: validw. Qed.

  Lemma write_uwrite  m p s (v:word s):
    is_ok (validw m p s) -> write m p v = ok (uwrite m p v).
  Proof. by rewrite /write => /is_okP [? ->]. Qed.

  Lemma read_uread  m p s:
    is_ok (validr m p s) -> read m p s = ok (LE.decode s (uread m p (wsize_size s))).
  Proof. by rewrite /read => /is_okP [? ->]. Qed.

  Lemma uwrite_uget m p ws (v:word ws) k t:
    validw m p ws = ok t ->
    uget (uwrite m p v) k =
       let i := sub k p in
       if (0 <=? i) && (i <? wsize_size ws) then (LE.wread8 v i)
       else uget m k.
  Proof.
    rewrite /uwrite -(in_ziota 0 (wsize_size ws) (sub k p)) => /sub_add_ziota.
    elim: ziota m => //= i l hrec m hsub.
    rewrite hrec; last by move=> ? hin;apply hsub; rewrite in_cons hin orbT.
    rewrite setP in_cons orbC; case: ifPn => //= _.
    case: eqP => [<- | hne].
    + by rewrite hsub ?mem_head ?eq_refl.
    by case: eqP => // ?;subst i; elim hne; rewrite add_sub.
  Qed.

  Lemma write_uget m m' p ws (v: word ws) k :
    write m p v = ok m' ->
    uget m' k =
      let i := sub k p in
       if (0 <=? i) && (i <? wsize_size ws) then (LE.wread8 v i)
       else uget m k.
  Proof. rewrite /write; t_xrbindP => ? hw <-; apply: uwrite_uget hw. Qed.

  Lemma uwrite_validr8 m p ws (v:word ws) t k:
    validw m p ws = ok t ->
    validr (uwrite m p v) k U8 =
      let i := sub k p in
      if (0 <=? i) && (i <? wsize_size ws) then ok tt
      else validr m k U8.
  Proof.
    rewrite /uwrite -(in_ziota 0 (wsize_size ws) (sub k p)) => hw.
    have : forall i, i \in ziota 0 (wsize_size ws) →
             sub (add p i) p = i /\ 0 <= i < wsize_size ws.
    + move=> i hin;split;first by apply: (sub_add_ziota hw hin).
      by move: hin;rewrite in_ziota !zify.
    elim: ziota m hw => //= i l hrec m hv hsub.
    rewrite hrec ?validw_uset //; last by move=> ? hin;apply hsub; rewrite in_cons hin orbT.
    rewrite (validw_validr _ _ hv); last by case: (hsub i (mem_head _ _)).
    rewrite in_cons orbC; case: ifPn => //=.
    case: eqP => [<- | hne].
    + by case: (hsub i (mem_head _ _)) => -> _; rewrite eq_refl; case: (t).
    by case: eqP => // ?;subst i; elim hne; rewrite add_sub.
  Qed.

  Lemma uread8_get m p : LE.decode U8 (uread m p (wsize_size U8)) = uget m p.
  Proof. by rewrite /uread /= -LE.encode8E LE.decodeK add_0. Qed.

  Lemma write_read8 m m' p ws (v: word ws) k :
    write m p v = ok m' ->
    read m' k U8 =
      let i := sub k p in
       if (0 <=? i) && (i <? wsize_size ws) then ok (LE.wread8 v i)
       else read m k U8.
  Proof.
    rewrite /write; t_xrbindP => ? hv <-.
    by rewrite /read (uwrite_validr8 v k hv) /= !uread8_get (uwrite_uget _ _ hv) /=; case:ifP.
  Qed.

  Delimit Scope nat_scope with N_.

  Lemma rangeP x1 x2 x3 : reflect (x1 <= x2 < x3) ((x1 <=? x2) && (x2 <? x3)).
  Proof. by case: andP => h;constructor; move: h;rewrite !zify. Qed.

  Lemma Z_of_nat_range i s: (i < Z.to_nat (wsize_size s))%N_ ->
     0 <= Z.of_nat i < wsize_size s.
  Proof.
    move=> hi; split;first by Psatz.lia.
    by move/ltP:hi; rewrite Nat2Z.inj_lt ?Z2Nat.id.
  Qed.

  Lemma writeP_eq m m' p ws (v: word ws) :
    write m p v = ok m' ->
    uread m' p (wsize_size ws) = LE.encode v.
  Proof.
    rewrite /write; t_xrbindP => t hv <-.
    apply (eq_from_nth (x0 := (wrepr U8 0))).
    + by rewrite size_map size_ziota LE.size_encode.
    move=> i; rewrite size_map size_ziota => hi.
    rewrite (nth_map 0%Z) ?size_ziota // nth_ziota // Z.add_0_l.
    rewrite (uwrite_uget _ _ hv) /=.
    have /dup[h1 /rangeP h2] := Z_of_nat_range hi.
    by rewrite (sub_add hv h1) h2 /LE.wread8 Nat2Z.id.
  Qed.

  Definition disjoint_range p s p' s' :=
    forall i i', 0 <= i < wsize_size s -> 0 <= i' < wsize_size s' ->
       add p i <> add p' i'.

  Lemma ureadP m1 m2 p1 p2 s:
    reflect (forall i, 0 <= i < wsize_size s -> uget m1 (add p1 i) = uget m2 (add p2 i))
            (uread m1 p1 (wsize_size s) == uread m2 p2 (wsize_size s)).
  Proof.
    apply: (@equivP
      (forall i, i \in ziota 0 (wsize_size s) ->
        uget m1 (add p1 i) = uget m2 (add p2 i))); last first.
    + by split=> h i hi;apply h; move: hi; rewrite in_ziota !zify.
    rewrite /uread;elim: ziota => /=.
    + by rewrite eq_refl; constructor.
    move=> i l hrec;rewrite eqseq_cons; case: eqP => /= heq.
    + case:hrec => hin; constructor.
      + by move=> k;rewrite in_cons => /orP [/eqP ->| /hin].
      by move=> hi; apply hin => k hk; apply hi; rewrite in_cons hk orbT.
    constructor => hin; apply heq; apply hin; apply mem_head.
  Qed.

  Lemma uread_decode m1 m2 p1 p2 s:
    reflect (forall i, 0 <= i < wsize_size s -> uget m1 (add p1 i) = uget m2 (add p2 i))
            (LE.decode s (uread m1 p1 (wsize_size s)) == LE.decode s (uread m2 p2 (wsize_size s))).
  Proof.
    have -> : (LE.decode s (uread m1 p1 (wsize_size s)) == LE.decode s (uread m2 p2 (wsize_size s))) =
              (uread m1 p1 (wsize_size s) == uread m2 p2 (wsize_size s)); last by apply ureadP.
    apply Bool.eq_true_iff_eq; split => [/eqP | /eqP ->]; last by rewrite eq_refl.
    move=> /LE.decode_inj; rewrite !size_map size_iota => /(_ erefl erefl) ->; apply eq_refl.
  Qed.

  Lemma writeP_neq m m' p s (v :word s) p' s':
    write m p v = ok m' ->
    disjoint_range p s p' s' ->
    uread m' p' (wsize_size s') = uread m p' (wsize_size s').
  Proof.
    rewrite /write; t_xrbindP => tt hv <- hd.
    apply /eqP /ureadP => i hi; rewrite (uwrite_uget _ _ hv) /=; case:ifP => //.
    rewrite !zify => ?; elim: (hd (sub (add p' i) p) i) => //.
    by rewrite add_sub.
  Qed.

End CoreMem.
End CoreMem.

(* ** Memory
 * -------------------------------------------------------------------- *)

Notation Uptr := U64 (only parsing).
Notation pointer := (word Uptr) (only parsing).

Definition no_overflow (p: pointer) (sz: Z) : bool :=
  (wunsigned p + sz <=? wbase Uptr)%Z.

Definition disjoint_zrange (p: pointer) (s: Z) (p': pointer) (s': Z) :=
  [/\ no_overflow p s,
      no_overflow p' s' &
      wunsigned p + s <= wunsigned p' \/
        wunsigned p' + s' <= wunsigned p]%Z.

Definition disjoint_range p s p' s' :=
  disjoint_zrange p (wsize_size s) p' (wsize_size s').

Definition between (pstk : pointer)  (sz : Z) (p : pointer) (s : wsize) : bool :=
  ((wunsigned pstk <=? wunsigned p) && (wunsigned p + wsize_size s <=? wunsigned pstk + sz))%Z.

Lemma between_leb pstk sz p s pstk' sz' :
  ((wunsigned pstk' <=? wunsigned pstk) && (wunsigned pstk + sz <=? wunsigned pstk' + sz'))%Z ->
  between pstk sz p s ->
  between pstk' sz' p s.
Proof.
rewrite /between => /andP [] /ZleP a /ZleP b /andP [] /ZleP c /ZleP d.
apply/andP; split; apply/ZleP; Psatz.lia.
Qed.

Lemma between_byte pstk sz b i ws :
  no_overflow b (wsize_size ws) →
  between pstk sz b ws →
  0 <= i ∧ i < wsize_size ws →
  between pstk sz (b + wrepr U64 i) U8.
Proof.
  rewrite /between !zify; change (wsize_size U8) with 1 => novf [] lo hi i_range.
  rewrite wunsigned_add; first Psatz.lia.
  move: (wunsigned_range b); Psatz.lia.
Qed.

Definition pointer_range (lo hi: pointer) : pred pointer :=
  λ p, (wunsigned lo <=? wunsigned p) && (wunsigned p <? wunsigned hi).

Lemma pointer_range_between lo hi p :
  pointer_range lo hi p →
  between lo (wunsigned hi - wunsigned lo) p U8.
Proof.
  rewrite /pointer_range /between !zify.
  change (wsize_size U8) with 1.
  Psatz.lia.
Qed.

(* -------------------------------------------------- *)

Class alignment : Type :=
  Alignment {
      is_align : pointer -> wsize -> bool
    ; is_align_add ptr1 ptr2 sz : is_align ptr1 sz -> is_align ptr2 sz -> is_align (ptr1 + ptr2) sz
    ; is_align_mod ptr sz : (wunsigned ptr mod wsize_size sz = 0)%Z -> is_align ptr sz
    ; is_align_m sz sz' ptr : (sz' ≤ sz)%CMP → is_align ptr sz → is_align ptr sz'
    ; is_align_no_overflow ptr sz : is_align ptr sz → no_overflow ptr (wsize_size sz)
    }.

Lemma cut_wbase_Uptr sz :
  wbase Uptr = (wsize_size sz * CoqWord.word.modulus (nat63.+3 - (Nat.log2 (wsize_size_minus_1 sz))))%Z.
Proof. by case: sz; vm_compute. Qed.

Lemma is_align8 (AL:alignment) ptr : is_align ptr U8.
Proof. by apply is_align_mod; rewrite wsize8 /= Z.mod_1_r. Qed.

Lemma is_align_mul (AL:alignment) sz j : is_align (wrepr _ (wsize_size sz * j)) sz.
Proof.
  apply is_align_mod.
  have hn := wsize_size_pos sz.
  have hnz : wsize_size sz ≠ 0%Z by Psatz.lia.
  rewrite wunsigned_repr.
  rewrite -/(wbase Uptr) (cut_wbase_Uptr sz).
  by rewrite (Z.mul_comm _ (CoqWord.word.modulus _)) mod_pq_mod_q // Z.mul_comm Z_mod_mult.
Qed.

Lemma is_align_array (AL:alignment) ptr sz j : 
  is_align ptr sz → is_align (wrepr _ (wsize_size sz * j) + ptr) sz.
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
  elim_div => /(_ ws_pos) [] ->{sz} D.
  case: eqP => ?.
  - exists z; Psatz.lia.
  exists (z + 1); Psatz.lia.
Qed.

Lemma round_ws_range ws sz :
  sz <= round_ws ws sz < sz + wsize_size ws.
Proof.
  have ws_pos := wsize_size_pos ws.
  rewrite /round_ws; elim_div => - [] // -> []; last by Psatz.lia.
  case: eqP; Psatz.lia.
Qed.

(** Round to the multiple of [sz'] below. *)
Definition align_word (sz sz': wsize) (p: word sz) : word sz :=
  wand p (wrepr sz (-wsize_size sz')).

Lemma align_word_U8 sz (p: word sz) :
  align_word U8 p = p.
Proof. by rewrite /align_word wandC wandN1. Qed.

Lemma align_word_aligned (sz sz': wsize) (p: word sz) :
  wunsigned (align_word sz' p) mod wsize_size sz' == 0.
Proof.
  replace (wsize_size sz')
    with (2 ^ Z.of_nat match sz' with
                       | U8 => 0
                       | U16 => 1
                       | U32 => 2
                       | U64 => 3
                       | U128 => 4
                       | U256 => 5
                       end).
  2: by case: sz'.
  rewrite /align_word -wand_modulo -wandA.
  set k := (X in wand p X).
  replace k with (0%R : word sz); first by rewrite wandC wand0.
  subst k; clear; apply/eqP.
  by case: sz'; case: sz.
Qed.

Lemma align_word_le sz sz' (p: word sz) :
  wunsigned (align_word sz' p) <= wunsigned p.
Proof.
Admitted.

Lemma align_word_bounded sz sz' (p: word sz) :
  wunsigned p - wsize_size sz' < wunsigned (align_word sz' p).
Proof.
Admitted.

Definition top_stack_after_alloc (top: pointer) (ws: wsize) (sz: Z) : pointer :=
  align_word ws (top + wrepr Uptr (- sz)).

Lemma top_stack_after_aligned_alloc p ws sz :
  wunsigned p mod wsize_size ws == 0 →
  top_stack_after_alloc p ws sz = (p + wrepr Uptr (- round_ws ws sz))%R.
Proof.
Admitted.

Lemma top_stack_after_alloc_bounded p ws sz :
  0 <= sz <= wunsigned p →
  wunsigned p - wunsigned (top_stack_after_alloc p ws sz) <= sz + wsize_size ws.
Proof.
  rewrite /top_stack_after_alloc => sz_pos.
  move: (align_word _ _) (align_word_bounded ws (p + wrepr Uptr (- sz))) => q.
  rewrite wunsigned_add; first Psatz.lia.
  have := wunsigned_range p.
  Psatz.lia.
Qed.

Class memory (mem: Type) : Type :=
  Memory {
      read_mem  : mem -> pointer -> forall (s:wsize), exec (word s)
    ; write_mem : mem -> pointer -> forall (s:wsize), word s -> exec mem
    ; valid_pointer : mem -> pointer -> wsize -> bool
    ; stack_root : mem -> pointer
    ; stack_limit : mem -> pointer
    ; frames : mem -> seq pointer
    ; alloc_stack : mem -> wsize -> Z -> Z -> exec mem (* alignement, size, extra-size *)
    ; free_stack : mem -> mem
    ; init : seq (pointer * Z) → pointer → exec mem
    }.

Arguments read_mem : simpl never.
Arguments write_mem {_ _} _ _ _ _ : simpl never.
Arguments valid_pointer : simpl never.

Definition top_stack {mem: Type} {M: memory mem} (m: mem) : pointer :=
  head (stack_root m) (frames m).

Section SPEC.
  Context (AL: alignment) mem (M: memory mem)
    (m: mem) (ws:wsize) (sz: Z) (sz': Z) (m': mem).
  Let pstk := top_stack m'.

  Record alloc_stack_spec : Prop := mkASS {
    ass_read_old : forall p s, valid_pointer m p s -> read_mem m p s = read_mem m' p s;
    ass_valid    : forall p,
      valid_pointer m' p U8 =
      valid_pointer m p U8 || between pstk sz p U8;
    ass_align    : forall ofs s,
      (s <= ws)%CMP ->
      is_align (pstk + wrepr _ ofs) s = is_align (wrepr _ ofs) s ;
    ass_fresh    : forall p s, valid_pointer m p s ->
      (wunsigned p + wsize_size s <= wunsigned pstk \/
       wunsigned pstk + sz <= wunsigned p)%Z;
    ass_root   : stack_root m' = stack_root m;
    ass_limit  : stack_limit m' = stack_limit m;
    ass_frames : frames m' = top_stack_after_alloc (top_stack m) ws (sz + sz') :: frames m;
  }.

  Record stack_stable : Prop := mkSS {
    ss_root: stack_root m = stack_root m';
    ss_limit: stack_limit m = stack_limit m';
    ss_frames: frames m = frames m';
  }.

  Record free_stack_spec : Prop := mkFSS {
    fss_read_old : forall p s, valid_pointer m' p s -> read_mem m p s = read_mem m' p s;
    fss_valid    : ∀ p, valid_pointer m' p U8 = valid_pointer m p U8 && ~~ pointer_range (top_stack m) (top_stack m') p;
    fss_root : stack_root m' = stack_root m;
    fss_limit : stack_limit m' = stack_limit m;
    fss_frames : frames m' = behead (frames m);
   }.

End SPEC.

Arguments alloc_stack_spec {_ _ _} _ _ _ _.
Arguments stack_stable {_ _} _ _.
Arguments free_stack_spec {_ _} _ _.

(** Pointer arithmetic *)
Instance Pointer : pointer_op pointer.
Proof.
refine
  {| add p k := (p + wrepr Uptr k)%R
   ; sub p1 p2 := wunsigned p1 - wunsigned p2
  |}.
- abstract (move => p k; rewrite wrepr_sub !wrepr_unsigned; ssrring.ssring).
- abstract (move => p; rewrite wrepr0; ssrring.ssring).
Defined.

Lemma addE p k : add p k = (p + wrepr Uptr k)%R.
Proof. by []. Qed.

Lemma subE p1 p2 : sub p1 p2 = wunsigned p1 - wunsigned p2.
Proof. by []. Qed.

Lemma addC p i j : add (add p i) j = add p (i + j).
Proof. rewrite /= wrepr_add; ssrring.ssring. Qed.

Global Opaque Pointer.

Module Type MemoryT.

Declare Instance A : alignment.

Parameter mem : Type.

Declare Instance CM : coreMem Pointer mem.
Declare Instance M : memory mem.

Parameter readV : forall m p s,
  reflect (exists v, read_mem m p s = ok v) (valid_pointer m p s).

Parameter writeV : forall m p s v,
  reflect (exists m', write_mem m p s v = ok m') (valid_pointer m p s).

Parameter read_mem_error : forall m p s e, read_mem m p s = Error e -> e = ErrAddrInvalid.

Parameter readP : forall m p s, read_mem m p s = CoreMem.read m p s.
Parameter writeP : forall m p s (v:word s), write_mem m p s v = CoreMem.write m p v.

Parameter write_read8 : forall m m' p ws (v: word ws) k,
  write_mem m p ws v = ok m' ->
  read_mem m' k U8 =
    let i := wunsigned k - wunsigned p in
    if (0 <=? i) && (i <? wsize_size ws) then ok (LE.wread8 v i)
    else read_mem m k U8.

Parameter writeP_eq : forall m m' p s (v :word s),
  write_mem m p s v = ok m' ->
  read_mem m' p s = ok v.

Parameter writeP_neq : forall m m' p s (v :word s) p' s',
  write_mem m p s v = ok m' ->
  disjoint_range p s p' s' ->
  read_mem m' p' s' = read_mem m p' s'.

Parameter write_valid : forall m m' p s (v :word s) p' s',
  write_mem m p s v = ok m' ->
  valid_pointer m' p' s' = valid_pointer m p' s'.

Parameter valid_pointerP : ∀ m p ws,
    reflect (is_align p ws ∧ ∀ k, 0 <= k < wsize_size ws -> valid_pointer m (p + wrepr U64 k) U8) (valid_pointer m p ws).

Parameter read_write_any_mem :
  forall m1 m1' pr szr pw szw vw m2 m2',
    valid_pointer m1 pr szr ->
    read_mem m1 pr szr = read_mem m1' pr szr ->
    write_mem m1 pw szw vw = ok m2 ->
    write_mem m1' pw szw vw = ok m2' ->
    read_mem m2 pr szr = read_mem m2' pr szr.

(* -------------------------------------------------------------------- *)
Parameter alloc_stackP : forall m m' ws sz sz',
  alloc_stack m ws sz sz' = ok m' -> alloc_stack_spec m ws sz sz' m'.

Parameter alloc_stack_complete :
  forall m ws sz sz',
    let: old_size:= sub (stack_root m) (top_stack m) in
    let: max_size := sub (stack_root m) (stack_limit m) in
    let: available := max_size - old_size in
    [&& 0 <=? sz, 0 <=? sz' &
    if is_align (top_stack m) ws
    then round_ws ws (sz + sz') <=? available (* tight bound *)
    else sz + sz' + wsize_size ws <=? available (* loose bound, exact behavior is under-specified *)
    ] →
    ∃ m', alloc_stack m ws sz sz' = ok m'.

Parameter write_mem_stable : forall m m' p s v,
  write_mem m p s v = ok m' -> stack_stable m m'.

Parameter free_stackP : forall m,
  free_stack_spec m (free_stack m).

End MemoryT.
