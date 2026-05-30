From Coq Require Import ZArith Lia.
From HB Require Import structures.

From mathcomp Require Import
  ssreflect
  ssralg
  ssrfun
  ssrbool
  ssrnat
  eqtype
  fintype
  matrix
  order
  seq
  word
  word_ssrZ
.

Require Import
  utils
  word
  warray_
  memory_model
  low_memory
  values
.

Import Order.TTheory.

#[local] Open Scope ring_scope.
#[local] Open Scope Z.

Section WSEQ.

Definition wseq : Type := seq u8.

Definition dummy_wseq : wseq := [::].

Definition wseq_of_arr (len : positive) (a : WArray.array len) : wseq :=
  rdflt [::] (mapM (WArray.get8 a) (ziota 0 len)).

Section READ_WRITE.

  Context {pd : PointerData}.

  Definition read8 (m : mem) (p : pointer) (i : Z) : exec u8 :=
    CoreMem.read m Aligned (p + wrepr Uptr i)%R U8.

  Definition write8 (m : mem) (p : pointer) (i : Z) (b : u8) : exec mem :=
    CoreMem.write m Aligned (p + wrepr Uptr i)%R b.

  Definition read_wseq (m : mem) (p : pointer) (len : positive) : wseq :=
    rdflt [::] (mapM (read8 m p) (ziota 0 len)).

  Definition write_wseq m p (bs : wseq) : mem :=
    rdflt m (fill_mem m p bs).

End READ_WRITE.

Section PD.

Context {pd : PointerData}.

Lemma write_wseq_stack_stable {m p bytes} :
  stack_stable m (write_wseq m p bytes).
Proof.
rewrite /write_wseq; case h: fill_mem => //; exact: fill_mem_stack_stable h.
Qed.

Lemma write_wseq_validw_eq m p bytes :
  validw m =3 validw (write_wseq m p bytes).
Proof.
rewrite /write_wseq; case h: fill_mem => [m'|//]; exact: fill_mem_validw_eq h.
Qed.

Lemma write_wseq_disjoint m p bytes al p' ws :
  disjoint_zrange p (Z.of_nat (size bytes)) p' (wsize_size ws) ->
  read m al p' ws = read (write_wseq m p bytes) al p' ws.
Proof.
rewrite /write_wseq; by case h: fill_mem => [m'|//] /(fill_mem_disjoint h).
Qed.

Lemma fill_fill_mem (n : positive) a m p bytes :
  (forall k : Z, 0 <= k < n -> validw m Aligned (p + wrepr _ k)%R U8) ->
  WArray.fill n bytes = ok a ->
  exists m', fill_mem m p bytes = ok m'.
Proof.
move=> hv; rewrite /WArray.fill /WArray.fill_aux /fill_mem.
t_xrbindP=> /eqP hn [? a'] hfold /= ?; subst a'.
elim: bytes m 0 (WArray.empty n) {hn} hv hfold => [|b bytes hind] m z a0 hv /=;
  first by exists m.
t_xrbindP=> _ a' hset <- /hind {}hind.
move: hset => /WArray.set_bound.
rewrite WArray.mk_scale_U8 Z.mul_1_r wsize8 => -[h1 h2 _].
suff [m0 hm0] :
  exists m0, [elaborate write m Aligned (p + wrepr Uptr z)%R b = ok m0 ].
- rewrite hm0; apply: hind => k hk.
  rewrite (write_validw_eq hm0); apply: hv; lia.
apply/writeV.
rewrite /validw /= is_align8 (valid8_validw _ Aligned) andbT /= add_0.
apply: hv; lia.
Qed.

Lemma read_write_wseq bytes (n : positive) a (i : Z) w p m :
  (Zpos n <= wbase Uptr) ->
  (forall k : Z, 0 <= k < n -> validw m Aligned (p + wrepr _ k)%R U8) ->
  WArray.fill n bytes = ok a ->
  read a Aligned i U8 = ok w ->
  read (write_wseq m p bytes) Aligned (p + wrepr Uptr i)%R U8 = ok w.
Proof.
move=> hn hv ha; have [m' hm'] := fill_fill_mem hv ha.
rewrite (WArray.fill_get8 ha) /write_wseq hm' /= (fill_mem_read8 _ hm') /=
  -(WArray.fill_size ha); last lia.
case: andP => // -[/ZleP ? /ZltP ?] <-.
rewrite subE -{2 4 6}(GRing.addr0 p) (GRing.addrC p (wrepr _ _)) GRing.addrKA
  GRing.subr0 wunsigned_repr_small; last lia.
rewrite  positive_nat_Z; case: andP => // -[].
by split; [apply/ZleP|apply/ZltP].
Qed.

End PD.

End WSEQ.

Section WVEC.

#[local] Coercion Pos.to_nat : positive >-> nat.

Definition wvec (n : nat) : Type := 'rV[u8]_n.
Definition mkwvec (n : nat) (s : seq u8) : wvec n := \row_i nth 0%R s i.
Definition dummy_wvec (n : nat) : wvec n := \row_i 0%R.

Coercion wseq_of_wvec (n : nat) (v : wvec n) : wseq :=
  [seq v ord0 i | i <- enum 'I_n ].

Definition wvec_of_arr (n : positive) (a : WArray.array n) : wvec n :=
  mkwvec n (wseq_of_arr a).

Definition read_wvec
  {_ : PointerData} (m : mem) (p : pointer) (len : positive) : wvec len :=
  mkwvec len (read_wseq m p len).

Definition pad0 (n : positive) (s : wseq) : wseq :=
  nseq (n - size s) 0%R ++ take n s.

Lemma size_wseq_of_wvec n (v : wvec n) : size (wseq_of_wvec v) = n.
Proof. by rewrite /wseq_of_wvec size_map size_enum_ord. Qed.

(* TODO lia used to solve it
Lemma size_pad0 n s : size (pad0 n s) = n.
Proof.
  rewrite /pad0 size_cat size_nseq size_take; case: ifP => ?; lia.
*)

Definition wvec_of_val (n : positive) (v : value) : wvec (Pos.to_nat n) :=
  let d := dummy_wvec n in
  match v with
  | Vword ws w => mkwvec n (pad0 n (split_vec 8 w))
  | Varr _ a => if WArray.cast n a is Ok a' then wvec_of_arr a' else d
  | _ => d
  end.

End WVEC.
