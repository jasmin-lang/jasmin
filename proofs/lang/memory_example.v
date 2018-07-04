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

(** This defines an example instance of the memory model.

  Stack allocation is not described.
*)

Require memory_model array.

Import Utf8.
Import all_ssreflect all_algebra.
Import ZArith.
Import ssrZ.
Import type word utils array.
Import memory_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma zip_nil S T (m: seq T) : zip [::] m = @ nil (S * T).
Proof. by case: m. Qed.

Lemma cut_wbase_Uptr sz :
  wbase Uptr = (wsize_size sz * CoqWord.word.modulus (nat63.+3 - (Nat.log2 (wsize_size_minus_1 sz))))%Z.
Proof. by case: sz; vm_compute. Qed.

Section Align.

  Let is_align (ptr: pointer) (ws: wsize) :=
    let w := wunsigned ptr in
    (w mod wsize_size ws == 0)%Z.

  Lemma is_align_array ptr sz j :
    is_align ptr sz → is_align (wrepr _ (wsize_size sz * j) + ptr) sz.
  Proof.
    have hn := wsize_size_pos sz.
    have hnz : wsize_size sz ≠ 0%Z by Psatz.lia.
    rewrite /is_align => /eqP /Zmod_divides [] // p hptr.
    rewrite /wunsigned CoqWord.word.addwE -!/(wunsigned _) Zplus_mod hptr -Zplus_mod.
    rewrite wunsigned_repr -/(wbase Uptr) (cut_wbase_Uptr sz).
    rewrite (Z.mul_comm _ (CoqWord.word.modulus _)) mod_pq_mod_q // (Z.mul_comm _ p) Z_mod_plus.
    2: Psatz.lia.
    by rewrite mod_pq_mod_q //; apply/eqP/Zmod_divides; eauto.
  Qed.

  Lemma is_align_no_overflow ptr sz :
    is_align ptr sz → no_overflow ptr (wsize_size sz).
  Proof.
    rewrite /is_align /no_overflow => /eqP ha; apply/ZleP.
    have hn := wsize_size_pos sz.
    have hnz : wsize_size sz ≠ 0%Z by Psatz.lia.
    move: (wunsigned ptr) (wunsigned_range ptr) ha => {ptr} ptr.
    rewrite (cut_wbase_Uptr sz); set a := CoqWord.word.modulus _.
    move: (wsize_size sz) hn hnz => n hn hnz hr /Zmod_divides [] // q ?; subst ptr.
    cut (q + 1 <= a)%Z; Psatz.nia.
  Qed.

End Align.

Module Type Endianness.

  Parameter encode : ∀ sz (w: word sz), seq u8.
  Parameter decode : ∀ sz, seq u8 → result unit (word sz).

  Axiom size_encode : ∀ sz (w: word sz), size (encode w) = Z.to_nat (wsize_size sz).

  Axiom decodeK : ∀ sz (w: word sz), decode sz (encode w) = ok w.

  Axiom size_decode : ∀ sz (bs : seq u8), size bs = Z.to_nat (wsize_size sz) → ∃ w, decode sz bs = ok w.

  Axiom decode_inj :
    ∀ sz (bs bs': seq u8) w,
      size bs = size bs' →
      size bs = Z.to_nat (wsize_size sz) →
      decode sz bs = ok w →
      decode sz bs' = ok w →
      bs = bs'.

End Endianness.

Module BigEndian : Endianness.
  Definition encode sz (w: word sz) : seq u8 := split_vec U8 w.
  Definition decode sz (n: seq u8) : result unit (word sz) := ok (make_vec sz n).

  Lemma size_encode sz (w: word sz) :
    size (encode w) = Z.to_nat (wsize_size sz).
  Proof.
    by rewrite /encode /split_vec size_map size_iota => {w}; case: sz.
  Qed.

  Lemma decodeK sz (w: word sz) :
    decode sz (encode w) = ok w.
  Proof. by rewrite /decode /encode make_vec_split_vec. Qed.

  Lemma size_decode sz bs :
    size bs = Z.to_nat (wsize_size sz) →
    ∃ w, decode sz bs = ok w.
  Proof. move => _; eexists; reflexivity. Qed.

  Lemma decode_inj sz (bs bs': seq u8) w :
    size bs = size bs' →
    size bs = Z.to_nat (wsize_size sz) →
    decode sz bs = ok w →
    decode sz bs' = ok w →
    bs = bs'.
  Proof.
    by move => eqsz hsz <- /(@ok_inj _ _ _ _) /esym /make_vec_inj; apply.
  Qed.

End BigEndian.

Module MemoryI (E: Endianness) : MemoryT.

  Instance A : alignment :=
    Alignment is_align_array is_align_no_overflow.

  Definition mem := FArray.array (result unit u8).

  Definition addresses (ptr: pointer) (sz: wsize) : seq Z :=
    map (λ o, wunsigned ptr + Z.of_nat o)%Z
      (iota 0 (Z.to_nat (wsize_size sz))).

  Lemma size_addresses ptr sz :
    size (addresses ptr sz) = Z.to_nat (wsize_size sz).
  Proof. by rewrite /addresses size_map size_iota. Qed.

  Lemma uniq_addresses ptr sz :
    uniq (addresses ptr sz).
  Proof.
    rewrite /addresses map_inj_uniq; first exact: iota_uniq.
    move => x y h; apply: Nat2Z.inj; Psatz.lia.
  Qed.

  Definition check_pointer ptr ws : exec unit :=
    assert (is_align ptr ws) ErrAddrInvalid.

  Definition to_exec E T (e: result E T) : exec T :=
    if e is Ok r then ok r else Error ErrAddrInvalid.

  Definition read_mem (m: mem) (ptr: pointer) (sz: wsize) : exec (word sz) :=
    Let _ := check_pointer ptr sz in
    to_exec (mapM (FArray.get m) (addresses ptr sz) >>= E.decode sz).

  Definition write_mem (m: mem) (ptr: pointer) (sz: wsize) (w: word sz) : exec mem :=
    Let _ := read_mem m ptr sz in
    ok (
        foldl
          (λ m av, FArray.set m av.1 (ok av.2))
          m
          (zip (addresses ptr sz) (E.encode w))
      ).

  Arguments write_mem : clear implicits.

  Definition valid_pointer (m: mem) (ptr: pointer) (sz: wsize) : bool :=
    if read_mem m ptr sz is Ok _ then true else false.

  Lemma valid_align m p s :
    valid_pointer m p s → is_align p s.
  Proof.
    by rewrite /valid_pointer /read_mem /check_pointer; case: is_align.
  Qed.

  Notation "'is_ok' m" := (if m is Ok _ then true else false) (at level 10).

  Definition all_ok (m: mem) (r: seq Z) : bool :=
    all (λ a, is_ok (FArray.get m a)) r.

  Lemma all_okP m r :
    reflect (∃ x, mapM (FArray.get m) r = ok x) (all_ok m r).
  Proof.
    elim: r.
    - by constructor; exists [::].
    move => a r /=.
    case: (FArray.get m a); last first.
    - by move => e _; constructor => - [].
    move => b /= [] h; constructor.
    - case: h => bs -> /=; eauto.
    case => bs'; t_xrbindP => bs k _; apply: h; eauto.
  Qed.

  Lemma valid_pointerE m p s :
    valid_pointer m p s = ((check_pointer p s == ok tt) && (all_ok m (addresses p s))).
  Proof.
    rewrite /valid_pointer /read_mem.
    case: check_pointer => // - [] /=.
    have := @mapM_size _ _ _ (FArray.get m) (addresses p s).
    rewrite size_addresses.
    move: (addresses p s) => r.
    case: all_okP.
    - case => bs -> /(_ _ erefl) hsz /=.
      have := @E.size_decode s bs.
      by rewrite hsz => /(_ erefl) [w ->].
    case: mapM => //.
    move => bs []; eauto.
  Qed.

  Lemma readV m p s :
    reflect (∃ v, read_mem m p s = ok v) (valid_pointer m p s).
  Proof.
    rewrite /valid_pointer; case: read_mem => [ w | e ]; constructor; eauto.
    by move => [].
  Qed.

  Lemma writeV m p s v :
    reflect (∃ m', write_mem m p s v = ok m') (valid_pointer m p s).
  Proof.
    rewrite /write_mem /valid_pointer; case: read_mem => [ w | e ] /=; constructor; eauto.
    by move => [].
  Qed.

  Lemma read_mem_error m p s e :
    read_mem m p s = Error e → e = ErrAddrInvalid.
  Proof.
    rewrite /read_mem /check_pointer; case: is_align => /=; last by case.
    by case: (Let _ := _ in _) => //= _ [].
  Qed.

  Lemma writeP_eq_aux T dec (v: T)
        (f := (λ (m' : mem) (av : Z * u8), FArray.set m' av.1 (ok av.2))) :
    ∀ n addr bytes acc m,
      size addr = n → size bytes = n → dec (acc ++ bytes) = ok v → uniq addr →
      to_exec (Let x := mapM
                          (FArray.get (foldl f m
                                 (zip addr bytes))) addr in dec (acc ++ x)) = ok v.
  Proof.
    elim.
    - by case => // - [] //= _ _ _ _ -> _.
    move => n ih [] // a addr [] //= b bytes acc m /succn_inj haddr /succn_inj hbytes hdec /andP [] ha hu.
    have {ih} := ih _ _ (rcons acc b) (f m (a, b)) haddr hbytes _ hu.
    rewrite cat_rcons => /(_ hdec) {haddr hbytes hdec hu}.
    set q := foldl _ _ _.
    have -> /= : FArray.get q a = ok b.
    - have : FArray.get (f m (a, b)) a = ok b := FArray.setP_eq _ _ _.
      subst q; move: (f _ _) => {m}.
      elim: addr ha bytes.
      + by move => _ bytes m; rewrite zip_nil /=.
      move => a' addr ih ha [] //= b' bytes m hm.
      move: ha; rewrite in_cons negb_or => /andP [] haa' ha.
      rewrite ih // -hm -/(FArray.get _ a) -/(FArray.get m a).
      apply: FArray.setP_neq.
      by rewrite eq_sym.
    case hsuff: (mapM _ _) => [ suff | // ] /=.
    by rewrite cat_rcons.
  Qed.

  Lemma writeP_eq m m' p s (v: word s) :
      write_mem m p s v = ok m' →
      read_mem m' p s = ok v.
  Proof.
    rewrite /write_mem /read_mem; t_xrbindP => _ u -> _ <-.
    exact: (writeP_eq_aux (acc := nil) m (size_addresses p s) (E.size_encode v) (E.decodeK v) (uniq_addresses p s)).
  Qed.

  Definition mem_eq_on (rng: seq Z) (m m': mem) : Prop :=
    ∀ a : Z, a \in rng → FArray.get m a = FArray.get m' a.

  Lemma mem_eq_onI rng m m' :
    mem_eq_on rng m m' →
    if rng is a :: r then
      FArray.get m a = FArray.get m' a ∧ mem_eq_on r m m'
    else True.
  Proof.
    case: rng => // a rng heq; split.
    - apply: heq; exact: mem_head.
    move => a' ha'; apply: heq.
    by rewrite in_cons ha' orbT.
  Qed.

  Definition mem_eq_exc (rng: seq Z) (m m': mem) : Prop :=
    ∀ a, a \notin rng → FArray.get m a = FArray.get m' a.

  Definition disj_seq (r r': seq Z) : Prop :=
    ∀ a, a \in r → a \in r' → False.

  Lemma mem_eq_exc_disjoint_eq_on r r' m m' :
    mem_eq_exc r m m' →
    disj_seq r r' →
    mem_eq_on r' m m'.
  Proof.
    move => hee hd a ha; apply: hee; move/hd: ha.
    by case: (_ \in _) => // /(_ erefl).
  Qed.

  Lemma eq_on_mapM rng m m' :
    mem_eq_on rng m m' →
    mapM (FArray.get m) rng = mapM (FArray.get m') rng.
  Proof.
    elim: rng => //= a rng ih /mem_eq_onI [<- heq].
    case: (FArray.get m a) => //= b.
    by rewrite ih.
  Qed.

  Lemma eq_on_read m m' p s :
    mem_eq_on (addresses p s) m m' →
    read_mem m p s = read_mem m' p s.
  Proof.
    move => heq; rewrite /read_mem.
    case: check_pointer => //= _.
    by rewrite (eq_on_mapM heq).
  Qed.

  Lemma mapM_mem_eq_on rng m m' :
    all_ok m rng →
    mapM (FArray.get m) rng = mapM (FArray.get m') rng →
    mem_eq_on rng m m'.
  Proof.
    case/all_okP.
    elim: rng => //= a rng ih bs'.
    t_xrbindP => b ok_b bs ok_bs _ {bs'}.
    rewrite ok_b ok_bs /= => /esym.
    t_xrbindP => b' ok_b' bs' ok_bs' ??; subst b' bs'.
    move => a'; rewrite in_cons.
    case: eqP.
    - by move => -> _; rewrite ok_b ok_b'.
    move => _. apply: ih; eauto.
    by rewrite ok_bs ok_bs'.
  Qed.

  Lemma read_mem_eq_on m m' p s :
    check_pointer p s = ok tt →
    all_ok m (addresses p s) →
    read_mem m p s = read_mem m' p s →
    mem_eq_on (addresses p s) m m'.
  Proof.
    move => hchk hok; rewrite /read_mem hchk /= => h.
    apply: mapM_mem_eq_on => //.
    case/all_okP: hok h (@mapM_size _ _ _ (FArray.get m) (addresses p s)) => bs -> /= h /(_ _ erefl) hsz.
    have := @E.decode_inj s bs.
    move: (size_addresses p s) h; rewrite hsz => /E.size_decode [w] -> /=.
    case: (mapM (FArray.get m')) (@mapM_size _ _ _ (FArray.get m') (addresses p s)) => //= bs' /(_ _ erefl) hsz' ok_w /(_ bs' w).
    rewrite -hsz -hsz' => /(_ erefl (size_addresses _ _) erefl).
    by case: E.decode ok_w => // _ [<-] /(_ erefl) ->.
  Qed.

  Lemma write_mem_eq_exc m p s v m' :
    write_mem m p s v = ok m' →
    mem_eq_exc (addresses p s) m' m.
  Proof.
    rewrite /write_mem; t_xrbindP => // _ _ <- {m'}.
    elim: (addresses p s) m {v} (E.encode v).
    - by move => m v; rewrite zip_nil.
    move => a r ih m [] //= b v a'.
    rewrite in_cons negb_or => /andP [/eqP haa' ha'].
    rewrite ih // -/(FArray.get (FArray.set _ _ _) a') FArray.setP_neq //.
    apply/eqP; auto.
  Qed.

  Lemma disjoint_range_disj_seq p s p' s' :
    disjoint_range p s p' s' →
    disj_seq (addresses p s) (addresses p' s').
  Proof.
    case => ho ho' hd a /mapP [/= n].
    rewrite mem_iota => /andP [/leP hnl /ltP hnr] -> {a} /mapP [/= n'].
    rewrite mem_iota => /andP [/leP hn'l /ltP hn'r].
    have hs := wsize_size_pos s.
    have hs' := wsize_size_pos s'.
    zify.
    move: hnr hn'r; rewrite !add0n !Z2Nat.id; Psatz.lia.
  Qed.

  Lemma write_mem_same_ok m p s v m' a :
    write_mem m p s v = ok m' →
    is_ok (FArray.get m' a) = is_ok (FArray.get m a).
  Proof.
    rewrite /write_mem; t_xrbindP => u ok_r <-.
    transitivity ((a \in addresses p s) || is_ok (FArray.get m a)); last first.
    - have : valid_pointer m p s by rewrite /valid_pointer ok_r.
      rewrite valid_pointerE => /andP [] _ /allP /(_ a).
      by case: (_ \in _) => // /(_ erefl) ->.
    move: (size_addresses p s); rewrite -(E.size_encode v).
    elim: (addresses p s) {ok_r} m {v} (E.encode v).
    - by move => m v ?; rewrite zip_nil.
    move => a' r ih m [] //= b bs /succn_inj hsz.
    rewrite ih // in_cons -/(FArray.get (FArray.set _ _ _) _) FArray.setP.
    case: (_ \in _); first by rewrite orbT.
    by rewrite eq_sym; case: eqP.
  Qed.

  Lemma write_valid m m' p s (v: word s) p' s' :
    write_mem m p s v = ok m' →
    valid_pointer m' p' s' = valid_pointer m p' s'.
  Proof.
    rewrite !valid_pointerE => ok_m'.
    case: (_ == _) => //=.
    apply: eq_all => a.
    exact: (write_mem_same_ok a ok_m').
  Qed.

  Lemma writeP_neq m m' p s (v :word s) p' s' :
    write_mem m p s v = ok m' →
    disjoint_range p s p' s' →
    read_mem m' p' s' = read_mem m p' s'.
  Proof.
    move => ok_m' hdisj.
    apply: eq_on_read.
    apply: mem_eq_exc_disjoint_eq_on.
    - exact: (write_mem_eq_exc ok_m').
    exact: disjoint_range_disj_seq.
  Qed.

  Lemma write_mem_eq_on m1 m1' p sz v m2 m2' :
    write_mem m1 p sz v = ok m2 →
    write_mem m1' p sz v = ok m2' →
    mem_eq_on (addresses p sz) m2 m2'.
  Proof.
    move => /writeP_eq h /writeP_eq; rewrite -h => /esym.
    have : valid_pointer m2 p sz.
    + by case:readV => //; rewrite h => - []; eauto.
    rewrite valid_pointerE => /andP [] /eqP hc ha.
    exact: read_mem_eq_on.
  Qed.

  Lemma read_write_any_mem m1 m1' pr szr pw szw vw m2 m2' :
    valid_pointer m1 pr szr ->
    read_mem m1 pr szr = read_mem m1' pr szr ->
    write_mem m1 pw szw vw = ok m2 ->
    write_mem m1' pw szw vw = ok m2' ->
    read_mem m2 pr szr = read_mem m2' pr szr.
  Proof.
    rewrite valid_pointerE => /andP [] /eqP hchk hvalid eqr hw hw'.
    rewrite /read_mem hchk /=.
    suff : mem_eq_on (addresses pr szr) m2 m2'.
    + by move => /eq_on_mapM ->.
    move => a ha.
    case ha': (a \in addresses pw szw).
    + exact: (write_mem_eq_on hw hw').
    rewrite (write_mem_eq_exc hw (negbT ha')) (write_mem_eq_exc hw' (negbT ha')).
    exact: (read_mem_eq_on hchk hvalid eqr).
  Qed.

Definition top_stack  `(mem) : pointer := 0%R.
Definition caller `(mem) `(pointer) : option pointer := None.
Definition frame_size `(mem) `(pointer) : option Z := None.

Definition alloc_stack `(mem) `(Z) : exec mem := Error ErrStack.
Definition free_stack (m: mem) `(Z) : mem := m.

Fixpoint array_zero_fill_loop m p s : mem :=
  if s is S s' then
    array_zero_fill_loop (FArray.set m p (ok 0%R)) (Z.succ p) s'
  else m.

Definition array_zero_fill (m: mem) (rng: pointer * Z) : mem :=
  let '(p, sz) := rng in
  array_zero_fill_loop m (wunsigned p) (Z.to_nat sz).

Definition init_mem (s: seq (pointer * Z)) : mem :=
  let empty := FArray.cnst (Error tt) in
  foldl array_zero_fill empty s.

Instance M : memory mem :=
  Memory read_mem write_mem valid_pointer top_stack caller frame_size alloc_stack free_stack init_mem.

Lemma alloc_stackP m m' sz :
  alloc_stack m sz = ok m' -> alloc_stack_spec m sz m'.
Proof. by []. Qed.

Lemma write_mem_stable m m' p s v :
  write_mem m p s v = ok m' -> stack_stable m m'.
Proof. by []. Qed.

Lemma free_stackP m sz :
  frame_size m (top_stack m) = Some sz ->
  free_stack_spec m sz (free_stack m sz).
Proof. by []. Qed.

End MemoryI.
