(* -------------------------------------------------------------------- *)
require import AllCore Distr DList BitEncoding IntDiv SmtMap List StdOrder BitEncoding Bool.
(*---*) import Ring.IntID IntOrder BS2Int.
require import JUtils JArray JWord.

abstract theory ByteArray.

  clone include MonoArray with
    type elem <- W8.t,
    op dfl    <- W8.zero.

  op darray = dmap (dlist W8.dword size) of_list.

  abbrev [-printing] get8  (t:t) (i:int) : W8.t = t.[i].
  abbrev [-printing] get8d (t:t) (i:int) : W8.t = t.[i].

  abbrev [-printing] set8  (t:t) (i:int) (w:W8.t) : t = t.[i <- w].
  abbrev [-printing] set8d (t:t) (i:int) (w:W8.t) : t = t.[i <- w].

  abbrev [-printing] of_list8 = of_list.

  abstract theory WSB.
    type B.
    op r : int.
    op _zero : B.
    op _of_list : W8.t list -> B.
    op (\bits8) : B -> int -> W8.t.

    axiom _gt0_r : 0 < r.
    axiom _nth_of_list (l: W8.t list) k :
      size l = r =>
      _of_list l \bits8 k = nth W8.zero l k.
    axiom _wordP:
      forall (w1 w2 : B),
        (forall (i : int), 0 <= i && i < r => (w1 \bits8 i) = (w2 \bits8 i)) =>
      w1 = w2.
    axiom _zero_bits8 i : _zero \bits8 i = W8.zero.


    op get'Sd (t:t) (i:int) : B =
      _of_list (sub t i r)
    axiomatized by get'SdE.

    op set'Sd (t:t) (i:int) (w:B) =
      fill (fun k => w \bits8 k - i) i r t
    axiomatized by set'SdE.


    abbrev [-printing] get'S (t:t) (i:int) : B = get'Sd t (r * i).
    abbrev [-printing] set'S (t:t) (i:int) (w:B) = set'Sd t (r * i) w.
    theory Notation'S.
      abbrev "_.[_<-_]" = set'S.
    end Notation'S.
    export Notation'S.

    lemma get8_set'SdE (t:t) (i:int) (w:B) j :
      (set'Sd t i w).[j] =
      if i <= j < i + r /\ 0 <= j && j < ByteArray.size then  w \bits8 (j - i) else t.[j].
    proof. by rewrite /set'Sd filliEs. qed.

    lemma get'Sd_byte (t:t) (i k:int) :
      0 <= k < r =>
      get'Sd t i \bits8 k = t.[i+k].
    proof. by move=> hk; rewrite /get'Sd _nth_of_list 1:size_map 1:size_iota 1:lez_maxr 1:/# 2:nth_sub. qed.

    lemma get_set'SdE (t:t) (i:int) (w:B) j :
      get'Sd (set'Sd t i w) j =
      if j + r <= i \/ i + r <= j then get'Sd t j
      else
        _of_list
          (map (fun k => if i <= j + k < i + r /\ 0 <= j + k && j + k < ByteArray.size then
                            w \bits8 (j + k - i)
                         else t.[j + k])
             (iota_ 0 r)).
    proof.
      apply _wordP => k hk.
      rewrite get'Sd_byte 1:// get8_set'SdE.
      case: (j + r <= i \/ i + r <= j) => hj.
      + by rewrite get'Sd_byte 1:// /#.
      by rewrite _nth_of_list 1:size_map 1:size_iota 1:/# (nth_map 0) 1:size_iota 1:/# nth_iota.
    qed.

    lemma get_set'SE_eq t i j w:
      0 <= i => r*(i + 1) <= ByteArray.size =>
      i = j =>
      get'S (set'S t i w) j = w.
    proof.
      move=> hx hs <<-; rewrite get_set'SdE.
      have -> /= : !(r * i + r <= r * i \/ r * i + r <= r * i) by smt(_gt0_r).
      apply _wordP => k hk.
      by rewrite _nth_of_list 1:size_map 1:size_iota 1:/# (nth_map 0) 1:size_iota 1:/# /= nth_iota // /#.
    qed.

    lemma get_set'SE_neq t i j w:
      i <> j =>
      get'S (set'S t i w) j = get'S t j.
    proof.
      move=> hne; rewrite get_set'SdE.
      case: (r * j + r <= r * i \/ r * i + r <= r * j) => //.
      move=> /negb_or [] /ltrNge + /ltrNge.
      have [-> ->] : r * j + r = r * (j + 1) /\ r * i + r = r * (i + 1) by smt().
      move=> /(ltr_pmul2l _ _gt0_r) ? /(ltr_pmul2l _ _gt0_r) ? /#.
    qed.

    lemma get_set'SE t i j w:
      0 <= i => r*(i + 1) <= ByteArray.size =>
      get'S (set'S t i w) j = if i = j then w else get'S t j.
    proof.
      move=> hx hs.
      by case (i=j) => heq; [apply get_set'SE_eq | apply get_set'SE_neq].
    qed.

    lemma get_set'SdE_eq t i j w:
      0 <= i => i + r <= ByteArray.size =>
      i = j =>
      get'Sd (set'Sd t i w) j = w.
    proof.
      move=> h1 h2 <<-; rewrite get_set'SdE //.
      have -> /= : !(i + r <= i) by smt(_gt0_r).
      apply _wordP => k hk; rewrite _nth_of_list 1:size_map 1:size_iota 1:/# /=.
      rewrite (nth_map 0) 1:size_iota 1:/# /= nth_iota // /#.
    qed.

    lemma get_set'SdE_neq t i j w:
      (j + r <= i \/ i + r <= j) =>
      get'Sd (set'Sd t i w) j = get'Sd t j.
    proof. by move => h; rewrite get_set'SdE h. qed.

    hint simplify get_set'SdE_eq, get_set'SdE_neq.

    lemma ext_eq'S t1 t2:
        (forall x, 0 <= r*x < ByteArray.size => get'S t1 x = get'S t2 x) =>
        t1 = t2.
    proof.
    have ? := _gt0_r.
    move => E.
    apply ByteArray.ext_eq => x h.
    rewrite (divz_eq x r).
    rewrite !(-get'Sd_byte, modz_cmp, _gt0_r).
    rewrite mulzC E 2://.
    smt().
    qed.

    op of_list'S (l:B list) =
      init (fun i => if i < List.size l * r then nth _zero l (i%/r) \bits8 (i%%r) else W8.zero).

    lemma get8_of_list'S l i :
      (of_list'S l).[i] =
         if (0 <= i < ByteArray.size) /\ i < List.size l * r then nth _zero l (i%/r) \bits8 (i%%r) else W8.zero.
    proof.
      rewrite /of_list'S.
      case: (0 <= i && i < ByteArray.size) => hi; last by rewrite get_out.
      by rewrite initiE.
    qed.

    lemma get'S_of_list'S l i :
      List.size l * r = ByteArray.size =>
      get'S (of_list'S l) i = nth _zero l i.
    proof.
      move=> h; apply _wordP => k hk.
      rewrite get'Sd_byte // get8_of_list'S.
      rewrite (mulzC r i) edivz_eq 1:/# emodz_eq 1:/#.
      case: (0 <= i < List.size l) => hi.
      + have /# : (i + 1) * r <= size l * r by apply ler_wpmul2r => /#.
      rewrite nth_out 1:// _zero_bits8 /#.
    qed.

  end WSB.

  clone include WSB with
    type B <- W16.t,
    op r <- 2,
    op _zero <- W16.zero,
    op _of_list <- W2u8.pack2,
    op (\bits8) <- W2u8.(\bits8),
    axiom _gt0_r <- W2u8.gt0_r,
    axiom _nth_of_list <- W2u8.get_pack2,
    axiom _wordP <- W2u8.wordP,
    axiom _zero_bits8 <- W2u8.get_zero
  rename [op, lemma, theory] "'S" as "16".

  clone include WSB with
    type B <- W32.t,
    op r <- 4,
    op _zero <- W32.zero,
    op _of_list <- W4u8.pack4,
    op (\bits8) <- W4u8.(\bits8),
    axiom _gt0_r <- W4u8.gt0_r,
    axiom _nth_of_list <- W4u8.get_pack4,
    axiom _wordP <- W4u8.wordP,
    axiom _zero_bits8 <- W4u8.get_zero
  rename [op, lemma, theory] "'S" as "32".

  clone include WSB with
    type B <- W64.t,
    op r <- 8,
    op _zero <- W64.zero,
    op _of_list <- W8u8.pack8,
    op (\bits8) <- W8u8.(\bits8),
    axiom _gt0_r <- W8u8.gt0_r,
    axiom _nth_of_list <- W8u8.get_pack8,
    axiom _wordP <- W8u8.wordP,
    axiom _zero_bits8 <- W8u8.get_zero
  rename [op, lemma, theory] "'S" as "64".

  clone include WSB with
    type B <- W128.t,
    op r <- 16,
    op _zero <- W128.zero,
    op _of_list <- W16u8.pack16,
    op (\bits8) <- W16u8.(\bits8),
    axiom _gt0_r <- W16u8.gt0_r,
    axiom _nth_of_list <- W16u8.get_pack16,
    axiom _wordP <- W16u8.wordP,
    axiom _zero_bits8 <- W16u8.get_zero
  rename [op, lemma, theory] "'S" as "128".

  clone include WSB with
    type B <- W256.t,
    op r <- 32,
    op _zero <- W256.zero,
    op _of_list <- W32u8.pack32,
    op (\bits8) <- W32u8.(\bits8),
    axiom _gt0_r <- W32u8.gt0_r,
    axiom _nth_of_list <- W32u8.get_pack32,
    axiom _wordP <- W32u8.wordP,
    axiom _zero_bits8 <- W32u8.get_zero
  rename [op, lemma, theory] "'S" as "256".

end ByteArray.

abstract theory SubByteArray.

  clone ByteArray as Asmall.
  clone ByteArray as Abig.

  op get_sub (a: Abig.t) i : Asmall.t =
    Asmall.of_list (Abig.sub a i Asmall.size).

  op set_sub (a:Abig.t) (i:int) (s:Asmall.t) =
    Abig.fill (fun k => Asmall.get8 s (k - i)) i Asmall.size a.

  abbrev [-printing] get_sub8   a i = get_sub a       i.
  abbrev [-printing] get_sub16  a i = get_sub a ( 2 * i).
  abbrev [-printing] get_sub32  a i = get_sub a ( 4 * i).
  abbrev [-printing] get_sub64  a i = get_sub a ( 8 * i).
  abbrev [-printing] get_sub128 a i = get_sub a (16 * i).
  abbrev [-printing] get_sub256 a i = get_sub a (32 * i).

  abbrev [-printing] set_sub8   a i s = set_sub a       i  s.
  abbrev [-printing] set_sub16  a i s = set_sub a ( 2 * i) s.
  abbrev [-printing] set_sub32  a i s = set_sub a ( 4 * i) s.
  abbrev [-printing] set_sub64  a i s = set_sub a ( 8 * i) s.
  abbrev [-printing] set_sub128 a i s = set_sub a (16 * i) s.
  abbrev [-printing] set_sub256 a i s = set_sub a (32 * i) s.

  lemma get8_get_sub (a:Abig.t) i k :
    Asmall.get8 (get_sub a i) k =
     if (0 <= k < Asmall.size) then Abig.get8 a (i+k)
     else W8.zero.
  proof.
    rewrite /get_sub.
    case : (0 <= k && k < Asmall.size) => [hk | ?]; last by rewrite Asmall.get_out.
    by rewrite Asmall.get_of_list // Abig.nth_sub.
  qed.

  lemma get8_set_sub a i s k :
    Abig.get8 (set_sub a i s) k =
     if (i <= k < i + Asmall.size) /\ (0 <= k < Abig.size) then Asmall.get8 s (k - i)
     else Abig.get8 a k.
  proof. by rewrite Abig.filliEs. qed.

  abstract theory GETSUB.
    type B.
    op r : int.
    axiom gt0_r : 0 < r.
    op (\bits8) : B -> int -> W8.t.
    op small_get : Asmall.t -> int -> B.
    op big_get : Abig.t -> int -> B.
    axiom small_get_byte (t : Asmall.t) (i k : int) :
      0 <= k && k < r => small_get t i \bits8 k = Asmall.get8 t (i + k).
    axiom big_get_byte (t : Abig.t) (i k : int) :
      0 <= k && k < r => big_get t i \bits8 k = Abig.get8 t (i + k).
    axiom _wordP:
      forall (w1 w2 : B),
        (forall (i : int), 0 <= i && i < r => (w1 \bits8 i) = (w2 \bits8 i)) =>
      w1 = w2.

    lemma get'Sd_get_sub_byte (a:Abig.t) i k j :
      0 <= j < r =>
      (small_get (get_sub a i) k) \bits8 j =
      if 0 <= k + j && k + j < Asmall.size then Abig.get8 a (i + k + j)
      else W8.zero.
    proof. move=> hj; rewrite small_get_byte 1:// get8_get_sub /#. qed.

    lemma get'Sd_get_sub (a:Abig.t) i k :
      (0 <= k /\ k + r <= Asmall.size) =>
      small_get (get_sub a i) k = big_get a (i+k).
    proof.
      move=> hk; apply _wordP => j jh.
      rewrite get'Sd_get_sub_byte 1:// big_get_byte 1:// /#.
    qed.

    lemma get'Sd_set_sub_byte (a:Abig.t) (i k:int) s j :
      0 <= j < r =>
      big_get (set_sub a i s) k \bits8 j =
       if (i <= k + j < i + Asmall.size) /\ (0 <= k + j < Abig.size) then Asmall.get8 s (k + j - i)
       else Abig.get8 a (k + j).
    proof. by move=> hj; rewrite big_get_byte 1:// get8_set_sub. qed.

    lemma get'Sd_set_sub_in (a:Abig.t) (i k:int) s :
      (0 <= i /\ i + Asmall.size <= Abig.size) /\
      (0 <= k - i /\ k - i + r <= Asmall.size) =>
      big_get (set_sub a i s) k = small_get s (k - i).
    proof.
      move=> h; apply _wordP => j hj.
      rewrite get'Sd_set_sub_byte 1:// small_get_byte 1:// /#.
    qed.

    lemma get'Sd_set_sub_out (a:Abig.t) (i k:int) s :
      (0 <= i /\ i + Asmall.size <= Abig.size) /\
      (k + r <= i \/ i + Asmall.size <= k) =>
      big_get (set_sub a i s) k = big_get a k.
    proof.
      move=> h; apply _wordP => j hj.
      rewrite get'Sd_set_sub_byte 1:// big_get_byte 1:// /#.
    qed.

  end GETSUB.

  clone include GETSUB with
    type B <- W16.t,
    op r <- 2,
    axiom gt0_r <- W2u8.gt0_r,
    op (\bits8) <- W2u8.(\bits8),
    op small_get <- Asmall.get16d,
    op big_get <- Abig.get16d,
    axiom small_get_byte <- Asmall.get16d_byte,
    axiom big_get_byte <- Abig.get16d_byte,
    axiom _wordP <- W2u8.wordP
  rename [op, lemma] "'S" as "16".

  clone include GETSUB with
    type B <- W32.t,
    op r <- 4,
    axiom gt0_r <- W4u8.gt0_r,
    op (\bits8) <- W4u8.(\bits8),
    op small_get <- Asmall.get32d,
    op big_get <- Abig.get32d,
    axiom small_get_byte <- Asmall.get32d_byte,
    axiom big_get_byte <- Abig.get32d_byte,
    axiom _wordP <- W4u8.wordP
  rename [op, lemma] "'S" as "32".

  clone include GETSUB with
    type B <- W64.t,
    op r <- 8,
    axiom gt0_r <- W8u8.gt0_r,
    op (\bits8) <- W8u8.(\bits8),
    op small_get <- Asmall.get64d,
    op big_get <- Abig.get64d,
    axiom small_get_byte <- Asmall.get64d_byte,
    axiom big_get_byte <- Abig.get64d_byte,
    axiom _wordP <- W8u8.wordP
  rename [op, lemma] "'S" as "64".

  clone include GETSUB with
    type B <- W128.t,
    op r <- 16,
    axiom gt0_r <- W16u8.gt0_r,
    op (\bits8) <- W16u8.(\bits8),
    op small_get <- Asmall.get128d,
    op big_get <- Abig.get128d,
    axiom small_get_byte <- Asmall.get128d_byte,
    axiom big_get_byte <- Abig.get128d_byte,
    axiom _wordP <- W16u8.wordP
  rename [op, lemma] "'S" as "128".

  clone include GETSUB with
    type B <- W256.t,
    op r <- 32,
    axiom gt0_r <- W32u8.gt0_r,
    op (\bits8) <- W32u8.(\bits8),
    op small_get <- Asmall.get256d,
    op big_get <- Abig.get256d,
    axiom small_get_byte <- Asmall.get256d_byte,
    axiom big_get_byte <- Abig.get256d_byte,
    axiom _wordP <- W32u8.wordP
  rename [op, lemma] "'S" as "256".

end SubByteArray.





