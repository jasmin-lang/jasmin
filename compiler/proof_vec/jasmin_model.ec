(* -------------------------------------------------------------------- *)
require import AllCore BitEncoding IntDiv SmtMap List StdOrder.
(*---*) import CoreMap Map Ring.IntID IntOrder.

(* -------------------------------------------------------------------- *)
lemma powS_minus (x p:int) : 0 < p => x ^ p  = x * x ^ (p-1).
proof. smt (powS). qed.

hint simplify pow_le0.
hint simplify powS_minus@1.

lemma pow2_1 : 2^1 = 2   by [].
lemma pow2_2 : 2^2 = 4   by [].
lemma pow2_3 : 2^3 = 8   by [].
lemma pow2_4 : 2^4 = 16  by [].
lemma pow2_5 : 2^5 = 32  by [].
lemma pow2_6 : 2^6 = 64  by [].
lemma pow2_7 : 2^7 = 128 by [].
lemma pow2_8 : 2^8 = 256 by [].
lemma pow2_16 : 2^16 = 65536 by [].
lemma pow2_32 : 2 ^ 32 = 4294967296 by [].
lemma pow2_64 : 2 ^ 64 = 18446744073709551616 by [].
lemma pow2_128 : 2 ^ 128 = 340282366920938463463374607431768211456 by [].

hint simplify
  (pow2_1, pow2_2, pow2_3, pow2_4, pow2_5, pow2_6, pow2_7, pow2_8, pow2_16, pow2_32, pow2_64, pow2_128)@0.

(* -------------------------------------------------------------------- *)
lemma iotaS_minus :
  forall (i n : int), 0 < n => iota_ i n = i :: iota_ (i + 1) (n - 1).
proof. smt (iotaS). qed.

hint simplify (iota0, iotaS_minus)@0.

(* -------------------------------------------------------------------- *)
abstract theory W.
type t.

op size : { int | 0 < size } as size_gt0.

lemma size_ge0 : 0 <= size.
proof. by apply/ltrW/size_gt0. qed.

hint exact : size_gt0 size_ge0.

op of_uint : int -> t.
op to_uint : t -> int.

op of_sint : int -> t.
op to_sint : t -> int.

op mk   : bool list -> t.
op repr : t -> bool list.

op "_.[_]" (w : t) (i : int) =
  nth false (repr w) i.

lemma getE (w : t) (i : int) : w.[i] = nth false (repr w) i.
proof. by []. qed.

abbrev modulus = 2 ^ size.

op normed (x : bool list) = size x = size.

lemma normedP (w : bool list) :
  normed w <=> size w = size.
proof. by []. qed.

op norm (x : bool list) =
  take size x ++ nseq (max 0 (size - size x)) false.

axiom repr_normed (w : t) : normed (repr w).

lemma size_repr (w : t) : size (repr w) = size.
proof. by apply/repr_normed. qed.

lemma norm_normed (w : bool list) : normed w => norm w = w.
proof.
move/normedP=> sz_w; rewrite /norm sz_w subrr nseq0 cats0.
by rewrite take_oversize // sz_w.
qed.

lemma size_norm (x : bool list) : size (norm x) = size.
proof.
rewrite /norm size_cat size_take // maxC /max subr_lt0.
case: (size < size x) => h; first by rewrite nseq0.
by rewrite size_nseq maxC /max subr_lt0 h /= addrCA subrr.
qed.

axiom mkK   x : mk (repr x) = x.
axiom reprK x : repr (mk x) = norm x.

axiom of_uintK (x : int) : to_uint (of_uint x) = x %% modulus.
axiom to_uintK : cancel to_uint of_uint.

lemma to_uintK' (x: t) : of_uint (to_uint x) = x.
proof. by apply to_uintK. qed.

hint simplify (of_uintK, to_uintK')@0.

op blift1 (f : bool -> bool) (w : t) =
  mk (map f (repr w)).

op blift2 (f : bool -> bool -> bool) (w1 w2 : t) =
  mk (map (fun b : _ * _ => f b.`1 b.`2) (zip (repr w1) (repr w2))).

op ilift1 (f : int -> int) (w : t) =
  of_uint (f (to_uint w)).

op ilift2 (f : int -> int -> int) (w1 w2 : t) =
  of_uint (f (to_uint w1) (to_uint w2)).

lemma get_default (w : t) (i : int) :
  size <= i => w.[i] = false.
proof. by move=> gt; rewrite getE nth_default // size_repr. qed.

lemma get_neg (w : t) (i : int) : i < 0 => w.[i] = false.
proof. by move=> lt0; rewrite getE nth_neg. qed.

lemma mk_seqE (w : bool list) (i : int) :
  (mk w).[i] = (0 <= i < size /\ nth false w i).
proof.
rewrite getE reprK; case: (0 <= i) => /=; last first.
+ by move=> /ltrNge gt0_i; rewrite nth_neg.
move=> ge0_i; case: (i < size) => /=; last first.
+ by move=> /lerNgt ge_i_sz; rewrite nth_default ?size_norm.
move=> gt_i_sz; rewrite -{2}(cat_take_drop size w) /norm.
rewrite !nth_cat; case: (i < size (take size w)) => //.
move=> /lerNgt h; rewrite nth_nseq_if if_same; apply/eq_sym.
case: (size w <= size) => [ge_wsz|]; first by rewrite drop_oversize.
move=> /ltrNge lt_szw; move: h; rewrite size_takel.
+ by rewrite size_ge0 /= ltzW.
+ by move/(ltr_le_trans _ _ _ gt_i_sz).
qed.

lemma blift1E (f : bool -> bool) (w : t) (i : int) :
  (blift1 f w).[i] = (0 <= i < size /\ f w.[i]).
proof.
rewrite mk_seqE; apply/eq_iff/andb_id2l => h.
by rewrite getE; apply/nth_map; rewrite size_repr.
qed.

lemma blift2E (f : bool -> bool -> bool) (w1 w2: t) (i : int) :
  (blift2 f w1 w2).[i] = (0 <= i < size /\ f w1.[i] w2.[i]).
proof.
rewrite mk_seqE; apply/eq_iff/andb_id2l => h.
rewrite !getE (nth_map (false, false)).
+ by rewrite size_zip !size_repr.
by rewrite nth_zip ?size_repr.
qed. 

op zeros = mk (nseq size false) axiomatized by zerosE.
op ones  = mk (nseq size true ) axiomatized by onesE.

op ( + ) = ilift2 Int.( + ) axiomatized by addE.
op ( - ) = ilift2 Int.( - ) axiomatized by subE.
op ([-]) = ilift1 Int.([-]) axiomatized by oppE.
op ( * ) = ilift2 Int.( * ) axiomatized by mulE.

op (\udiv) : t -> t -> t.
op (\umod) : t -> t -> t.

op (\sdiv) : t -> t -> t.
op (\smod) : t -> t -> t.

op (`&`) = blift2 (/\) axiomatized by andE.
op (`|`) = blift2 (\/) axiomatized by orE.
op (`^`) = blift2 Logic.(^) axiomatized by xorE.

(* FIXME : check extraction *)
op (\sle) (x y : t) = (to_sint x) <= (to_sint x) axiomatized by wsleE.
op (\slt) (x y : t) = (to_sint x) <  (to_sint x) axiomatized by wsltE.
 
op (\ule) (x y : t) = (to_uint x) <= (to_uint x) axiomatized by wuleE.
op (\ult) (x y : t) = (to_uint x) <  (to_uint x) axiomatized by wultE.

op (`>>>`) (x : t) (i : int) =
  mk (mkseq (fun j => x.[j + (i %% size)]) size)
  axiomatized by wlsrE.

op (`<<<`) (x : t) (i : int) =
  mk (mkseq (fun j => x.[j - (i %% size)]) size)
  axiomatized by wlslE.

op addc : t -> t -> bool -> bool * t.
op mulu : t -> t -> t * t.

lemma bandE (w1 w2 : t) (i : int) :
  0 <= i < size => (w1 `&` w2).[i] = (w1.[i] /\ w2.[i]).
proof. by move=> szok; rewrite andE blift2E szok. qed.

lemma borE (w1 w2 : t) (i : int) :
  0 <= i < size => (w1 `|` w2).[i] = (w1.[i] \/ w2.[i]).
proof. by move=> szok; rewrite orE blift2E szok. qed.

lemma bxorE (w1 w2 : t) (i : int) :
  0 <= i < size => (w1 `^` w2).[i] = (w1.[i] ^ w2.[i]).
proof. by move=> szok; rewrite xorE blift2E szok. qed.

axiom xor_zero_l x : zeros `^` x = x.
axiom xor_zero_r x : x `^` zeros = x.

hint simplify (xor_zero_l, xor_zero_r).

op slice (i : int) (n : int) (w : t) =
  take n (drop i (repr w))
  axiomatized by sliceE.
end W.

(* -------------------------------------------------------------------- *)
theory W8.
  clone include W with op size = 8.

  op (`>>`) (w1 w2 : W8.t) = w1 `>>>` to_uint w2.
  op (`<<`) (w1 w2 : W8.t) = w1 `<<<` to_uint w2.
end W8.
export W8. 

(* -------------------------------------------------------------------- *)
theory W16.
  clone include W with op size = 16.

  op (`>>`) (w1 w2 : W16.t) = w1 `>>>` to_uint w2.
  op (`<<`) (w1 w2 : W16.t) = w1 `<<<` to_uint w2.
end W16. 
export W16. 

(* -------------------------------------------------------------------- *)
theory W32.
  clone include W with op size = 32.

  op (`>>`) (w1 : W32.t) (w2 : W8.t) = w1 `>>>` to_uint w2.
  op (`<<`) (w1 : W32.t) (w2 : W8.t) = w1 `<<<` to_uint w2.
end W32.
export W32. 

(* -------------------------------------------------------------------- *)
theory W64.
  clone include W with op size = 64.

  op (`>>`) (w1 : W64.t) (w2 : W8.t) = w1 `>>>` to_uint w2.
  op (`<<`) (w1 : W64.t) (w2 : W8.t) = w1 `<<<` to_uint w2.
end W64. 
export W64. 

(* -------------------------------------------------------------------- *)
theory W128.
  clone include W with op size = 128.

  op (`>>`) (w1 : W128.t) (w2 : W8.t) = w1 `>>>` to_uint w2.
  op (`<<`) (w1 : W128.t) (w2 : W8.t) = w1 `<<<` to_uint w2.
end W128. 
export W128. 

(* -------------------------------------------------------------------- *)
theory W256.
  clone include W with op size = 256.

  op (`>>`) (w1 : W256.t) (w2 : W8.t) = w1 `>>>` to_uint w2.
  op (`<<`) (w1 : W256.t) (w2 : W8.t) = w1 `<<<` to_uint w2.
end W256. 
export W256. 

hint simplify (W8.of_uintK, W8.to_uintK')@0.
hint simplify (W16.of_uintK, W16.to_uintK')@0.
hint simplify (W32.of_uintK, W32.to_uintK')@0.
hint simplify (W64.of_uintK, W64.to_uintK')@0.
hint simplify (W128.of_uintK, W128.to_uintK')@0.
hint simplify (W256.of_uintK, W256.to_uintK')@0.

(* -------------------------------------------------------------------- *)
theory W8List.
  abbrev "_.[_]" (w : W8.t list) (i : int) = nth W8.zeros w i.
end W8List.
export W8List.

(* -------------------------------------------------------------------- *)
op sigext_8_16  = fun x => W16.of_sint  (W8.to_sint x)
  axiomatized by sigext_8_16E.

op sigext_8_32  = fun x => W32.of_sint  (W8.to_sint x)
  axiomatized by sigext_8_32E.

op sigext_8_64  = fun x => W64.of_sint  (W8.to_sint x)
  axiomatized by sigext_8_64E.

op sigext_8_128 = fun x => W128.of_sint (W8.to_sint x)
  axiomatized by sigext_8_128E.

op sigext_8_256 = fun x => W256.of_sint (W8.to_sint x)
  axiomatized by sigext_8_256E.

(* -------------------------------------------------------------------- *)
op sigext_16_32  = fun x => W32.of_sint  (W16.to_sint x)
  axiomatized by sigext_16_32E.

op sigext_16_64  = fun x => W64.of_sint  (W16.to_sint x)
  axiomatized by sigext_16_64E.

op sigext_16_128 = fun x => W128.of_sint (W16.to_sint x)
  axiomatized by sigext_16_128E.

op sigext_16_256 = fun x => W256.of_sint (W16.to_sint x)
  axiomatized by sigext_16_256E.

(* -------------------------------------------------------------------- *)
op sigext_32_64  = fun x => W64.of_sint  (W32.to_sint x)
  axiomatized by sigext_32_64E.

op sigext_32_128 = fun x => W128.of_sint (W32.to_sint x)
  axiomatized by sigext_32_128E.

op sigext_32_256 = fun x => W256.of_sint (W32.to_sint x)
  axiomatized by sigext_32_256E.

(* -------------------------------------------------------------------- *)
op sigext_64_128 = fun x => W128.of_sint (W64.to_sint x)
  axiomatized by sigext_64_128E.

op sigext_64_256 = fun x => W256.of_sint (W64.to_sint x)
  axiomatized by sigext_64_256E.

(* -------------------------------------------------------------------- *)
op sigext_128_256 = fun x => W256.of_sint (W128.to_sint x)
  axiomatized by sigext_128_256E.

(* -------------------------------------------------------------------- *)
op zeroext_8_16  = fun x => W16.of_uint  (W8.to_uint x)
  axiomatized by zeroext_8_16E.

op zeroext_8_32  = fun x => W32.of_uint  (W8.to_uint x)
  axiomatized by zeroext_8_32E.

op zeroext_8_64  = fun x => W64.of_uint  (W8.to_uint x)
  axiomatized by zeroext_8_64E.

op zeroext_8_128 = fun x => W128.of_uint (W8.to_uint x)
  axiomatized by zeroext_8_128E.

op zeroext_8_256 = fun x => W256.of_uint (W8.to_uint x)
  axiomatized by zeroext_8_256E.

(* -------------------------------------------------------------------- *)
op zeroext_16_8   = fun x => W8.of_uint   (W16.to_uint x)
  axiomatized by zeroext_16_8E.

op zeroext_16_32  = fun x => W32.of_uint  (W16.to_uint x)
  axiomatized by zeroext_16_32E.

op zeroext_16_64  = fun x => W64.of_uint  (W16.to_uint x)
  axiomatized by zeroext_16_64E.

op zeroext_16_128 = fun x => W128.of_uint (W16.to_uint x)
  axiomatized by zeroext_16_128E.

op zeroext_16_256 = fun x => W256.of_uint (W16.to_uint x)
  axiomatized by zeroext_16_256E.

(* -------------------------------------------------------------------- *)
op zeroext_32_8   = fun x => W8.of_uint   (W32.to_uint x)
  axiomatized by zeroext_32_8E.

op zeroext_32_16  = fun x => W16.of_uint  (W32.to_uint x)
  axiomatized by zeroext_32_16E.

op zeroext_32_64  = fun x => W64.of_uint  (W32.to_uint x)
  axiomatized by zeroext_32_64E.

op zeroext_32_128 = fun x => W128.of_uint (W32.to_uint x)
  axiomatized by zeroext_32_128E.

op zeroext_32_256 = fun x => W256.of_uint (W32.to_uint x)
  axiomatized by zeroext_32_256E.

(* -------------------------------------------------------------------- *)
op zeroext_64_8   = fun x => W8.of_uint   (W64.to_uint x)
  axiomatized by zeroext_64_8E.

op zeroext_64_16  = fun x => W16.of_uint  (W64.to_uint x)
  axiomatized by zeroext_64_16E.

op zeroext_64_32  = fun x => W32.of_uint  (W64.to_uint x)
  axiomatized by zeroext_64_32E.

op zeroext_64_128 = fun x => W128.of_uint (W64.to_uint x)
  axiomatized by zeroext_64_128E.

op zeroext_64_256 = fun x => W256.of_uint (W64.to_uint x)
  axiomatized by zeroext_64_256E.

(* -------------------------------------------------------------------- *)
op zeroext_128_8   = fun x => W8.of_uint   (W128.to_uint x)
  axiomatized by zeroext_128_8E.

op zeroext_128_16  = fun x => W16.of_uint  (W128.to_uint x)
  axiomatized by zeroext_128_16E.

op zeroext_128_32  = fun x => W32.of_uint  (W128.to_uint x)
  axiomatized by zeroext_128_32E.

op zeroext_128_64  = fun x => W64.of_uint  (W128.to_uint x)
  axiomatized by zeroext_128_64E.

op zeroext_128_256 = fun x => W256.of_uint (W128.to_uint x)
  axiomatized by zeroext_128_256E.

(* -------------------------------------------------------------------- *)
op zeroext_256_8   = fun x => W8.of_uint   (W256.to_uint x)
  axiomatized by zeroext_256_8E.

op zeroext_256_16  = fun x => W16.of_uint  (W256.to_uint x)
  axiomatized by zeroext_256_16E.

op zeroext_256_32  = fun x => W32.of_uint  (W256.to_uint x)
  axiomatized by zeroext_256_32E.

op zeroext_256_64  = fun x => W64.of_uint  (W256.to_uint x)
  axiomatized by zeroext_256_64E.

op zeroext_256_128 = fun x => W128.of_uint (W256.to_uint x)
  axiomatized by zeroext_256_128E.

(* -------------------------------------------------------------------- *)
abbrev [-printing] u8_16  = zeroext_8_16.
abbrev [-printing] u8_32  = zeroext_8_32.
abbrev [-printing] u8_64  = zeroext_8_64.
abbrev [-printing] u8_128 = zeroext_8_128.
abbrev [-printing] u8_256 = zeroext_8_256.

abbrev [-printing]  u16_8 = zeroext_16_8.
abbrev [-printing]  u32_8 = zeroext_32_8.
abbrev [-printing]  u64_8 = zeroext_64_8.
abbrev [-printing] u128_8 = zeroext_128_8.
abbrev [-printing] u256_8 = zeroext_256_8.

(* -------------------------------------------------------------------- *)
op unpackW16 (w : W16.t) : W8.t list =
  map (fun i => u16_8 (w `>>>` (i * 8))) (range 0 2).

op unpackW32 (w : W32.t) : W8.t list =
  map (fun i => u32_8 (w `>>>` (i * 8))) (range 0 4).

op unpackW64 (w : W64.t) : W8.t list =
  map (fun i => u64_8 (w `>>>` (i * 8))) (range 0 8).

op unpackW128 (w : W128.t) : W8.t list =
  map (fun i => u128_8 (w `>>>` (i * 8))) (range 0 16).

op unpackW256 (w : W256.t) : W8.t list =
  map (fun i => u256_8 (w `>>>` (i * 8))) (range 0 32).

(* -------------------------------------------------------------------- *)
op packW16 (w : W8.t list) =
      (u8_16 w.[0] `<<<` (0 * 8))
  `^` (u8_16 w.[1] `<<<` (1 * 8)).

op packW32 (w : W8.t list) =
      (u8_32 w.[0] `<<<` (0 * 8))
  `^` (u8_32 w.[1] `<<<` (1 * 8))
  `^` (u8_32 w.[2] `<<<` (2 * 8))
  `^` (u8_32 w.[3] `<<<` (3 * 8)).

op packW64 (w : W8.t list) =
      (u8_64 w.[0] `<<<` 0 * 8)
  `^` (u8_64 w.[1] `<<<` 1 * 8)
  `^` (u8_64 w.[2] `<<<` 2 * 8)
  `^` (u8_64 w.[3] `<<<` 3 * 8)
  `^` (u8_64 w.[4] `<<<` 4 * 8)
  `^` (u8_64 w.[5] `<<<` 5 * 8)
  `^` (u8_64 w.[6] `<<<` 6 * 8)
  `^` (u8_64 w.[7] `<<<` 7 * 8).

op packW128 (w : W8.t list) =
      (u8_128 w.[ 0] `<<<`  0 * 8)
  `^` (u8_128 w.[ 1] `<<<`  1 * 8)
  `^` (u8_128 w.[ 2] `<<<`  2 * 8)
  `^` (u8_128 w.[ 3] `<<<`  3 * 8)
  `^` (u8_128 w.[ 4] `<<<`  4 * 8)
  `^` (u8_128 w.[ 5] `<<<`  5 * 8)
  `^` (u8_128 w.[ 6] `<<<`  6 * 8)
  `^` (u8_128 w.[ 7] `<<<`  7 * 8)
  `^` (u8_128 w.[ 8] `<<<`  8 * 8)
  `^` (u8_128 w.[ 9] `<<<`  9 * 8)
  `^` (u8_128 w.[10] `<<<` 10 * 8)
  `^` (u8_128 w.[11] `<<<` 11 * 8)
  `^` (u8_128 w.[12] `<<<` 12 * 8)
  `^` (u8_128 w.[13] `<<<` 13 * 8)
  `^` (u8_128 w.[14] `<<<` 14 * 8)
  `^` (u8_128 w.[15] `<<<` 15 * 8).

op packW256 (w : W8.t list) =
      (u8_256 w.[ 0] `<<<`  0 * 8)
  `^` (u8_256 w.[ 1] `<<<`  1 * 8)
  `^` (u8_256 w.[ 2] `<<<`  2 * 8)
  `^` (u8_256 w.[ 3] `<<<`  3 * 8)
  `^` (u8_256 w.[ 4] `<<<`  4 * 8)
  `^` (u8_256 w.[ 5] `<<<`  5 * 8)
  `^` (u8_256 w.[ 6] `<<<`  6 * 8)
  `^` (u8_256 w.[ 7] `<<<`  7 * 8)
  `^` (u8_256 w.[ 8] `<<<`  8 * 8)
  `^` (u8_256 w.[ 9] `<<<`  9 * 8)
  `^` (u8_256 w.[10] `<<<` 10 * 8)
  `^` (u8_256 w.[11] `<<<` 11 * 8)
  `^` (u8_256 w.[12] `<<<` 12 * 8)
  `^` (u8_256 w.[13] `<<<` 13 * 8)
  `^` (u8_256 w.[14] `<<<` 14 * 8)
  `^` (u8_256 w.[15] `<<<` 15 * 8)
  `^` (u8_256 w.[16] `<<<` 16 * 8)
  `^` (u8_256 w.[17] `<<<` 17 * 8)
  `^` (u8_256 w.[18] `<<<` 18 * 8)
  `^` (u8_256 w.[19] `<<<` 19 * 8)
  `^` (u8_256 w.[20] `<<<` 20 * 8)
  `^` (u8_256 w.[21] `<<<` 21 * 8)
  `^` (u8_256 w.[22] `<<<` 22 * 8)
  `^` (u8_256 w.[23] `<<<` 23 * 8)
  `^` (u8_256 w.[24] `<<<` 24 * 8)
  `^` (u8_256 w.[25] `<<<` 25 * 8)
  `^` (u8_256 w.[26] `<<<` 26 * 8)
  `^` (u8_256 w.[27] `<<<` 27 * 8)
  `^` (u8_256 w.[28] `<<<` 28 * 8)
  `^` (u8_256 w.[29] `<<<` 29 * 8)
  `^` (u8_256 w.[30] `<<<` 30 * 8)
  `^` (u8_256 w.[31] `<<<` 31 * 8).

(* -------------------------------------------------------------------- *)
type address = W64.t.

type global_mem_t = (address, W8.t) map.

op loads (m : global_mem_t) (a : address) (l : int) =
  map (fun i => m.[a + W64.of_uint i]) (range 0 l).

op stores (m : global_mem_t) (a : address) (w : W8.t list) =
  foldl (fun (m:global_mem_t) i => m.[a + W64.of_uint i <- w.[i]]) m (range 0 (size w)).

op loadW8   (m : global_mem_t) (a : address) = m.[a]                   axiomatized by loadW8E.
op loadW16  (m : global_mem_t) (a : address) = packW16  (loads m a  2) axiomatized by loadW16E.
op loadW32  (m : global_mem_t) (a : address) = packW32  (loads m a  4) axiomatized by loadW32E.
op loadW64  (m : global_mem_t) (a : address) = packW64  (loads m a  8) axiomatized by loadW64E.
op loadW128 (m : global_mem_t) (a : address) = packW128 (loads m a 16) axiomatized by loadW128E.
op loadW256 (m : global_mem_t) (a : address) = packW256 (loads m a 32) axiomatized by loadW256E.

op storeW8 (m : global_mem_t) (a : address) (w : W8.t) =
  m.[a <- w]
axiomatized by storeW8E.

op storeW16 (m : global_mem_t) (a : address) (w : W16.t) =
  stores m a (unpackW16 w)
axiomatized by storeW16E.

op storeW32 (m : global_mem_t) (a : address) (w : W32.t) =
  stores m a (unpackW32 w)
axiomatized by storeW32E.

op storeW64 (m : global_mem_t) (a : address) (w : W64.t) =
  stores m a (unpackW64 w)
axiomatized by storeW64E.

op storeW128 (m : global_mem_t) (a : address) (w : W128.t) =
  stores m a (unpackW128 w)
axiomatized by storeW128E.

op storeW256 (m : global_mem_t) (a : address) (w : W256.t) =
  stores m a (unpackW256 w)
axiomatized by storeW256E.

(* ------------------------------------------------------------------- *)
(* Global Memory                                                       *)

module Glob = {
  var mem : global_mem_t
}.

(* -------------------------------------------------------------------- *)
type p4u32 = W32.t * W32.t * W32.t * W32.t.

op unpack_4u32 (w : W128.t) : p4u32 =
  (W32.mk (W128.slice  0 32 w), 
   W32.mk (W128.slice 32 32 w),
   W32.mk (W128.slice 64 32 w),
   W32.mk (W128.slice 96 32 w) )
  axiomatized by unpack_4u32_E.

op pack_4u32 (w : p4u32) : W128.t =
  W128.mk (W32.repr w.`1 ++ W32.repr w.`2 ++ W32.repr w.`3 ++ W32.repr w.`4)
  axiomatized by pack_4u32_E.

axiom pack_unpack_4u32 w : pack_4u32 (unpack_4u32 w) = w.

axiom unpack_pack_4u32 w : 
  unpack_4u32 (pack_4u32 w) = w.

hint simplify (pack_unpack_4u32, unpack_pack_4u32)@0.

op map_4u32 (f : W32.t -> W32.t) (w : p4u32) : p4u32 =
  (f w.`1, f w.`2, f w.`3, f w.`4).

op map2_4u32 (f : W32.t -> W32.t -> W32.t) (w1 w2:p4u32) : p4u32 = 
  (f w1.`1 w2.`1, f w1.`2 w2.`2, f w1.`3 w2.`3, f w1.`4 w2.`4).

axiom VPAND_128_32 (w1 w2 : p4u32):
  (pack_4u32 w1 `&` pack_4u32 w2) = 
  pack_4u32 (map2_4u32 W32.(`&`) w1 w2).

axiom VPOR_128_32 (w1 w2 : p4u32):
  (pack_4u32 w1 `|` pack_4u32 w2) = 
  pack_4u32 (map2_4u32 W32.(`|`) w1 w2).

axiom VPXOR_128_32 (w1 w2 : p4u32):
  (pack_4u32 w1 `^` pack_4u32 w2) = 
  pack_4u32 (map2_4u32 W32.(`^`) w1 w2).

hint simplify (VPAND_128_32, VPOR_128_32, VPXOR_128_32)@0.

(* -------------------------------------------------------------------- *)
op x86_MOVD_32 (x : W32.t) =
  pack_4u32 (x, W32.zeros, W32.zeros, W32.zeros).

(* FIXME cnt should be unsigned int mod 32 *)
op x86_ROL_32 (x : W32.t) (cnt : W8.t) =
  let result = rot (to_uint cnt) (repr x) in
  let CF = last true result in
  let OF = Logic.(^) CF (head true result) in
  (CF, OF, W32.mk result)
  axiomatized by x86_ROL_32_E.

(* -------------------------------------------------------------------- *)
op x86_SHLD_32 :
  W32.t -> W32.t -> W8.t -> (bool * bool * bool * bool * bool * W32.t).

op x86_SHRD_32 :
  W32.t -> W32.t -> W8.t -> (bool * bool * bool * bool * bool * W32.t).

op x86_SHLD_64 :
  W64.t -> W64.t -> W8.t -> (bool * bool * bool * bool * bool * W64.t).

op x86_SHRD_64 :
  W64.t -> W64.t -> W8.t -> (bool * bool * bool * bool * bool * W64.t).

(* -------------------------------------------------------------------- *)
op x86_VPSLL_4u32 (w : W128.t) (cnt : W8.t) =
  let f = fun w : W32.t => w `<<` cnt in
  pack_4u32 (map_4u32 f (unpack_4u32 w)).

op x86_VPSRL_4u32 (w : W128.t) (cnt : W8.t) =
  let f = fun w : W32.t => w `>>` cnt in
  pack_4u32 (map_4u32 f (unpack_4u32 w)).

(* -------------------------------------------------------------------- *)
type p16u8 = W8.t * W8.t * W8.t * W8.t * W8.t * W8.t * W8.t * W8.t *
             W8.t * W8.t * W8.t * W8.t * W8.t * W8.t * W8.t * W8.t.

op unpack_16u8 (w : W128.t) : p16u8 =
  (W8.mk (W128.slice 0 8 w),
   W8.mk (W128.slice 8 8 w),
   W8.mk (W128.slice 16 8 w),
   W8.mk (W128.slice 24 8 w),
   W8.mk (W128.slice 32 8 w),
   W8.mk (W128.slice 40 8 w),
   W8.mk (W128.slice 48 8 w),
   W8.mk (W128.slice 56 8 w),
   W8.mk (W128.slice 64 8 w),
   W8.mk (W128.slice 72 8 w),
   W8.mk (W128.slice 80 8 w),
   W8.mk (W128.slice 88 8 w),
   W8.mk (W128.slice 96 8 w),
   W8.mk (W128.slice 104 8 w),
   W8.mk (W128.slice 112 8 w),
   W8.mk (W128.slice 120 8 w))
  axiomatized by unpack_16u8_E.

op p16u8_l (w:p16u8) = 
   [ w.`1; w.`2; w.`3; w.`4; w.`5; w.`6; w.`7; w.`8;
     w.`9;  w.`10; w.`11; w.`12; w.`13; w.`14; w.`15; w.`16 ].

op pack_16u8 (w : p16u8) : W128.t =
  W128.mk (List.flatten (List.map W8.repr (p16u8_l w)))
  axiomatized by pack_16u8_E.

axiom pack_unpack_16u8 w : pack_16u8 (unpack_16u8 w) = w.

axiom unpack_pack_16u8 w : 
  unpack_16u8 (pack_16u8 w) = w.

hint simplify pack_unpack_16u8.
hint simplify unpack_pack_16u8.

op map_16u8 (f : W8.t -> W8.t) (w : p16u8) : p16u8 =
  ( f w.`1, f w.`2, f w.`3, f w.`4, f w.`5, f w.`6, f w.`7, f w.`8,
    f w.`9, f w.`10, f w.`11, f w.`12, f w.`13, f w.`14, f w.`15, f w.`16 ).

op map2_16u8 (f : W8.t -> W8.t -> W8.t) (w1 w2 : p16u8) : p16u8 =
  ( f w1.`1  w2.`1 , 
    f w1.`2  w2.`2 , 
    f w1.`3  w2.`3 , 
    f w1.`4  w2.`4 , 
    f w1.`5  w2.`5 , 
    f w1.`6  w2.`6 , 
    f w1.`7  w2.`7 , 
    f w1.`8  w2.`8 ,
    f w1.`9  w2.`9 , 
    f w1.`10 w2.`10, 
    f w1.`11 w2.`11, 
    f w1.`12 w2.`12, 
    f w1.`13 w2.`13, 
    f w1.`14 w2.`14, 
    f w1.`15 w2.`15, 
    f w1.`16 w2.`16 ).

op x86_VPSHUFB_128_B (w:W8.t list) (m : W8.t) =
  let i = W8.to_uint m in
  if 128 <= i then W8.zeros 
  else
    let i = i %% 16 in
    nth W8.zeros w i.
    
op x86_VPSHUFB_128 (w m : W128.t) : W128.t =
  let w = p16u8_l (unpack_16u8 w) in
  let m = unpack_16u8 m in
  pack_16u8 (map_16u8 (x86_VPSHUFB_128_B w) m).

axiom VPAND_128_8 (w1 w2 : p16u8):
  (pack_16u8 w1 `&` pack_16u8 w2) = 
  pack_16u8 (map2_16u8 W8.(`&`) w1 w2).

axiom VPOR_128_8 (w1 w2 : p16u8):
  (pack_16u8 w1 `|` pack_16u8 w2) = 
  pack_16u8 (map2_16u8 W8.(`|`) w1 w2).

axiom VPXOR_128_8 (w1 w2 : p16u8):
  (pack_16u8 w1 `^` pack_16u8 w2) = 
  pack_16u8 (map2_16u8 W8.(`^`) w1 w2).

hint simplify VPAND_128_8.
hint simplify VPOR_128_8.
hint simplify VPXOR_128_8.

(* -------------------------------------------------------------------- *)
op x86_VPSHUFD_128_B (w : W32.t list) (m : W8.t) (i : int) : W32.t =
  let m = W8.to_uint m in
  let p = (m %/ (2^(2*i)))%%4 in
  nth W32.zeros w p.

op p4u32_l (w:p4u32) = [w.`1; w.`2; w.`3; w.`4].

op x86_VPSHUFD_128 (w : W128.t) (m : W8.t) : W128.t =
  let w = p4u32_l (unpack_4u32 w) in
  pack_4u32 (x86_VPSHUFD_128_B w m 0,
             x86_VPSHUFD_128_B w m 1,
             x86_VPSHUFD_128_B w m 2,
             x86_VPSHUFD_128_B w m 3).

(* -------------------------------------------------------------------- *)
type p2u32 = W32.t * W32.t.

op unpack_2u32 (w:W64.t) = 
  ( W32.mk (W64.slice 0 32 w), 
    W32.mk (W64.slice 32 32 w) )
  axiomatized by unpack_2u32_E.

op pack_2u32 (w:p2u32) = 
  W64.mk (W32.repr w.`1 ++ W32.repr w.`2)
  axiomatized by pack_2u32_E.

axiom pack_unpack_2u32 w : pack_2u32 (unpack_2u32 w) = w.
axiom unpack_pack_2u32 w : unpack_2u32 (pack_2u32 w) = w.

hint simplify (pack_unpack_2u32, unpack_pack_2u32)@0.

op mulu_64 (w1 w2 : W64.t) = 
  let p1 = unpack_2u32 w1 in
  let p2 = unpack_2u32 w2 in
  pack_2u32 (W32.mulu p1.`1 p2.`1). 
 
(* -------------------------------------------------------------------- *)
type p2u64 = W64.t * W64.t.

op unpack_2u64 (w : W128.t) : p2u64 =
  ( W64.mk (W128.slice 0 64 w),
    W64.mk (W128.slice 64 64 w) )
  axiomatized by unpack_2u64_E. 

op pack_2u64 (w : p2u64) : W128.t =
  W128.mk (W64.repr w.`1 ++ W64.repr w.`2)
  axiomatized by pack_2u64_E. 

axiom pack_unpack_2u64 w : pack_2u64 (unpack_2u64 w) = w.
axiom unpack_pack_2u64 w : unpack_2u64 (pack_2u64 w) = w.

hint simplify (pack_unpack_2u64, unpack_pack_2u64)@0.

op map_2u64 (f : W64.t -> W64.t) (w : p2u64) : p2u64 =
  (f w.`1, f w.`2).

op map2_2u64 (f : W64.t -> W64.t -> W64.t) (w1 w2 : p2u64) : p2u64 =
  (f w1.`1 w2.`1, f w1.`2 w2.`2).

op x86_VPADD_2u64 (w1 : W128.t) (w2:W128.t) = 
   pack_2u64 (map2_2u64 W64.(+) (unpack_2u64 w1) (unpack_2u64 w2)).

op x86_VPEXTR_64 (w:W128.t) (i:W8.t) = 
  let p = unpack_2u64 w in
  if W8.to_uint i = 0 then p.`1 
  else if W8.to_uint i = 1 then p.`2 
  else W64.of_uint 0.

op x86_VPINSR_2u64 (v1:W128.t) (v2:W64.t) (i:W8.t) = 
  let p = unpack_2u64 v1 in
  if W8.to_uint i = 0 then pack_2u64 (v2, p.`2)
  else if W8.to_uint i = 1 then pack_2u64 (p.`1, v2)
  else v1.

op x86_MOVD_64 (v:W64.t) = 
  pack_2u64 (v, W64.zeros). 

op x86_VPUNPCKL_2u64 (w1 w2: W128.t) = 
  let p1 = unpack_2u64 w1 in
  let p2 = unpack_2u64 w2 in
  pack_2u64 (p1.`1, p2.`1).

op x86_VPUNPCKH_2u64 (w1 w2: W128.t) = 
  let p1 = unpack_2u64 w1 in
  let p2 = unpack_2u64 w2 in
  pack_2u64 (p1.`2, p2.`2).

op x86_VPSLL_2u64 (w:W128.t) (cnt:W8.t) = 
  let f = fun w : W64.t => w `<<`  cnt in
  pack_2u64 (map_2u64 f (unpack_2u64 w)).

op x86_VPSRL_2u64 (w:W128.t) (cnt:W8.t) = 
  let f = fun w : W64.t => w `>>` cnt in
  pack_2u64 (map_2u64 f (unpack_2u64 w)).

op x86_VPAND_128 = W128.(`&`).
op x86_VPOR_128 = W128.(`|`).

op x86_VPMULU_128 (w1 w2: W128.t) = 
  pack_2u64 (map2_2u64 mulu_64 (unpack_2u64 w1) (unpack_2u64 w2)).


axiom VPAND_128_64 w1 w2:
  pack_2u64 w1 `&` pack_2u64 w2 = 
  pack_2u64(w1.`1 `&` w2.`1, w1.`2 `&` w2.`2).

axiom VPOR_128_64 w1 w2:
  pack_2u64 w1 `|` pack_2u64 w2 = 
  pack_2u64(w1.`1 `|` w2.`1, w1.`2 `|` w2.`2).

axiom VPXOR_128_64 w1 w2:
  pack_2u64 w1 `^` pack_2u64 w2 = 
  pack_2u64(w1.`1 `^` w2.`1, w1.`2 `^` w2.`2).

hint simplify (VPAND_128_64, VPOR_128_64, VPXOR_128_64)@0.

(*-------------------------------------------------------------------- *)

abstract theory Array.

  op size: int.

  type 'a t.

  op init : 'a -> 'a t.

  op "_.[_]" ['a] : 'a t -> int -> 'a.

  op "_.[_<-_]" ['a] : 'a t -> int -> 'a -> 'a t.

  op map ['a 'b] : ('a -> 'b) -> 'a t -> 'b t.

  axiom get_setE ['a] (t:'a t) (x y:int) (a:'a) :
    0 <= x < size => t.[x<-a].[y] = if y = x then a else t.[y].

  lemma nosmt get_set_eqE (t : 'a t) x y a :
    0 <= x < size => y = x => t.[x <- a].[y] = a.
  proof. by move=> h1 ->; rewrite get_setE. qed.

  lemma nosmt get_set_neqE (t : 'a t) x y a :
    0 <= x < size => y <> x => t.[x <- a].[y] = t.[y].
  proof. by move=> h1; rewrite get_setE // => ->. qed.

  axiom ext_eq (t1 t2: 'a t) : 
    (forall x, 0 <= x < size => t1.[x] = t2.[x]) => 
    t1 = t2.

  op all_eq (t1 t2: 'a t) =
    all (fun x => t1.[x] = t2.[x]) (range 0 size).

  lemma ext_eq_all (t1 t2: 'a t) : 
    all_eq t1 t2 <=> t1 = t2.
  proof. 
    split.
    + by move=> /allP h; apply ext_eq => x /mem_range; apply h. 
    by move=> ->;apply /allP.
  qed.
  
  axiom mapE (f:'a -> 'b) (t:'a t) i : 0 <= i < size => (map f t).[i] = f (t.[i]).

  op is_init (t: 'a option t) = 
    all (fun i => t.[i] <> None) (range 0 size).

  hint simplify (get_set_eqE, get_set_neqE, mapE).
end Array.

clone export Array as Array0  with op size <- 0.
clone export Array as Array1  with op size <- 1.
clone export Array as Array2  with op size <- 2.
clone export Array as Array3  with op size <- 3.
clone export Array as Array4  with op size <- 4.
clone export Array as Array5  with op size <- 5.
clone export Array as Array6  with op size <- 6.
clone export Array as Array7  with op size <- 7.
clone export Array as Array8  with op size <- 8.
clone export Array as Array9  with op size <- 9.
clone export Array as Array10  with op size <- 10.
clone export Array as Array11  with op size <- 11.
clone export Array as Array12  with op size <- 12.
clone export Array as Array13  with op size <- 13.
clone export Array as Array14  with op size <- 14.
clone export Array as Array15  with op size <- 15.
clone export Array as Array16  with op size <- 16.
clone export Array as Array17  with op size <- 17.
clone export Array as Array18  with op size <- 18.
clone export Array as Array19  with op size <- 19.
clone export Array as Array20  with op size <- 20.
clone export Array as Array21  with op size <- 21.
clone export Array as Array22  with op size <- 22.
clone export Array as Array23  with op size <- 23.
clone export Array as Array24  with op size <- 24.
clone export Array as Array25  with op size <- 25.
clone export Array as Array26  with op size <- 26.
clone export Array as Array27  with op size <- 27.
clone export Array as Array28  with op size <- 28.
clone export Array as Array29  with op size <- 29.

hint simplify (Array0.get_set_eqE, Array0.get_set_neqE, Array0.mapE)@0.
hint simplify (Array1.get_set_eqE, Array1.get_set_neqE, Array1.mapE)@0.
hint simplify (Array2.get_set_eqE, Array2.get_set_neqE, Array2.mapE)@0.
hint simplify (Array3.get_set_eqE, Array3.get_set_neqE, Array3.mapE)@0.
hint simplify (Array4.get_set_eqE, Array4.get_set_neqE, Array4.mapE)@0.
hint simplify (Array5.get_set_eqE, Array5.get_set_neqE, Array5.mapE)@0.
hint simplify (Array6.get_set_eqE, Array6.get_set_neqE, Array6.mapE)@0.
hint simplify (Array7.get_set_eqE, Array7.get_set_neqE, Array7.mapE)@0.
hint simplify (Array8.get_set_eqE, Array8.get_set_neqE, Array8.mapE)@0.
hint simplify (Array9.get_set_eqE, Array9.get_set_neqE, Array9.mapE)@0.
hint simplify (Array10.get_set_eqE, Array10.get_set_neqE, Array10.mapE)@0.
hint simplify (Array11.get_set_eqE, Array11.get_set_neqE, Array11.mapE)@0.
hint simplify (Array12.get_set_eqE, Array12.get_set_neqE, Array12.mapE)@0.
hint simplify (Array13.get_set_eqE, Array13.get_set_neqE, Array13.mapE)@0.
hint simplify (Array14.get_set_eqE, Array14.get_set_neqE, Array14.mapE)@0.
hint simplify (Array15.get_set_eqE, Array15.get_set_neqE, Array15.mapE)@0.
hint simplify (Array16.get_set_eqE, Array16.get_set_neqE, Array16.mapE)@0.
hint simplify (Array17.get_set_eqE, Array17.get_set_neqE, Array17.mapE)@0.
hint simplify (Array18.get_set_eqE, Array18.get_set_neqE, Array18.mapE)@0.
hint simplify (Array19.get_set_eqE, Array19.get_set_neqE, Array19.mapE)@0.
hint simplify (Array20.get_set_eqE, Array20.get_set_neqE, Array20.mapE)@0.
hint simplify (Array21.get_set_eqE, Array21.get_set_neqE, Array21.mapE)@0.
hint simplify (Array22.get_set_eqE, Array22.get_set_neqE, Array22.mapE)@0.
hint simplify (Array23.get_set_eqE, Array23.get_set_neqE, Array23.mapE)@0.
hint simplify (Array24.get_set_eqE, Array24.get_set_neqE, Array24.mapE)@0.
hint simplify (Array25.get_set_eqE, Array25.get_set_neqE, Array25.mapE)@0.
hint simplify (Array26.get_set_eqE, Array26.get_set_neqE, Array26.mapE)@0.
hint simplify (Array27.get_set_eqE, Array27.get_set_neqE, Array27.mapE)@0.
hint simplify (Array28.get_set_eqE, Array28.get_set_neqE, Array28.mapE)@0.
hint simplify (Array29.get_set_eqE, Array29.get_set_neqE, Array29.mapE)@0.

(* ------------------------------------------------------------------- *)
(* Leakages                                                            *)

type leakage_t = [
  | LeakExpr of W64.t list
  | LeakCond of bool
  | LeakFor  of (int * int)
].

type leakages_t = leakage_t list.

(* ------------------------------------------------------------------- *)
(* Safety                                                              *)

op is_init (x : 'a option) = x <> None.
op in_bound (x n:int) = 0 <= x /\ x < n.

type wsize = [
  | W8
  | W16
  | W32
  | W64
  | W128
  | W256
].

(* FIXME : define this *)
op is_valid (m:global_mem_t) (p:W64.t) (ws:wsize) : bool.




 



 

  

