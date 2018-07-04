require import AllCore BitEncoding IntDiv SmtMap List StdOrder.
(*---*) import CoreMap Map Ring.IntID IntOrder.

lemma powS_minus (x p:int) : 1 <= p => x ^ p  = x * x ^ (p-1).
proof. smt (powS). qed.

hint simplify pow_le0.
hint simplify powS_minus@1.

lemma pow2_1 : 2^1 = 2.
proof. by move=> /=. qed.
lemma pow2_2 : 2^2 = 4.
proof. by move=> /=. qed.
lemma pow2_3 : 2^3 = 8.
proof. by move=> /=. qed.
lemma pow2_4 : 2^4 = 16.
proof. by move=> /=. qed.
lemma pow2_5 : 2^5 = 32.
proof. by move=> /=. qed.
lemma pow2_6 : 2^6 = 64.
proof. by move=> /=. qed.
lemma pow2_7 : 2^7 = 128.
proof. by move=> /=. qed.
lemma pow2_8 : 2^8 = 256.
proof. by move=> /=. qed.

hint simplify (pow2_1, pow2_2, pow2_3, pow2_4, pow2_5, pow2_6, pow2_7, pow2_8)@0.


(*sopn_tin, sopn_tout*)
abstract theory W.

type t.

op size : { int | 0 < size } as size_gt0.

lemma size_ge0 : 0 <= size.
proof. by apply/ltrW/size_gt0. qed.

hint exact : size_gt0 size_ge0.

op of_int : int -> t.
op to_sint : t -> int.
op to_uint : t -> int.

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

axiom of_uintK (x : int) : to_uint (of_int x) = x %% modulus.
axiom to_uintK : cancel to_uint of_int.
lemma to_uintK' (x: t) : of_int (to_uint x) = x.
proof. apply to_uintK. qed.

hint simplify of_uintK.
hint simplify to_uintK'.

op blift1 (f : bool -> bool) (w : t) =
  mk (map f (repr w)).

op blift2 (f : bool -> bool -> bool) (w1 w2 : t) =
  mk (map (fun b : _ * _ => f b.`1 b.`2) (zip (repr w1) (repr w2))).

op ilift1 (f : int -> int) (w : t) =
  of_int (f (to_uint w)).

op ilift2 (f : int -> int -> int) (w1 w2 : t) =
  of_int (f (to_uint w1) (to_uint w2)).

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

op (`&`) = blift2 (/\) axiomatized by andE.
op (`|`) = blift2 (\/) axiomatized by orE.
op (`^`) = blift2 Logic.(^) axiomatized by xorE.

(* FIXME : check extraction *)
op (`<=`) (x y : t) = (to_sint x) <= (to_sint x) axiomatized by wsleE.
op (`<` ) (x y : t) = (to_sint x) <  (to_sint x) axiomatized by wsltE.
 
op (\ule) (x y : t) = (to_uint x) <= (to_uint x) axiomatized by wuleE.
op (\ult) (x y : t) = (to_uint x) <  (to_uint x) axiomatized by wultE.

op (`>>>`) (x : t) (i : int) =
  mk (mkseq (fun j => x.[j + i]) size)
  axiomatized by wlsrE.

op (`<<<`) (x : t) (i : int) =
  mk (mkseq (fun j => x.[j - i]) size)
  axiomatized by wlslE.

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

op slice (i : int) (n : int) (w : t) =
  take n (drop i (repr w))
  axiomatized by sliceE.

end W.

(* example below *)

theory W8.
  clone include W with op size = 8.

  op (`>>`) : t -> t -> t.
  op (`<<`) : t -> t -> t.

  op addc_8: t -> t -> bool -> (bool * t).
end W8.
export W8. 

hint simplify (W8.of_uintK, W8.to_uintK')@0.
 
theory W16.
  clone include W with op size = 16.

  op (`>>`) : t -> W8.t -> t.
  op (`<<`) : t -> W8.t -> t.

  op addc_16: t -> t -> bool -> (bool * t).
end W16. 
export W16.

theory W32.
  clone include W with op size = 32.

  op (`>>`) : t -> W8.t -> t.
  op (`<<`) : t -> W8.t -> t.

  op mulu_32   : t -> t -> (t * t). (* low bits first *)
  op addc_32: t -> t -> bool -> (bool * t).
end W32.
export W32.

theory W64.
  clone include W with op size = 64.

  op (`>>`) : t -> W8.t -> t.
  op (`<<`) : t -> W8.t -> t.

  op mulu_64: t -> t -> (t*t). (* low bits first *)
  op addc_64: t -> t -> bool -> (bool * t).
end W64. 
export W64.

theory W128.
  clone include W with op size = 128.

  op (`>>`) : t -> W8.t -> t.
  op (`<<`) : t -> W8.t -> t.

  op addc_128: t -> t -> bool -> (bool * t).
end W128. 
export W128.

theory W256.
  clone include W with op size = 256.

  op (`>>`) : t -> W8.t -> t.
  op (`<<`) : t -> W8.t -> t.

  op addc_256: t -> t -> bool -> (bool * t).
  op cast_32: t -> W32.t.
end W256. 
export W256.

op sigext_8_8:   W8.t -> W8.t.
op sigext_8_16:  W8.t -> W16.t.
op sigext_8_32:  W8.t -> W32.t.
op sigext_8_64:  W8.t -> W64.t.
op sigext_8_128: W8.t -> W128.t.
op sigext_8_256: W8.t -> W256.t.

op sigext_16_8:   W16.t -> W8.t.
op sigext_16_16:  W16.t -> W16.t.
op sigext_16_32:  W16.t -> W32.t.
op sigext_16_64:  W16.t -> W64.t.
op sigext_16_128: W16.t -> W128.t.
op sigext_16_256: W16.t -> W256.t.

op sigext_32_8:   W32.t -> W8.t.
op sigext_32_16:  W32.t -> W16.t.
op sigext_32_32:  W32.t -> W32.t.
op sigext_32_64:  W32.t -> W64.t.
op sigext_32_128: W32.t -> W128.t.
op sigext_32_256: W32.t -> W256.t.

op sigext_64_8:   W64.t -> W8.t.
op sigext_64_16:  W64.t -> W16.t.
op sigext_64_32:  W64.t -> W32.t.
op sigext_64_64:  W64.t -> W64.t.
op sigext_64_128: W64.t -> W128.t.
op sigext_64_256: W64.t -> W256.t.

op sigext_128_8:   W128.t -> W8.t.
op sigext_128_16:  W128.t -> W16.t.
op sigext_128_32:  W128.t -> W32.t.
op sigext_128_64:  W128.t -> W64.t.
op sigext_128_128: W128.t -> W128.t.
op sigext_128_256: W128.t -> W256.t.

op sigext_256_8:   W256.t -> W8.t.
op sigext_256_16:  W256.t -> W16.t.
op sigext_256_32:  W256.t -> W32.t.
op sigext_256_64:  W256.t -> W64.t.
op sigext_256_128: W256.t -> W128.t.
op sigext_256_256: W256.t -> W256.t.

op zeroext_8_8:   W8.t -> W8.t.
op zeroext_8_16:  W8.t -> W16.t.
op zeroext_8_32:  W8.t -> W32.t.
op zeroext_8_64:  W8.t -> W64.t.
op zeroext_8_128: W8.t -> W128.t.
op zeroext_8_256: W8.t -> W256.t.

op zeroext_16_8:   W16.t -> W8.t.
op zeroext_16_16:  W16.t -> W16.t.
op zeroext_16_32:  W16.t -> W32.t.
op zeroext_16_64:  W16.t -> W64.t.
op zeroext_16_128: W16.t -> W128.t.
op zeroext_16_256: W16.t -> W256.t.

op zeroext_32_8:   W32.t -> W8.t.
op zeroext_32_16:  W32.t -> W16.t.
op zeroext_32_32:  W32.t -> W32.t.
op zeroext_32_64:  W32.t -> W64.t.
op zeroext_32_128: W32.t -> W128.t.
op zeroext_32_256: W32.t -> W256.t.

op zeroext_64_8:   W64.t -> W8.t.
op zeroext_64_16:  W64.t -> W16.t.
op zeroext_64_32:  W64.t -> W32.t.
op zeroext_64_64:  W64.t -> W64.t.
op zeroext_64_128: W64.t -> W128.t.
op zeroext_64_256: W64.t -> W256.t.

op zeroext_128_8:   W128.t -> W8.t.
op zeroext_128_16:  W128.t -> W16.t.
op zeroext_128_32:  W128.t -> W32.t.
op zeroext_128_64:  W128.t -> W64.t.
op zeroext_128_128: W128.t -> W128.t.
op zeroext_128_256: W128.t -> W256.t.

op zeroext_256_8:   W256.t -> W8.t.
op zeroext_256_16:  W256.t -> W16.t.
op zeroext_256_32:  W256.t -> W32.t.
op zeroext_256_64:  W256.t -> W64.t.
op zeroext_256_128: W256.t -> W128.t.
op zeroext_256_256: W256.t -> W256.t.

(* -------------------------------------------------------------------- *)
type wsize   = [ W32 | W64 ].
type address = W64.t.

type global_mem_t = {
  gm128 : (address, W128.t) map;
   gm64 : (address,  W64.t) map;
   gm32 : (address,  W32.t) map;
   gm16 : (address,  W16.t) map;
   gm8  : (address,   W8.t) map;
}.
op loadW8   (m : global_mem_t) (a : address) = m.`gm8  .[a].
op loadW16  (m : global_mem_t) (a : address) = m.`gm16 .[a].
op loadW32  (m : global_mem_t) (a : address) = m.`gm32 .[a].
op loadW64  (m : global_mem_t) (a : address) = m.`gm64 .[a].
op loadW128 (m : global_mem_t) (a : address) = m.`gm128.[a].

op storeW8  (m : global_mem_t) (a : address) (w : W8.t) =
  {| m with gm8 = m.`gm8.[a <- w] |}.

op storeW16 (m : global_mem_t) (a : address) (w : W16.t) =
  {| m with gm16 = m.`gm16.[a <- w] |}.

op storeW32 (m : global_mem_t) (a : address) (w : W32.t) =
  {| m with gm32 = m.`gm32.[a <- w] |}.

op storeW64 (m : global_mem_t) (a : address) (w : W64.t) =
  {| m with gm64 = m.`gm64.[a <- w] |}.

op storeW128 (m : global_mem_t) (a : address) (w : W128.t) =
  {| m with gm128 = m.`gm128.[a <- w] |}.

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

(*op x86_SHLD_64 (x:W64.t) (y:W64.t) (cnt:W8.t)=
let result = (drop (to_int cnt) (repr x)) ++ (take (32 - (to_int cnt)) (repr y)) in
let CF = true in
let OF = Logic.(^) (head true result) (head true (repr x)) in
let SF = true in
let ZF = true in
let AF = true in
(CF, OF, SF, ZF, AF, W64.mk result).*)

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
  let f = fun w : W32.t => w `>>`  cnt in
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

(*
lemma test w0 w1 w2 w3: x86_VPSHUFD_128 (pack_4u32 (w0, w1, w2, w3)) 
             (W8.of_int (3 + 4 * (2 + 4 * (1 + 4 * 0)))) = 
            pack_4u32 (w3, w2, w1, w0).
cbv delta.
done.
qed.
*)

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
  let (w10, w11) = unpack_2u32 w1 in
  let (w20, w21) = unpack_2u32 w2 in
  pack_2u32 (W32.mulu_32 w10 w20). 
 
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
  let (w0,w1) = unpack_2u64 w in
  if i = W8.of_int 0 then w0 
  else if i = W8.of_int 1 then w1 
  else W64.of_int 0.

op x86_VPINSR_2u64 (v1:W128.t) (v2:W64.t) (i:W8.t) = 
  let (w0,w1) = unpack_2u64 v1 in
  if i = W8.of_int 0 then pack_2u64 (v2, w1)
  else if i = W8.of_int 1 then pack_2u64 (w0, v2)
  else v1.

op x86_MOVD_64 (v:W64.t) = 
  pack_2u64 (v, W64.zeros). 

op x86_VPUNPCKL_2u64 (w1 w2: W128.t) = 
  let (w10, w11) = unpack_2u64 w1 in
  let (w20, w21) = unpack_2u64 w2 in
  pack_2u64 (w10, w20).

op x86_VPUNPCKH_2u64 (w1 w2: W128.t) = 
  let (w10, w11) = unpack_2u64 w1 in
  let (w20, w21) = unpack_2u64 w2 in
  pack_2u64 (w11, w21).

op x86_VPSLL_2u64 (w:W128.t) (cnt:W8.t) = 
  let f = fun w : W64.t => w `<<`  cnt in
  pack_2u64 (map_2u64 f (unpack_2u64 w)).

op x86_VPSRL_2u64 (w:W128.t) (cnt:W8.t) = 
  let f = fun w : W64.t => w `>>`  cnt in
  pack_2u64 (map_2u64 f (unpack_2u64 w)).

op x86_VPAND_128 = W128.(`&`).
op x86_VPOR_128 = W128.(`|`).

op x86_VPMULU_128 (w1 w2: W128.t) = 
  pack_2u64 (map2_2u64 mulu_64 (unpack_2u64 w1) (unpack_2u64 w2)).

axiom VPAND_128_64 (w10 w11 w20 w21):
  pack_2u64(w10,w11) `&` pack_2u64(w20,w21) = 
  pack_2u64(w10 `&` w20, w11 `&` w21).

axiom VPOR_128_64 (w10 w11 w20 w21):
  pack_2u64(w10,w11) `|` pack_2u64(w20,w21) = 
  pack_2u64(w10 `|` w20, w11 `|` w21).

axiom VPXOR_128_64 (w10 w11 w20 w21):
  pack_2u64(w10,w11) `^` pack_2u64(w20,w21) = 
  pack_2u64(w10 `^` w20, w11 `^` w21).

hint simplify (VPAND_128_64, VPOR_128_64, VPXOR_128_64)@0.

(* ------------------------------------------ *)

op array_init_8   (n:int) : (int, W8  .t) map = CoreMap.cst witness.
op array_init_16  (n:int) : (int, W16 .t) map = CoreMap.cst witness.
op array_init_32  (n:int) : (int, W32 .t) map = CoreMap.cst witness.
op array_init_64  (n:int) : (int, W64 .t) map = CoreMap.cst witness.
op array_init_128 (n:int) : (int, W128.t) map = CoreMap.cst witness.
op array_init_256 (n:int) : (int, W256.t) map = CoreMap.cst witness.





