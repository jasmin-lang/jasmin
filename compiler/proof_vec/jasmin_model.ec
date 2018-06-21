require import AllCore BitEncoding IntDiv SmtMap List StdOrder.
(*---*) import CoreMap Map Ring.IntID IntOrder.

(*sopn_tin, sopn_tout*)
abstract theory W.

type t.

op size : { int | 0 < size } as size_gt0.

lemma size_ge0 : 0 <= size.
proof. by apply/ltrW/size_gt0. qed.

hint exact : size_gt0 size_ge0.

op of_int : int -> t.
op to_int : t -> int.

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

axiom of_intK (x : int) : to_int (of_int x) = x %% modulus.
axiom to_intK (x : t  ) : cancel to_int of_int.

op blift1 (f : bool -> bool) (w : t) =
  mk (map f (repr w)).

op blift2 (f : bool -> bool -> bool) (w1 w2 : t) =
  mk (map (fun b : _ * _ => f b.`1 b.`2) (zip (repr w1) (repr w2))).

op ilift1 (f : int -> int) (w : t) =
  of_int (f (to_int w)).

op ilift2 (f : int -> int -> int) (w1 w2 : t) =
  of_int (f (to_int w1) (to_int w2)).

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

op zeros = mk (nseq size false).
op ones  = mk (nseq size true ).

op ( + ) = ilift2 Int.( + ).
op ( - ) = ilift2 Int.( - ).
op ([-]) = ilift1 Int.([-]).
op ( * ) = ilift2 Int.( * ).

op (`&`) = blift2 (/\).
op (`|`) = blift2 (\/).
op (`^`) = blift2 Logic.(^).
 
op (`<=`) (x y : t) = (to_int x) <= (to_int x).
op (`<` ) (x y : t) = (to_int x) <  (to_int x).

op (`>>`) (x : t) (i : int) =
  mk (mkseq (fun j => x.[j + i]) size).

op (`<<`) (x : t) (i : int) =
  mk (mkseq (fun j => x.[j - i]) size).

lemma bandE (w1 w2 : t) (i : int) :
  0 <= i < size => (w1 `&` w2).[i] = (w1.[i] /\ w2.[i]).
proof. by move=> szok; rewrite blift2E szok. qed.

lemma borE (w1 w2 : t) (i : int) :
  0 <= i < size => (w1 `|` w2).[i] = (w1.[i] \/ w2.[i]).
proof. by move=> szok; rewrite blift2E szok. qed.

lemma bxorE (w1 w2 : t) (i : int) :
  0 <= i < size => (w1 `^` w2).[i] = (w1.[i] ^ w2.[i]).
proof. by move=> szok; rewrite blift2E szok. qed.

op slice (i : int) (n : int) (w : t) =
  take n (drop i (repr w)).
end W.

(* example below *)

theory W8.
  clone include W with op size = 8.
  op addc_8: t -> t -> bool -> (bool * t).
end W8.
export W8. 
 
theory W16.
  clone include W with op size = 16.
  op addc_16: t -> t -> bool -> (bool * t).
end W16. 
export W16.

theory W32.
  clone include W with op size = 32.
  op addc_32: t -> t -> bool -> (bool * t).
end W32.
export W32.

theory W64.
  clone include W with op size = 64.
  op mulu_64: t -> t -> (t*t).
  op addc_64: t -> t -> bool -> (bool * t).
end W64. 
export W64.

theory W128.
  clone include W with op size = 128.
  op addc_128: t -> t -> bool -> (bool * t).
end W128. 
export W128.

theory W256.
  clone include W with op size = 256.
  op addc_256: t -> t -> bool -> (bool * t).
  op cast_32: t -> W32.t.
end W256. 
export W256.

(*op sigext_8_8:   W16.t -> W8.t.
op sigext_8_16:  W16.t -> W16.t.
op sigext_8_32:  W16.t -> W32.t.
op sigext_8_64:  W16.t -> W64.t.
op sigext_8_128: W16.t -> W128.t.
op sigext_8_256: W16.t -> W256.t.

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
op sigext_256_256: W256.t -> W256.t.*)

(* -------------------------------------------------------------------- *)
type wsize   = [ W32 | W64 ].
type address = W64.t.

type global_mem_t = {
  gm128 : (address, W128.t) map;
   gm64 : (address,  W64.t) map;
   gm32 : (address,  W32.t) map;
}.

op loadW32  (m : global_mem_t) (a : address) = m.`gm32 .[a].
op loadW64  (m : global_mem_t) (a : address) = m.`gm64 .[a].
op loadW128 (m : global_mem_t) (a : address) = m.`gm128.[a].

op storeW32 (m : global_mem_t) (a : address) (w : W32.t) =
  {| m with gm32 = m.`gm32.[a <- w] |}.

op storeW64 (m : global_mem_t) (a : address) (w : W64.t) =
  {| m with gm64 = m.`gm64.[a <- w] |}.

op storeW128 (m : global_mem_t) (a : address) (w : W128.t) =
  {| m with gm128 = m.`gm128.[a <- w] |}.

(* -------------------------------------------------------------------- *)
type p4u32 = W32.t * W32.t * W32.t * W32.t.

op unpack_4u32 (w : W128.t) : p4u32 =
  (W32.mk (W128.slice 96 32 w),
   W32.mk (W128.slice 64 32 w),
   W32.mk (W128.slice 32 32 w),
   W32.mk (W128.slice  0 32 w)).

op pack_4u32 (w : p4u32) : W128.t =
  W128.mk (W32.repr w.`1 ++ W32.repr w.`2 ++ W32.repr w.`3 ++ W32.repr w.`4).

op map_4u32 (f : W32.t -> W32.t) (w : p4u32) : p4u32 =
  (f w.`1, f w.`2, f w.`3, f w.`4).

(* -------------------------------------------------------------------- *)
op x86_MOVD_32 (x : W32.t) =
  pack_4u32 (x, x, x, x).

op x86_ROL_32 (x : W32.t) (cnt : W8.t) =
  let result = rot (to_int cnt) (repr x) in
  let CF = last true result in
  let OF = Logic.(^) CF (head true result) in
  (CF, OF, W32.mk result).

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
  let f = fun w : W32.t => w `<<` (W8.to_int cnt) in
  pack_4u32 (map_4u32 f (unpack_4u32 w)).

op x86_VPSRL_4u32 (w : W128.t) (cnt : W8.t) =
  let f = fun w : W32.t => w `>>` (W8.to_int cnt) in
  pack_4u32 (map_4u32 f (unpack_4u32 w)).

(* -------------------------------------------------------------------- *)
op x86_VPSHUFB_128_B (w m : W128.t) (i : int) =
  if m.[i * 8 + 7] then W8.zeros else
  let idx = BS2Int.bs2int (W128.slice (i * 8) 4 m) in
  W8.mk (W128.slice idx 8 w).

op x86_VPSHUFB_128 (w m : W128.t) : W128.t =
  W128.mk (flatten (rev (map (W8.repr \o x86_VPSHUFB_128_B w m) (range 0 15)))).

(* -------------------------------------------------------------------- *)
op x86_VPSHUFD_128_B (w : W128.t) (m : W8.t) (i : int) : W32.t =
  let lvl  = BS2Int.bs2int (W8.slice (2 * i) 2 m) in
  (unpack_4u32 (w `>>` lvl)).`1.

op x86_VPSHUFD_128 (w : W128.t) (m : W8.t) : W128.t =
  pack_4u32 (x86_VPSHUFD_128_B w m 4,
             x86_VPSHUFD_128_B w m 3,
             x86_VPSHUFD_128_B w m 2,
             x86_VPSHUFD_128_B w m 1).
