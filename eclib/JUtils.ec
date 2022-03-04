require import AllCore IntDiv List Bool StdOrder.
        import IntOrder.

(* -------------------------------------------------------------------- *)

lemma modz_cmp m d : 0 < d => 0 <= m %% d < d.
proof. smt (edivzP). qed.

lemma divz_cmp d i n : 0 < d => 0 <= i < n * d => 0 <= i %/ d < n.
proof.
  by move=> hd [hi1 hi2]; rewrite divz_ge0 // hi1 /= ltz_divLR.
qed.

lemma mulz_cmp_r i m r : 0 < m => 0 <= i < r => 0 <= i * m < r * m.
proof.
  move=> h0m [h0i hir]; rewrite IntOrder.divr_ge0 //=; 1: by apply ltzW.
  by rewrite IntOrder.ltr_pmul2r.
qed.

lemma cmpW i d : 0 <= i < d => 0 <= i <= d.
proof. by move=> [h1 h2];split => // ?;apply ltzW. qed.

lemma le_modz m d : 0 <= m => m %% d <= m.
proof.
  move=> hm.
  have [ ->| [] hd]: d = 0 \/ d < 0 \/ 0 < d by smt().
  + by rewrite modz0.
  + by rewrite -modzN {2}(divz_eq m (-d)); smt (divz_ge0).
  by rewrite {2}(divz_eq m d); smt (divz_ge0).
qed.

lemma bound_abs (i j:int) : 0 <= i < j => 0 <= i < `|j| by smt().
hint solve 0 : bound_abs.

lemma gt0_pow2 (p:int) : 0 < 2^p.
proof. by apply expr_gt0. qed.

lemma dvdmodz d m p : d %| m => d %| p => d %| (p%%m).
proof. move=> h1 h2; rewrite /(%|);rewrite modz_dvd //. qed.

lemma modz_add_carry k i d : 0 <= k < d => 0 <= i < d => d <= k + i =>
   (k + i)%% d = (k + i) - d.
proof.
  move=> hk hi hd; have [_ <- //]:= euclideUl d 1 ((k + i) - d) (k+i) _ _;last by smt().
  by rewrite -divz_eq; ring.
qed.

lemma modz_sub_carry k i d : 0 <= k < d => 0 <= i < d => k - i < 0 =>
   (k - i)%% d = d + (k - i).
  move=> hk hi hd; have [_ <- //]:= euclideUl d (-1) (d + (k - i)) (k-i) _ _;last by smt().
  by rewrite -divz_eq; ring.
qed.

lemma nosmt divz_mod_mul n p i: 0 <= p => 0 <= n =>
  (i %% (n*p)) %/ p = (i %/ p) %% n.
proof.
  move=> [hp | <- //]; move=> [hn | <- //].
  rewrite {2}(divz_eq i (n*p)) {2} (divz_eq (i %% (n * p)) p).
  pose i1 := i %% (n * p).
  have -> : (i %/ (n * p) * (n * p) + (i1 %/ p * p + i1 %% p)) =
         ((i %/ (n * p) * n + i1 %/ p) * p + i1 %% p) by ring.
  have hp0 : p <> 0 by smt().
  rewrite divzMDl 1:// (divz_small (i1%%p) p) 2:/=; 1: smt (edivzP).
  rewrite modzMDl modz_small 2://.
  apply bound_abs;apply divz_cmp => //.
  by apply modz_cmp => /#.
qed.

lemma nosmt divz_mod_div n p i: p %| n => 0 <= p => 0 <= n =>
  (i %% n) %/ p = (i %/ p) %% (n%/p).
proof.
  rewrite dvdz_eq => {2}<- hp hn;apply divz_mod_mul => //.
  by case: hp => [hp | <-//]; apply divz_ge0.
qed.

lemma exp_abs (x n:int) : x ^ `|n| = x ^ n.
proof. by smt (exprV). qed.

lemma modz_mod_pow2 i n k : i %% 2^n %% 2^k = i %% 2^(min `|n| `|k|).
proof. 
  rewrite -(exp_abs 2 n) -(exp_abs 2 k).
  move: `|n| `|k| (IntOrder.normr_ge0 n) (IntOrder.normr_ge0 k) => {n k} n k hn hk.
  rewrite /min;case (n < k) => hnk.
  + by rewrite (modz_small (i %% 2^n)) 2://; smt (modz_cmp gt0_pow2 IntOrder.ler_weexpn2l).
  by rewrite modz_dvd 2://;1: by apply dvdz_exp2l => /#.
qed.

(* FIXME: this is defined in IntDiv but with 0 <= i *)
lemma nosmt modz_pow2_div n p i: 0 <= p <= n =>
  (i %% 2^n) %/ 2^p = (i %/ 2^p) %% 2^(n-p).
proof.
  move=> [h1 h2];rewrite divz_mod_div.
  + by apply dvdz_exp2l.
  + by apply ltzW; apply gt0_pow2.
  + by apply ltzW; apply gt0_pow2.
  congr; have {1}->: n = (n - p) + p by ring.
  by rewrite exprD_nneg 1:/# 1:// mulzK 2://; smt (gt0_pow2).
qed.

(* -------------------------------------------------------------------- *)
lemma powS_minus (x p:int) : 0 < p => x ^ p  = x * x ^ (p-1).
proof. smt (exprS). qed.

hint simplify expr0@1.
hint simplify powS_minus@1.

lemma pow2_0 : 2^0 = 1   by [].
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
lemma pow2_256 : 2 ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 by [].

hint simplify
  (pow2_1, pow2_2, pow2_3, pow2_4, pow2_5, pow2_6, pow2_7, pow2_8,
   pow2_16, pow2_32, pow2_64, pow2_128, pow2_256)@0.

(* -------------------------------------------------------------------- *)
lemma iotaS_minus :
  forall (i n : int), 0 < n => iota_ i n = i :: iota_ (i + 1) (n - 1).
proof. smt (iotaS). qed.

op iotared = iota_
  axiomatized by iotaredE.

lemma iotared0 i n : n <= 0 => iotared i n = [].
proof. by move=> ?; rewrite iotaredE iota0. qed.

lemma iotaredS_minus i n : 0 < n => iotared i n = i :: iotared (i + 1) (n - 1).
proof. by move=> *; rewrite iotaredE iotaS_minus. qed.

hint simplify (iotared0, iotaredS_minus)@0.

lemma nseqS_minus n (e:'a) : 0 < n => nseq n e = e :: nseq (n-1) e.
proof. smt (nseqS). qed.

(* hint simplify (nseq0, nseqS_minus)@0. *)

(* -------------------------------------------------------------------- *)
(* Allow to extend reduction rule with xor *)

lemma xor1b (b : bool) : true ^^ b = !b.
proof. by rewrite xorC xor_true. qed.

lemma xor0b (b : bool) : false ^^ b = b.
proof. by rewrite xorC xor_false. qed.

lemma nosmt xorK_simplify (b1 b2: bool) : b1 = b2 => b1 ^^ b2 = false.
proof. by move=> ->; apply xorK. qed.

hint simplify (xor1b, xor_true, xor0b, xor_false)@0.
hint simplify xorK_simplify@1.

(* -------------------------------------------------------------------- *)
(* extra stuff on list                                                  *)

op map2 ['a, 'b, 'c] (f:'a -> 'b -> 'c) (s:'a list) (t:'b list) =
  with s = "[]"   , t = "[]" => []
  with s = _ :: _ , t = "[]" => []
  with s = "[]"   , t = _ :: _ => []
  with s = x :: s', t = y :: t' => f x y :: map2 f s' t'.

lemma map2_zip (f:'a -> 'b -> 'c) s t :
  map2 f s t = map (fun (p:'a * 'b) => f p.`1 p.`2) (zip s t).
proof.
  by elim: s t => [ | s1 s hrec] [ | t1 t] //=;rewrite hrec.
qed.

op mapN ['a, 'b] (f:'a -> 'b) dfa (s:'a list) N =
  with s = "[]" =>
   if N <= 0 then [] else nseq N (f dfa)
  with s = x :: s' =>
    if N <= 0 then []
    else f x :: mapN f dfa s' (N-1).

op mapN2 ['a, 'b, 'c] (f:'a -> 'b -> 'c) dfa dfb (s:'a list) (t:'b list) N =
  with s = "[]"   , t = "[]"    =>
    if N <= 0 then [] else nseq N (f dfa dfb)

  with s = _ :: _ , t = "[]"    => mapN (fun x => f x dfb) dfa s N

  with s = "[]"   , t = _ :: _  => mapN (fun y => f dfa y) dfb t N

  with s = x :: s', t = y :: t' =>
    if N <= 0 then []
    else f x y :: mapN2 f dfa dfb s' t' (N-1).

lemma nth_mapN ['a, 'b] dfb (f:'a -> 'b) dfa (s:'a list) N i :
  0 <= i < N =>
  nth dfb (mapN f dfa s N) i = f (nth dfa s i).
proof.
  elim: s N i => /= [ | x s hrec] N i hiN;
    have -> /= : !(N <= 0)
      by apply ltzNge; case hiN; apply IntOrder.ler_lt_trans.
  + by rewrite nth_nseq.
  by case (i=0) => // ?; apply hrec => /#.
qed.

lemma nth_mapN2 ['a, 'b, 'c]
  (f:'a -> 'b -> 'c) dfa dfb dfc (s:'a list) (t:'b list) N i :
  0 <= i < N =>
  nth dfc (mapN2 f dfa dfb s t N) i = f (nth dfa s i) (nth dfb t i).
proof.
  elim: s t N i => [ | x s hrec] [ | y t] N i hiN /=;
    have -> /= : !(N <= 0)
      by apply ltzNge; case hiN; apply IntOrder.ler_lt_trans.
  + by rewrite nth_nseq.
  + by case (i=0) => // neqi; apply nth_mapN => /#.
  + by case (i=0) => // neqi; apply nth_mapN => /#.
  by case (i=0) => // ?;apply hrec => /#.
qed.

lemma map2_cat (f:'a -> 'b -> 'c) (l1 l2:'a list) (l1' l2':'b list):
  size l1 = size l1' =>
  map2 f (l1 ++ l2) (l1' ++ l2') = map2 f l1 l1' ++ map2 f l2 l2'.
proof. by move=> hs;rewrite !map2_zip zip_cat // map_cat. qed.

lemma map2C (f: 'a -> 'a -> 'b) (l1 l2:'a list) :
  (forall a1 a2, f a1 a2 = f a2 a1) =>
  map2 f l1 l2 = map2 f l2 l1.
proof.
  move=> hf; elim: l1 l2=> [ | a1 l1 hrec] [ | a2 l2] //=.
  by rewrite hf hrec.
qed.

lemma map2_take1 (f: 'a -> 'b -> 'c) (l1: 'a list) (l2: 'b list) :
  map2 f l1 l2 = map2 f (take (size l2) l1) l2.
proof.
  elim: l1 l2 => [ | a1 l1 hrec] [ | a2 l2] //=.
  have ->: ! 1 + size l2 <= 0 by smt(size_ge0).
  by rewrite hrec.
qed.

lemma map2_take2 (f: 'a -> 'b -> 'c) (l1: 'a list) (l2: 'b list) :
  map2 f l1 l2 = map2 f l1 (take (size l1) l2).
proof.
  elim: l1 l2 => [ | a1 l1 hrec] [ | a2 l2] //=.
  have ->: ! 1 + size l1 <= 0 by smt(size_ge0).
  by rewrite hrec.
qed.

lemma size_map2 (f:'a -> 'b -> 'c) (l1:'a list) l2 : size (map2 f l1 l2) = min (size l1) (size l2).
proof. by rewrite map2_zip size_map size_zip. qed.

lemma nth_map2 dfla dflb dflc (f:'a -> 'b -> 'c) (l1:'a list) l2 i:
  0 <= i < min (size l1) (size l2) =>
  nth dflc (map2 f l1 l2) i = f (nth dfla l1 i) (nth dflb l2 i).
proof.
  elim: l1 l2 i => [ | a l1 hrec] [ | b l2] i /=; 1..3:smt(size_ge0).
  case: (i=0) => [->> // | hi ?].
  apply hrec;smt().
qed.

(* FIXME: we can not do l1 = "[]", l2= _ => l2 *)
op _interleave (l1 l2: 'a list) =
 with l1 = "[]", l2= "[]" => []
 with l1 = "[]", l2= _::_ => l2
 with l1 = _::_, l2 = "[]" => l1
 with l1 = a1::l1', l2 = a2::l2' => a1::a2::_interleave l1' l2'.

(* ------------------------------------------------------------------- *)
(* Safety                                                              *)

op in_bound (x n:int) = 0 <= x /\ x < n.
op is_init (x : 'a option) = x <> None.

lemma is_init_Some (a:'a) : is_init (Some a).
proof. done. qed.

lemma in_bound_simplify x n :
    0 <= x < n => in_bound x n.
proof. done. qed.

hint simplify [eqtrue] is_init_Some.
hint simplify [eqtrue] in_bound_simplify.

(* -------------------------------------------------------------------- *)

lemma powm1_mod k n:
 (0 <= n <= k)%Int =>
 (2^k - 1) %% 2^n = 2^n - 1.
proof.
move=> ?.
have [i [Hi ->]]: exists i, 0<=i /\ k = n+i by exists (k-n); smt().
rewrite exprD_nneg 1,2:/# mulzC (modzMDl (2^i) (-1) (2^n)) modNz //.
by apply gt0_pow2.
qed.

lemma nth_and i bs1 bs2:
 nth false (map2 (/\) bs1 bs2) i = (nth false bs1 i /\ nth false bs2 i).
proof.
rewrite map2_zip.
case: (i < 0) => ?; first by rewrite !nth_neg //.
case: (0 <= i < min (size bs1) (size bs2)) => ?.
 rewrite (nth_map (false,false)) /=.
  by rewrite size_zip.
 rewrite nth_zip_cond.
 by have ->: i < size (zip bs1 bs2) by rewrite size_zip /#.
rewrite nth_default; first by rewrite size_map size_zip /#.
case: (size bs1 < size bs2) => ?.
 have ->//: !nth false bs1 i.
 by rewrite nth_default /#.
have ->//: !nth false bs2 i.
by rewrite nth_default /#.
qed.

require import BitEncoding.
require import StdBigop.
import Bigint Bigint.BIA.

import BitEncoding.BS2Int.

lemma bs2int0P i bs:
 bs2int bs = 0 =>
 !(nth false bs i).
proof.
elim/last_ind : bs => // bs b /= IH.
rewrite bs2int_rcons.
move: (bs2int_ge0 bs) => ?.
have T2: 0 <= 2 ^ size bs * b2i b by smt(expr_ge0).
move=> H1.
have E1: bs2int bs = 0 by smt().
have: 2 ^ size bs * b2i b = 0 by smt().
rewrite Ring.IntID.mulf_eq0; move=> [?|]; first by smt(expr_gt0).
rewrite b2i_eq0 => H0.
rewrite nth_rcons (IH E1) H0 /#.
qed.

lemma bs2int_cat bs1 bs2:
 bs2int (bs1 ++ bs2) = bs2int bs1 + 2^(size bs1) * bs2int bs2.
proof.
move: (size_ge0 bs1) => Hsize1.
move: (size_ge0 bs2) => Hsize2.
rewrite /bs2int (range_cat (size bs1)) //.
 by rewrite size_cat /#.
rewrite big_cat; congr.
 apply eq_big_int => /> ? H H0.
 by rewrite nth_cat H0.
rewrite mulr_sumr /=.
have ->: range (size bs1) (size (bs1 ++ bs2)) = range (size bs1+0) (size bs2+size bs1).
 by rewrite addz0 addzC size_cat.
rewrite range_addr big_map /(\o) /=.
apply eq_big_int => /> *.
by rewrite exprD_nneg // mulzA nth_cat /#.
qed.

lemma bs2int_cons x xs:
  bs2int (x::xs) = b2i x + 2 * bs2int xs.
proof.
have ->: x::xs = [x]++xs by done.
rewrite bs2int_cat /=; congr.
by rewrite /bs2int /= big_int1.
qed.

lemma bs2int_nseq b k: 
  bs2int (nseq k b) = if b /\ 0 <= k then 2^k - 1 else 0.
proof.
case: (0 <= k) => /= hk; last by rewrite nseq0_le 1:/# /bs2int /= big_geq //.
elim: k hk b => [| n Hn IH] b /=.
+ by rewrite nseq0 bs2int_nil.
rewrite nseqS // bs2int_cons ; case: b => ?.
+ rewrite b2i1 exprD_nneg // pow2_1 /= (IH true) /=.
  by ring.
by rewrite (IH false) b2i0; ring.
qed.

lemma bs2int_pad sz bs:
 bs2int bs = bs2int (bs ++ nseq sz false).
proof. by rewrite bs2int_cat (bs2int_nseq false). qed.

lemma bs2int_and0 i bs1 bs2:
 bs2int (map2 (/\) bs1 bs2) = 0 =>
 !(nth false bs1 i /\ nth false bs2 i).
proof. by move=> /bs2int0P H; move: (H i); rewrite nth_and. qed.

lemma bs2int_xor_sub bs1 bs2:
 size bs1 = size bs2 =>
 bs2int (map2 (/\) (map [!] bs1) bs2) = 0 =>
 bs2int (map2 (^^) bs1 bs2) = bs2int bs1 - bs2int bs2.
proof.
move=> Esz.
have Esz2: min (size bs1) (size bs2) = size bs2 by smt().
move=> H.
rewrite /bs2int !Esz !size_map2 !Esz2 sumrN !sumrD.
apply eq_big_int => i /=.
move=> H0; rewrite !map2_zip.
rewrite (nth_map (false,false)) /=; first by rewrite size_zip Esz2.
rewrite nth_zip //=.
case: (nth false bs1 i); case: (nth false bs2 i) => //=.
move=> H1 H2.
move/(bs2int_and0 i): H.
by rewrite (nth_map false) ?Esz // H2 H1.
qed.

lemma bs2int_or_add bs1 bs2:
 size bs1 = size bs2 =>
 bs2int (map2 (/\) bs1 bs2) = 0 =>
 bs2int (map2 (\/) bs1 bs2) = bs2int bs1 + bs2int bs2.
proof.
move=> Esz.
have Esz2: min (size bs1) (size bs2) = size bs2 by smt().
move=> H.
rewrite /bs2int !Esz !size_map2 !Esz2 !sumrD.
apply eq_big_int => i /=.
move=> H0; rewrite !map2_zip.
rewrite (nth_map (false,false)) /=; first by rewrite size_zip Esz2.
rewrite nth_zip //=.
case: (nth false bs1 i); case: (nth false bs2 i) => //=.
move=> H1 H2.
move/(bs2int_and0 i): H.
by rewrite H2 H1.
qed.

lemma bs2int_add_disjoint bs1 bs2 modulus:
 size bs1 = size bs2 =>
 modulus = 2^(size bs2) =>
 bs2int (map2 (/\) bs1 bs2) = 0 =>
 bs2int bs1 + bs2int bs2 < modulus.
proof.
move=> Esz.
have Esz2: min (size bs1) (size bs2) = size bs2 by smt().
move=> H H0.
rewrite -bs2int_or_add // H.
have:= bs2int_le2Xs (map2 (\/) bs1 bs2).
by rewrite size_map2 Esz2.
qed.

lemma bs2int_sub_common bs1 bs2:
 size bs1 = size bs2 =>
 bs2int (map2 (/\) (map [!] bs1) bs2) = 0 =>
 0 <= bs2int bs1 - bs2int bs2.
proof.
move=> Esz.
have Esz2: min (size bs1) (size bs2) = size bs2 by smt().
move=> ?.
rewrite -bs2int_xor_sub //.
by apply bs2int_ge0.
qed.

(* --------------------------------------------------- *)
(* Count leading zeros *)
op lzcnt (x: bool list) : int =
  with x = [] => 0
  with x = b :: l => if b then 0 else 1 + lzcnt l.

lemma lzcnt_size l : 0 <= lzcnt l <= size l.
proof. elim l => //= /#. qed.

lemma lzcnt_bound l :
    (if size l = lzcnt (rev l) then 0 else 2^(size l - lzcnt (rev l) - 1))
      <= bs2int l < 2^(size l - lzcnt (rev l)).
proof.
elim /last_ind: l => /=.
+ by rewrite rev_nil /= bs2int_nil.
move=> l b hrec; rewrite rev_rcons /= size_rcons.
rewrite bs2int_rcons; case: b => _ /=; last by smt().
rewrite /b2i /=.
have -> /= : !(size l + 1 = 0) by smt(size_ge0).
rewrite Ring.IntID.exprD_nneg 1:size_ge0 //=.
smt (bs2int_ge0 bs2int_le2Xs).
qed.

(* --------------------------------------------------- *)
(* shift over integer *)
op (`<<`) (x i : int) : int =
  if (0 <= i) then x * 2^i
  else (x %/ 2^(-i)).

op (`|>>`) (x i : int) : int = x `<<` (-i).
