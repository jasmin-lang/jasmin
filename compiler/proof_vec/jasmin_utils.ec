require import AllCore IntDiv List Bool StdOrder.

hint simplify (oget_some, oget_none).

(* -------------------------------------------------------------------- *)

lemma modz_cmp m d : 0 < d => 0 <= m %% d < d.
proof. smt (edivzP). qed.

lemma divz_cmp d i n : 0 < d => 0 <= i < n * d => 0 <= i %/ d < n.
proof.
  by move=> hd [hi1 hi2]; rewrite divz_ge0 // hi1 /= ltz_divLR.
qed.

lemma bound_abs (i j:int) : 0 <= i < j => 0 <= i < `|j| by smt().
hint solve 0 : bound_abs.

lemma gt0_pow2 (p:int) : 0 < 2^p.
proof.
  case (p <= 0)=> [? | /ltzNge hp]; 1:by rewrite pow_le0.
  apply (IntOrder.ltr_le_trans 1) => //.
  by rewrite -(pow_le0 0 2) // pow_Mle /= ltzW.
qed.

lemma dvdmodz d m p : d %| m => d %| p => d %| (p%%m).
proof. move=> h1 h2; rewrite /(%|);rewrite modz_dvd //. qed.

(* -------------------------------------------------------------------- *)
lemma powS_minus (x p:int) : 0 < p => x ^ p  = x * x ^ (p-1).
proof. smt (powS). qed.

hint simplify pow_le0@1.
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
lemma pow2_256 : 2 ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 by [].

hint simplify
  (pow2_1, pow2_2, pow2_3, pow2_4, pow2_5, pow2_6, pow2_7, pow2_8, 
   pow2_16, pow2_32, pow2_64, pow2_128, pow2_256)@0.

(* -------------------------------------------------------------------- *)
lemma iotaS_minus :
  forall (i n : int), 0 < n => iota_ i n = i :: iota_ (i + 1) (n - 1).
proof. smt (iotaS). qed.

hint simplify (iota0, iotaS_minus)@0.

lemma nseqS_minus n (e:'a) : 0 < n => nseq n e = e :: nseq (n-1) e.
proof. smt (nseqS). qed.

hint simplify (nseq0, nseqS_minus)@0.

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

(* ------------------------------------------------------------------- *)
(* Safety                                                              *)

op in_bound (x n:int) = 0 <= x /\ x < n.
op is_init (x : 'a option) = x <> None.

lemma is_init_Some (a:'a) : is_init (Some a).
proof. done. qed.

lemma in_bound_simplify x n : 
    0 <= x < n => in_bound x n.
proof. done. qed.

hint simplify (is_init_Some, in_bound_simplify).