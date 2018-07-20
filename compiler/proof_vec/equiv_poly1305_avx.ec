require import AllCore IntDiv List CoreMap Jasmin_model.
require import Poly1305_amd64_5x Poly1305_amd64_5xPR Poly1305_avx_5x Poly1305_avx_5xp.
import StdOrder.IntOrder.

lemma zero_u128_pack : 
  Poly1305_avx_5xp.zero_u128 = pack2 [W64.of_int 0; W64.of_int 0].
proof. by rewrite of_uint_pack2. qed.

lemma five_u128_pack : 
   Poly1305_avx_5xp.five_u128 = pack2 [W64.of_int 5; W64.of_int 5].
proof. by rewrite of_uint_pack2. qed.

lemma bit25_u128_pack :
   Poly1305_avx_5xp.bit25_u128 = pack2 [W64.of_int 16777216; W64.of_int 16777216].
proof. by rewrite of_uint_pack2. qed.

lemma mask26_u128_pack1 :
   Poly1305_avx_5xp.mask26_u128 = pack2 [W64.of_int 67108863; W64.of_int 67108863].
proof. by rewrite of_uint_pack2. qed.

hint simplify (zero_u128_pack, five_u128_pack, bit25_u128_pack, mask26_u128_pack1).

lemma and_small n : 0 <= n < 4294967296 => W64.of_int n `&` W64.of_int 4294967295 = W64.of_int n.
proof. 
  have -> h: 4294967295 = 2^32 - 1 by done. 
  rewrite W64.and_mod //.
  by rewrite W64.of_uintK modz_dvd 1:// modz_small 2://;apply bound_abs.
qed.

hint simplify and_small.

lemma zeroext_truncateu64 (w:W64.t) :
   zeroextu64 (truncateu32 w) = w `&` W64.of_int 4294967295.
proof. by rewrite zeroext_truncateu32_and. qed.

hint simplify zeroext_truncateu64. 

(* ------------------------------------------------------------------------ *)

op bounded n (w:W64.t) = W64.to_uint w < 2^n
axiomatized by boundedE.

lemma bounded_add i x y : 0 < i => bounded (i-1) x => bounded (i-1) y => bounded i (x + y).
proof.
  move=> hi; rewrite !boundedE (powS_minus 2 i) 1://.
  rewrite W64.to_uintD; smt (W64.to_uint_cmp le_modz).
qed.

lemma bounded0 i : bounded i (W64.of_int 0).
proof. by rewrite boundedE /= gt0_pow2. qed.

lemma boundedNeg i w : i <= 0 => bounded i w <=> w = W64.of_int 0.
proof.
  move=> hi;rewrite boundedE powNeg 1:/#;split=> [|-> //].
  rewrite -{2}(W64.to_uintK w)=> h.
  by have -> : to_uint w = 0 by smt (W64.to_uint_cmp).
qed.

lemma bounded_mul i j x y:
  bounded i x => 
  bounded j y =>
  bounded (i+j) (x * y).
proof.
  case: (0 < i) => hi;last first.
  + by rewrite boundedNeg 1:/# => -> /= ?; apply bounded0.
  case: (0 < j)=> hj;last first.
  + by move=> ?; rewrite boundedNeg 1:/# => -> /=; apply bounded0.
  rewrite !boundedE to_uintM -pow_add 1,2:ltzW 1,2:// => h1 h2. 
  apply (ler_lt_trans (to_uint x * to_uint y)).
  + by apply le_modz; smt (W64.to_uint_cmp). 
  apply ltr_pmul => //; smt (W64.to_uint_cmp). 
qed.

lemma bounded_shr i j x : 
  0 <= j < 64 => 0 <= i => 
  bounded (i + j) x => 
  bounded i (x `>>` W8.of_int j).
proof.
  rewrite !boundedE /W64.(`>>`) => -[h0j hjs] hi hx.
  rewrite W8.of_uintK -pow2_6 modz_mod_pow2 /min /=.
  rewrite modz_small 1:// W64.to_uint_shr 1://.
  apply ltz_divLR; 1: by apply gt0_pow2.
  by rewrite pow_add.
qed.

lemma boundedP n w :  
  bounded n w <=> forall i, n <= i < W64.size => !w.[i].
proof.
  case (0 <= n) => hn.
  + have -> : bounded n w <=> (to_uint w = (to_uint w) %% 2^n).
    + rewrite boundedE;split => [h | ->].
      + rewrite modz_small; smt (W64.to_uint_cmp).
      smt (modz_cmp gt0_pow2).
    have -> : to_uint w = to_uint w %% 2 ^ n <=> w = W64.of_int (to_uint w %% 2 ^ n).
    + split => [<- | ->]; 1: by rewrite W64.to_uintK.
      by rewrite of_uintK !modz_mod_pow2 /#. 
    rewrite -W64.and_mod 1://.
    split => [-> i hi| hi].
    + by rewrite /= of_int_powm1 /#.
    apply W64.wordP => i h0i /=;rewrite of_int_powm1 h0i.
    by case (i < n) => hin //=; rewrite hi /#. 
  rewrite boundedNeg 1:/#.
  by split => [-> //| hi];apply W64.wordP => k hk /=;rewrite hi 2:// /#.
qed.

lemma bounded_and i x y : bounded i x \/ bounded i y => bounded i (x `&` y).
proof. by rewrite !boundedP /= => -[] h j hj;rewrite h. qed.
 
lemma bounded_or  i x y : bounded i x /\ bounded i y => bounded i (x `|` y).
proof. by rewrite !boundedP /= => -[h1 h2] j hj;rewrite h1 // h2. qed.

lemma bounded_weak (i j:int) x : i <= j => bounded i x => bounded j x.
proof.
  case : (0 <= i) => hi hij.
  + by rewrite !boundedE; smt (pow_Mle).
  by rewrite boundedNeg 1:/# => ->;apply bounded0.  
qed.

lemma bounded_w64 i w : 64 <= i => bounded i w.
proof. by rewrite boundedE;smt (W64.to_uint_cmp pow_Mle). qed.

lemma bounded_and_2p26 i w : 26 <= i => bounded i (w `&`  (W64.of_int 67108863)).
proof.
  move=> h; apply (bounded_weak 26); 1: done.
  by apply bounded_and;right;rewrite boundedE. 
qed.

lemma bounded_and_2p32 i w : 32 <= i => bounded i (w `&` (W64.of_int 4294967295)).
  move=> h; apply (bounded_weak 32); 1: done.
  by apply bounded_and;right;rewrite boundedE. 
qed.

lemma bounded_mul5 i w : bounded (i-3) w => bounded i (w * (W64.of_int 5)).
proof.
  move=> h; have -> : i = (i - 3) + 3 by ring.
  by apply bounded_mul => //; rewrite boundedE.
qed.

lemma bounded32_and w : bounded 32 w => w `&` (of_int 4294967295)%W64 = w.
proof.
  rewrite boundedE /= => h.
  rewrite -(W64.to_uintK w) and_small 2://; smt (W64.to_uint_cmp).
qed.

(* ------------------------------------------------------------------------------ *)
(* AVX-5x and its optimized version AVX-5xp                                       *)
(* ------------------------------------------------------------------------------ *)

equiv poly1305_avx_5x_5xp : 
  Poly1305_avx_5x.M.poly1305 ~ Poly1305_avx_5xp.M.poly1305 :
   ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof.
  proc => /=; sim (_: ={Glob.mem}).
  (* remaining_blocks *)
  proc => /=. 
  sim.
  inline{2} M.mulmod_add_u128_prefetch M.mulmod_u128_prefetch.
  inline{1} Poly1305_avx_5x.M.mulmod_u128 Poly1305_avx_5x.M.mulmod_add_u128.
  swap{2} 108 6;sim.
  swap{2} 50 6;sim.
qed.

(* ------------------------------------------------------------------------------ *)
(* AMD64-5x and AMD64-5x_for_proof                                                *)
(* ------------------------------------------------------------------------------ *)

equiv amd64_amd64_pr_load : Poly1305_amd64_5x.M.load ~ Poly1305_amd64_5xPR.M.load :
   ={Glob.mem, in_0} ==> ={res}.
proof. sim. qed.

equiv poly1305_amd64_amd64_pr : 
  Poly1305_amd64_5x.M.poly1305 ~ Poly1305_amd64_5xPR.M.poly1305 :
    ={arg,Glob.mem} ==> ={res, Glob.mem}.
proof.
  proc => /=; sim (_: ={Glob.mem}).
  (* first bloc *)
  + proc => /=.    
    swap{1} 10 2.
    swap{1} [12..15] 2.
    swap{1} 17 5. swap{1} 18 -4. swap{1} 21 -6.
    swap{1} 18 2. swap{1} 18 -1.
    swap{2} [10..11] -1.
    inline{2} Poly1305_amd64_5xPR.M.unpack_u128x2_to_u26x5x2
              Poly1305_amd64_5xPR.M.mulmod_u128
              Poly1305_amd64_5xPR.M.add_u128
              Poly1305_amd64_5xPR.M.carry_reduce_u128.
    sim. swap{2} 7 2. swap{2} [16..17] -10. conseq />.
    seq 7 10 : (#pre); 1:by sim.
    transitivity{1} {
        x0 <@ Poly1305_amd64_5x.M.load(in_0);
        x1 <@ Poly1305_amd64_5x.M.load(in_0 + (of_int 32)%W64);
        y0 <@ Poly1305_amd64_5x.M.load((in_0 + (of_int 16)%W64));
        y1 <@ Poly1305_amd64_5x.M.load((in_0 +  (of_int 32)%W64 + (of_int 16)%W64));
        in_0 <- (in_0 + (of_int 32)%W64) + (of_int 32)%W64;
      } 
      (={Glob.mem, in_0, s_r2, s_r2x5} ==> ={in_0, x0, x1, y0, y1})
      (={Glob.mem, in_0, s_r2, s_r2x5} ==> ={in_0, x0, x1, y0, y1})=> //.
    + by move=> &m1 &m2 />; exists Glob.mem{m2} in_0{m2} s_r2{m2} s_r2x5{m2}.
    + do !(wp;call (_: ={Glob.mem, in_0} ==> ={res}); 1: by sim); skip => />.
      move=> &m1; split => [|_]; 1: (by ring); split => [|_]; ring. 
    swap{1} 3 -1; do !(wp; call amd64_amd64_pr_load); auto => />.

  (* remaining_blocks *)
  + proc => /=.
    swap{1} [17..18] -8. swap{1} 9 -1.
    swap{1} [17..18] 6. 
    swap{1} 16 5.
    swap{1} 18 2.
    swap{1} 13 6.
    swap{1} [9..10] 8.
    swap{2} [9..10] -1. swap{2} 5 4. 
    inline{2} Poly1305_amd64_5xPR.M.unpack_u128x2_to_u26x5x2
              Poly1305_amd64_5xPR.M.mulmod_u128 Poly1305_amd64_5xPR.M.mulmod_add_u128
              Poly1305_amd64_5xPR.M.add_u128
              Poly1305_amd64_5xPR.M.carry_reduce_u128.
    sim. swap{2} 5 2. swap{2} [14..15] - 11. conseq />. 
    seq 6 8 : (#pre); 1: by sim.
    transitivity{1} {
        x0 <@ Poly1305_amd64_5x.M.load(in_0);
        x1 <@ Poly1305_amd64_5x.M.load(in_0 + (of_int 32)%W64);
        y0 <@ Poly1305_amd64_5x.M.load((in_0 + (of_int 16)%W64));
        y1 <@ Poly1305_amd64_5x.M.load((in_0 +  (of_int 32)%W64 + (of_int 16)%W64));
        in_0 <- (in_0 + (of_int 32)%W64) + (of_int 32)%W64;
      } 
      ( ={Glob.mem, hx, hy, in_0, s_r4, s_r4x5, s_r2, s_r2x5} ==> ={in_0, hy, y1, y0, x1, x0} )   
      ( ={Glob.mem, hx, hy, in_0, s_r4, s_r4x5, s_r2, s_r2x5} ==> ={in_0, hy, y1, y0, x1, x0} ) => //.
    + by move=> &m1 &m2 />; exists Glob.mem{m2} hx{m2} hy{m2} in_0{m2} s_r2{m2} s_r2x5{m2} s_r4{m2} s_r4x5{m2}.
    move=> />.
    + do !(wp;call (_: ={Glob.mem, in_0} ==> ={res}); 1: by sim); wp; skip => />.
      move=> &m1; split => [|_]; 1: (by ring); split => [|_]; ring. 
    by swap{1} 3 -1; do !(wp; call amd64_amd64_pr_load); auto => />.

  (* final_mul *)
  proc=> /=.
  swap{1} [6..7] 2.
  inline{2} Poly1305_amd64_5xPR.M.mulmod_u128 Poly1305_amd64_5xPR.M.carry_reduce_u128. 
  by sim.
qed.

(* ------------------------------------------------------------------------------ *)
(* AMD64-5x_for_proof and AVX-5x                                                  *)
(* ------------------------------------------------------------------------------ *)

op rela4 (x y: W64.t Array4.t) 
     (xy : W128.t Array4.t) = 
  xy.[0] = pack2 [x.[0]; y.[0]] /\
  xy.[1] = pack2 [x.[1]; y.[1]] /\
  xy.[2] = pack2 [x.[2]; y.[2]] /\
  xy.[3] = pack2 [x.[3]; y.[3]].

op rela5 (x y: W64.t Array5.t) 
     (xy : W128.t Array5.t) = 
  xy.[0] = pack2 [x.[0]; y.[0]] /\
  xy.[1] = pack2 [x.[1]; y.[1]] /\
  xy.[2] = pack2 [x.[2]; y.[2]] /\
  xy.[3] = pack2 [x.[3]; y.[3]] /\
  xy.[4] = pack2 [x.[4]; y.[4]].

op is_x5 (z : W64.t Array5.t) (zx5 : W64.t Array4.t) = 
  zx5.[0] = z.[1] * W64.of_int 5 /\
  zx5.[1] = z.[2] * W64.of_int 5 /\
  zx5.[2] = z.[3] * W64.of_int 5 /\
  zx5.[3] = z.[4] * W64.of_int 5.

op wf5 (z : W64.t Array5.t) = 
   bounded 27 z.[0] /\
   bounded 27 z.[1] /\
   bounded 27 z.[2] /\
   bounded 27 z.[3] /\
   bounded 27 z.[4].

op wf4 (z : W64.t Array4.t) = 
   bounded 30 z.[0] /\
   bounded 30 z.[1] /\
   bounded 30 z.[2] /\
   bounded 30 z.[3].


hoare carry_reduceWF : Poly1305_amd64_5xPR.M.carry_reduce : true ==> wf5 res.
proof.
  proc; wp; skip; rewrite /wf5 => &m1 &m2 /=.
  smt (bounded_and_2p26 bounded_and_2p32 bounded_add bounded_shr bounded_mul5 bounded_w64).
qed.

equiv carry_reduceP : Poly1305_amd64_5xPR.M.carry_reduce ~ Poly1305_avx_5x.M.carry_reduce : 
        ={x} ==> ={res} /\ wf5 res{1}.
proof.
  conseq (_: ={res}) carry_reduceWF.
  by proc; wp; skip => &m1 &m2 /= ->.
qed.


equiv carry_reduce_u128P : Poly1305_amd64_5xPR.M.carry_reduce_u128 ~ Poly1305_avx_5x.M.carry_reduce_u128 : 
        rela5 hx{1} hy{1} x{2} ==>
        rela5 res{1}.`1 res{1}.`2 res{2} /\ wf5 res{1}.`1 /\ wf5 res{1}.`2.
proof.
  conseq (_: rela5 res{1}.`1 res{1}.`2 res{2}) (_ : true ==> wf5 res.`1 /\ wf5 res.`2) => //.
  + by proc; do 2!call carry_reduceWF;auto.
  proc. inline *. wp; skip;rewrite /rela5 => /=. 
  by move=> &m1 &m2 [#] 5!-> /=; cbv x86_VPADD_2u64 x86_VPMULU_128 (%/) (%%) mulu_64.
qed.

hoare clampWF : Poly1305_amd64_5xPR.M.clamp : true ==> wf5 res.
proof.
  proc;wp; conseq (_:true);last done.
  rewrite /wf5 /= => ?.
  do !(split || by apply bounded_and;right;rewrite boundedE).
qed.

equiv clampP : Poly1305_amd64_5xPR.M.clamp ~ Poly1305_avx_5x.M.clamp : 
  ={Glob.mem, k} ==> ={res} /\ wf5 res{1}.
proof.
  conseq (_: ={res}) clampWF.
  proc; sim.
qed.

equiv add_carryP : Poly1305_amd64_5xPR.M.add_carry ~ Poly1305_avx_5x.M.add_carry : 
   ={x,y} ==> ={res}.
proof.
  proc => /=.
  conseq (_: Array5.all_eq x{1} x{2}).
  + move=> ??? ??;apply Array5.ext_eq_all.
  unroll for {1} 3; unroll for {2} 3.
  wp; skip; cbv delta => />.
qed.

equiv hadd_u128P : Poly1305_amd64_5xPR.M.add_carry ~ Poly1305_avx_5x.M.hadd_u128 :  
  rela5 x{1} y{1} x{2} ==> ={res}.
proof.
  proc *.
  inline{2} Poly1305_avx_5x.M.hadd_u128; wp.
  call (add_carryP) => /=.
  conseq (_: Array5.all_eq x{1} h{2} /\ Array5.all_eq y{1} t{2}).
  + by move=> ?????;rewrite !Array5.ext_eq_all.
  by unroll for {2} 5; wp; skip => &m1 &m2; cbv delta => [#] 5!->.
qed.
 
equiv mulmod_u128P : 
  Poly1305_amd64_5xPR.M.mulmod_u128 ~ Poly1305_avx_5x.M.mulmod_u128 : 
  wf5 x1{1} /\ wf5 x2{1} /\ wf5 y1{1} /\ wf5 y2{1} /\ wf4 y1x5{1} /\ wf4 y2x5{1} /\
  rela5 x1{1} x2{1} x{2} /\
  rela5 y1{1} y2{1} y{2} /\
  rela4 y1x5{1} y2x5{1} yx5{2} ==>
  rela5 res{1}.`1 res{1}.`2 res{2}.
proof.
  proc => /=; inline *; wp; skip.
 cbv x86_VPMULU_128 x86_VPADD_2u64 wf5 wf4 rela5 rela4 mulu_64.
  move=> &m1 &m2 [#] X10 X11 X12 X13 X14 X20 X21 X22 X23 X24.
  move=> Y10 Y11 Y12 Y13 Y14 Y20 Y21 Y22 Y23 Y24.
  move=> Y1x0 Y1x1 Y1x2 Y1x3 Y2x0 Y2x1 Y2x2 Y2x3 14!-> /=.
  smt (bounded32_and bounded_weak).
qed.

equiv mulmod_add_u128P : 
  Poly1305_amd64_5xPR.M.mulmod_add_u128 ~ Poly1305_avx_5x.M.mulmod_add_u128 : 
  wf5 x1{1} /\ wf5 x2{1} /\ wf5 y{1} /\ wf4 yx5{1} /\
  rela5 u1{1} u2{1} u{2} /\
  rela5 x1{1} x2{1} x{2} /\
  rela5 y{1} y{1} y{2} /\
  rela4 yx5{1} yx5{1} yx5{2} ==>
  rela5 res{1}.`1 res{1}.`2 res{2}.
proof.
  proc => /=; inline *. 
  unroll for{1} 107. unroll for{1} 20.
  unroll for{2} 11.
  wp; skip; cbv x86_VPMULU_128 x86_VPADD_2u64 wf5 wf4 rela5 rela4 mulu_64.
  move=> &m1 &m2 [#] X10 X11 X12 X13 X14 X20 X21 X22 X23 X24.
  move=> Y0 Y1 Y2 Y3 Y4 Yx0 Yx1 Yx2 Yx3 19!-> /=.
  smt (bounded32_and bounded_weak).
qed.

equiv add_u128P : Poly1305_amd64_5xPR.M.add_u128 ~ Poly1305_avx_5x.M.add_u128 :  
  rela5 x1{1} x2{1} x{2} /\ rela5 y1{1} y2{1} y{2} 
  ==> 
  rela5 res{1}.`1 res{1}.`2 res{2}.
proof.
  proc; inline *.
  unroll for {1} 9; unroll for {1} 4.
  unroll for {2} 2; wp; skip; cbv delta.
  by move=> &1 &2 [#] 10!->.
qed.

hoare loadWF : Poly1305_amd64_5xPR.M.load : true ==> wf5 res.
proof.
  proc; inline *; wp; skip; rewrite /wf5 => /= &hr.
  have h : bounded 27 ((of_int 16777216))%W64 by rewrite boundedE. 
  smt (bounded_and_2p26 bounded_add bounded_shr bounded_w64 bounded_or).
qed.

hint simplify (W64.get_out, W64.of_intwE). 
equiv unpack_u128P : 
 Poly1305_amd64_5xPR.M.unpack_u128x2_to_u26x5x2 ~  Poly1305_avx_5x.M.unpack_u128x2_to_u26x5x2 :
  ={Glob.mem} /\ in_0{1} = m{2} ==> rela5 res{1}.`1 res{1}.`2 res{2} /\ wf5 res{1}.`1 /\ wf5 res{1}.`2.
proof. 
  conseq (_: ={Glob.mem} /\ in_0{1} = m{2} ==> rela5 res{1}.`1 res{1}.`2 res{2}) 
         (_: true ==> wf5 res.`1 /\ wf5 res.`2).
  + by proc; do !(call loadWF;wp); skip.
  proc;inline *;wp; skip => />.
  cbv x86_VPUNPCKL_2u64 x86_MOVD_64 (%/) (%%).
  move => &m.
  by split; apply W128.all_eq_eq;cbv W128.all_eq (%%) (%/) W64.(`>>`) W64.(`<<`) W64.int_bit. 
qed.

equiv remaining_blocksP : Poly1305_amd64_5xPR.M.remaining_blocks ~ Poly1305_avx_5x.M.remaining_blocks :
   ={Glob.mem, in_0} /\ 
   wf5 hx{1} /\ wf5 hy{1} /\ wf5 s_r2{1} /\ wf5 s_r4{1} /\ wf4 s_r2x5{1} /\ wf4 s_r4x5{1} /\
   rela5 hx{1} hy{1} hxy{2} /\ 
   rela5 s_r2{1} s_r2{1} s_r2r2{2} /\ 
   rela5 s_r4{1} s_r4{1} s_r4r4{2} /\ 
   rela4 s_r2x5{1} s_r2x5{1} s_r2r2x5{2} /\
   rela4 s_r4x5{1} s_r4x5{1} s_r4r4x5{2} ==>
   res{1}.`3 = res{2}.`2 /\ wf5 res{1}.`1 /\ wf5 res{1}.`2 /\
   rela5 res{1}.`1 res{1}.`2 res{2}.`1.
proof.
  proc => /=.
  call carry_reduce_u128P. 
  call add_u128P; wp. 
  call unpack_u128P.
  call mulmod_add_u128P; wp.
  call unpack_u128P.
  by call mulmod_u128P; wp; skip.
qed.

equiv first_blockP : Poly1305_amd64_5xPR.M.first_block ~ Poly1305_avx_5x.M.first_block :
   ={Glob.mem, in_0} /\
   wf5 s_r2{1} /\ wf4 s_r2x5{1} /\
   rela5 s_r2{1} s_r2{1} s_r2r2{2} /\
   rela4 s_r2x5{1} s_r2x5{1} s_r2r2x5{2} ==>
   res{1}.`3 = res{2}.`2 /\
   rela5 res{1}.`1 res{1}.`2 res{2}.`1 /\ wf5 res{1}.`1 /\ wf5 res{1}.`2.
proof.
  proc => /=.
  call carry_reduce_u128P.
  call add_u128P; wp.
  call unpack_u128P; wp.
  call mulmod_u128P; wp.
  by call unpack_u128P; wp; skip.
qed.

equiv final_mulP : Poly1305_amd64_5xPR.M.final_mul ~ Poly1305_avx_5x.M.final_mul : 
  wf5 hx{1} /\ wf5 hy{1} /\ wf5 s_r2{1} /\ wf4 s_r2x5{1} /\ wf5 s_r{1} /\ wf4 s_rx5{1} /\
  rela5 hx{1} hy{1} hxy{2} /\
  rela5 s_r2{1} s_r{1} s_r2r{2} /\
  rela4 s_r2x5{1} s_rx5{1} s_r2rx5{2} ==> ={res}.
proof.
  proc => /=.
  call hadd_u128P => /=.
  call carry_reduce_u128P.
  call mulmod_u128P.  
  by wp; skip => />.
qed.

phoare unpack_u26x5x2P x0 y0:
   [Poly1305_avx_5x.M.unpack_u26x5x2_to_u26x5x2 :
    s = x0 /\ t = y0 ==> rela5 x0 y0 res] = 1%r.
proof.
  proc.
  by unroll for 3; wp;skip => />; cbv x86_VPINSR_2u64.
qed.

equiv poly1305_amd64_avx_5x :
  Poly1305_amd64_5xPR.M.poly1305 ~ Poly1305_avx_5x.M.poly1305 :
   ={arg, Glob.mem} ==> ={res, Glob.mem}.
proof.
  proc=> /=. sim.
  seq 20 26 : 
    (#pre /\ (r=s_r){1} /\ wf5 r{1} /\
    ={s_out, s_in, s_inlen, s_k, r, s_r, s_rx5, s_r2x5, h}).
  + wp. call clampP => /=. 
    conseq (_ :
      ={Glob.mem, out, in_0, inlen, k, s_out, s_in, s_inlen, s_k, s_rx5, s_r2x5, h}) => //.
    by sim.
  seq 2 2 : (#pre /\  (is_x5 r s_rx5){1}).
  + conseq />;unroll for {1} 2; unroll for {2} 2.
    by wp;skip;cbv delta => />.
  seq 0 0 : (#pre /\ wf4 s_rx5{1}).
  + by skip => &m1 &m2 /> R0 R1 R2 R3 R4 4!->; rewrite !bounded_mul5.
  seq 4 4 : (#pre /\ ={b64}); 1: by sim />.
  if => //.
  seq 1 1 : (#pre /\ ={s_b64} /\ (b64 = s_b64){1}); 1: by auto.
  seq 4 4 : (#pre /\  ={r2, s_r2} /\ (r2 = s_r2){1} /\ wf5 r2{1}).
  + conseq |>; wp; call carry_reduceP.
    by conseq (_: ={r2}) => //; sim.
  seq 2 2 : (#pre /\ (is_x5 r2 s_r2x5){1}).
  + conseq />;unroll for {1} 2; unroll for {2} 2.
    by wp;skip;cbv delta => />.
  seq 0 0 : (#pre /\ wf4 s_r2x5{1}).
  + by skip => &m1 &m2 |> ? ? ? ? />  R0 R1 R2 R3 R4 4!->; rewrite !bounded_mul5.
  seq 0 1 : (#pre); 1: by auto.
  seq 0 2 : (#pre /\ (r2r = s_r2r){2} /\ rela5 r2{1} r{1} r2r{2}).
  + wp.
    exists * r2{2}, r{2}; elim * => r2_R r_R.
    by call{2} (unpack_u26x5x2P r2_R r_R); skip => />.
  seq 0 2 : (#pre /\ rela4 s_r2x5{1} s_rx5{1} s_r2rx5{2}).
  + conseq />;unroll for {2} 2.
    wp;skip => |> &m2 + + _ _ + + _.
    move=> />  R0 R1 R2 R3 R4 4!-> R20 R21 R22 R23 R24 4!-> ? 4!->.
    by cbv x86_VPMULU_128 (%%) (%/) mulu_64; smt (bounded32_and bounded_weak).
  seq 0 2 : (#pre /\ (r2r2 = s_r2r2){2} /\ rela5 r2{1} r2{1} r2r2{2}).
  + wp; conseq />.
    exists * r2{2}; elim * => r2_R.
    by call{2} (unpack_u26x5x2P r2_R r2_R); skip => />.
  seq 0 2 : (#pre /\ rela4 s_r2x5{1} s_r2x5{1} s_r2r2x5{2}).
  + conseq />;unroll for {2} 2.
    wp;skip => |> &m _ _ _ _ + + _ _ _.
    move=> /> ?????  4!-> ? 4!->.  
    cbv x86_VPMULU_128 (%%) (%/) mulu_64; smt (bounded32_and bounded_weak).
  seq 1 1 : (#pre); 1: by auto. 
  if => //.
  + seq 4 3 : (#pre /\ ={r4} /\ (r4 = s_r4){1} /\ wf5 r4{1}).
    + conseq |>; wp;call carry_reduceP.
      by conseq (_: ={r4}) => //; sim.
    seq 0 2 : (#pre /\ (r4r4=s_r4r4){2} /\ rela5 r4{1} r4{1} r4r4{2}).
    + wp; exists * r4{2}; elim * => r4_R.
      by call{2} (unpack_u26x5x2P r4_R r4_R); skip => />.
    seq 2 2 : (#pre /\ is_x5 r4{1} s_r4x5{1} /\ rela4 s_r4x5{1} s_r4x5{1} s_r4r4x5{2}).
    + unroll for {1} 2. unroll for {2} 2.
      wp; skip => |> &m1 &m2 _ _ _ _ _ _ _ _ _ _ _ _ /> ????? ? 4!->. 
      cbv x86_VPMULU_128 (%%) (%/) mulu_64; smt (bounded32_and bounded_weak).
    seq 0 0 : (#pre /\ wf4 s_r4x5{1}).
    + skip => &m1 &m2 |> ???????????? + _ + _.
      by move=> /> ????? 4!->; rewrite !bounded_mul5.
    call final_mulP => /=.
    while (={Glob.mem, b64, in_0} /\ 
            wf5 hx{1}   /\ wf5 hy{1} /\
            wf5 s_r2{1} /\ wf4 s_r2x5{1} /\
            wf5 s_r4{1} /\ wf4 s_r4x5{1} /\
            rela5 hx{1} hy{1} hxy{2} /\ 
            rela5 s_r2{1} s_r2{1} s_r2r2{2} /\ 
            rela5 s_r4{1} s_r4{1} s_r4r4{2} /\ 
            rela4 s_r2x5{1} s_r2x5{1} s_r2r2x5{2} /\
            rela4 s_r4x5{1} s_r4x5{1} s_r4r4x5{2}).
    + by wp; call remaining_blocksP; wp; skip.
    by wp; call first_blockP; wp; skip.  
  rcondf{1} 5.  
  + move=> &m2; wp; conseq (_: true) => //.
    move=> |> ??? + ???????. 
    rewrite -!uleNgt !W64.uleE W64.ultE /= => h.
    rewrite to_uint_minus 1:W64.uleE /= /#. 
  rcondf{2} 5.
  + move=> &m1; wp; conseq (_: true) => //.
    move=> |> ???? + ???????.  
    rewrite -!uleNgt !W64.uleE W64.ultE /= => h.
    rewrite to_uint_minus 1:W64.uleE /= /#. 
  by call final_mulP; wp; call first_blockP; wp; skip.  
qed.

