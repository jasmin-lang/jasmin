require import AllCore IntDiv List CoreMap Jasmin_model.
require import Poly1305_amd64_5x Poly1305_amd64_5xPR Poly1305_avx_5x Poly1305_avx_5xp.

axiom W128_unpack_2u64_of_uint i : 
  unpack_2u64 (W128.of_uint i) = 
    let i = i %% (2^ W128.size) in
    (W64.of_uint (i %% 2^64), W64.of_uint (i %/ 2^64)).

hint simplify W128_unpack_2u64_of_uint.

axiom W64_unpack_2u32_of_uint i : 
  unpack_2u32 (W64.of_uint i) = 
    let i = i %% (2^ W64.size) in
    (W32.of_uint (i %% 2^32), W32.of_uint (i %/ 2^32)).
  
hint simplify W64_unpack_2u32_of_uint.

hint simplify (pack_unpack_2u64, unpack_pack_2u64)@0.
hint simplify (W8.of_uintK, W8.to_uintK')@0.
hint simplify (W32.of_uintK, W32.to_uintK')@0.
hint simplify (W64.of_uintK, W64.to_uintK')@0.
hint simplify (W128.of_uintK, W128.to_uintK')@0.

hint simplify (Array0.get_set_eqE, Array0.get_set_neqE)@0.
hint simplify (Array1.get_set_eqE, Array1.get_set_neqE)@0.
hint simplify (Array2.get_set_eqE, Array2.get_set_neqE)@0.
hint simplify (Array3.get_set_eqE, Array3.get_set_neqE)@0.
hint simplify (Array4.get_set_eqE, Array4.get_set_neqE)@0.
hint simplify (Array5.get_set_eqE, Array5.get_set_neqE)@0.
hint simplify (Array6.get_set_eqE, Array6.get_set_neqE)@0.
hint simplify (Array7.get_set_eqE, Array7.get_set_neqE)@0.
hint simplify (Array8.get_set_eqE, Array8.get_set_neqE)@0.
hint simplify (Array9.get_set_eqE, Array9.get_set_neqE)@0.
hint simplify (Array10.get_set_eqE, Array10.get_set_neqE)@0.

hint simplify (iota0, iotaS_minus)@0.

(* ------------------------------------------------------------------------------ *)
(* AVX-5x and its optimized version AVX-5xp                                       *)
(* ------------------------------------------------------------------------------ *)

equiv poly1305_avx_5x_5xp : 
  Poly1305_avx_5x.M.poly1305 ~ Poly1305_avx_5xp.M.poly1305 :
   ={arg} ==> ={res}.
proof.
  proc => /=; sim (_:true).
  (* remaining_blocks *)
  proc => /=. 
  sim.
  inline{2} M.mulmod_add_u128_prefetch M.mulmod_u128_prefetch.
  inline{1} Poly1305_avx_5x.M.mulmod_u128 Poly1305_avx_5x.M.mulmod_add_u128.
  swap{2} 110 6;sim.
  swap{2} 51 6;sim.
qed.

(* ------------------------------------------------------------------------------ *)
(* AMD64-5x and AMD64-5x_for_proof                                                *)
(* ------------------------------------------------------------------------------ *)

equiv amd64_amd64_pr_load : Poly1305_amd64_5x.M.load ~ Poly1305_amd64_5xPR.M.load :
   ={global_mem, in_0} ==> ={res}.
proof. sim. qed.

equiv poly1305_amd64_amd64_pr : 
  Poly1305_amd64_5x.M.poly1305 ~ Poly1305_amd64_5xPR.M.poly1305 :
    ={arg} ==> ={res}.
proof.
  proc => /=; sim (_:true).
  + proc.    
    swap{1} 10 2.
    swap{1} [12..15] 2.
    swap{1} 17 5. swap{1} 18 -4. swap{1} 21 -6.
    swap{1} 18 2. swap{1} 18 -1.
    swap{2} [10..11] -1.
    inline{2} Poly1305_amd64_5xPR.M.unpack_u128x2_to_u26x5x2
              Poly1305_amd64_5xPR.M.mulmod_u128
              Poly1305_amd64_5xPR.M.add_u128
              Poly1305_amd64_5xPR.M.carry_reduce_u128.
    sim; wp.
    call amd64_amd64_pr_load;wp => /=.
    seq 7 6 : (#pre); 1:by sim.
    conseq />.
    transitivity{1} {
      x0 <@ Poly1305_amd64_5x.M.load(global_mem, in_0);
      x1 <@ Poly1305_amd64_5x.M.load(global_mem, in_0 + (of_uint 32)%W64);
      y0 <@ Poly1305_amd64_5x.M.load(global_mem, in_0 + (of_uint 32)%W64 - (of_uint 16)%W64);
      in_0 <- in_0 + (of_uint 32)%W64 - (of_uint 16)%W64;
    } 
      (={global_mem, in_0, s_r2, s_r2x5} ==> ={global_mem, in_0, x0, x1, y0})
      (={global_mem, in_0, s_r2, s_r2x5} ==> (global_mem{2} = global_mem1{2} /\
             in_0{1} + (of_uint 32)%W64 = in_01{2} + (of_uint 16)%W64) /\
             (in_0{1} + (of_uint 32)%W64 = in_01{2} + (of_uint 16)%W64 =>
             in_0{1} + (of_uint 32)%W64 + (of_uint 16)%W64 = in_0{2} + (of_uint 32)%W64 /\
             ={y0} /\ x1{1} = x2{2} /\ ={x0}))=> //.
    + by move=> &m1 &m2 />; exists global_mem{m2} in_0{m2} s_r2{m2} s_r2x5{m2}.
    + do !(wp;call (_: ={global_mem, in_0} ==> ={res}); 1: by sim).
     
amd64_amd64_pr_load.

#post).

    sp.
in_0{1} 
(* ------------------------------------------------------------------------------ *)
(* AMD64-5x and AVX-5x                                                            *)
(* ------------------------------------------------------------------------------ *)

op rela4 (x y: W64.t Array4.t) 
     (xy : W128.t Array4.t) = 
  xy.[0] = pack_2u64 (x.[0], y.[0]) /\
  xy.[1] = pack_2u64 (x.[1], y.[1]) /\
  xy.[2] = pack_2u64 (x.[2], y.[2]) /\
  xy.[3] = pack_2u64 (x.[3], y.[3]).

op rela5 (x y: W64.t Array5.t) 
     (xy : W128.t Array5.t) = 
  xy.[0] = pack_2u64 (x.[0], y.[0]) /\
  xy.[1] = pack_2u64 (x.[1], y.[1]) /\
  xy.[2] = pack_2u64 (x.[2], y.[2]) /\
  xy.[3] = pack_2u64 (x.[3], y.[3]) /\
  xy.[4] = pack_2u64 (x.[4], y.[4]).

op is_x5 (z : W64.t Array5.t) (zx5 : W64.t Array4.t) = 
  zx5.[0] = z.[1] * W64.of_uint 5 /\
  zx5.[1] = z.[2] * W64.of_uint 5 /\
  zx5.[2] = z.[3] * W64.of_uint 5 /\
  zx5.[3] = z.[4] * W64.of_uint 5.

op bounded n (w:W64.t) = 
  W64.to_uint w < 2^n
  axiomatized by boundedE.

op wf5 (z : W64.t Array5.t) = 
   bounded 27 z.[0] /\
   bounded 27 z.[1] /\
   bounded 27 z.[2] /\
   bounded 27 z.[3] /\
   bounded 27 z.[4].

op wf4 (z : W64.t Array4.t) = 
   bounded 31 z.[0] /\
   bounded 31 z.[1] /\
   bounded 31 z.[2] /\
   bounded 31 z.[3].

axiom bounded_add i x y : 0 < i => bounded (i-1) x => bounded (i-1) y => bounded i (x + y).
axiom bounded_and i x y : bounded i x \/ bounded i y => bounded i (x `&` y).
axiom bounded_shr i j x : 
  0 <= i => (* i + j <= 64 => *)
  bounded (i + j) x => 
  bounded i (x `>>` W8.of_uint j).
axiom bounded_mul i j x y:
  bounded i x => 
  bounded j y =>
  bounded (i+j) (x * y).

axiom bounded_weak (i j:int) x : i <= j => bounded i x => bounded j x.

axiom bounded_w64 i w : 64 <= i => bounded i w.

(*lemma bounded_5 i : 4 <= i => bounded i (W64.of_uint 5).
proof. by move=> ?;apply (bounded_weak 4). qed.

lemma bounded_67108863 i : 26 <= i => bounded 26 (W64.of_uint 67108863).
proof. by move=> ?;apply (bounded_weak 26). qed. *)

lemma bounded_and_2p26 i w : 26 <= i => bounded i (w `&`  (W64.of_uint 67108863)).
proof.
  move=> h; apply (bounded_weak 26); 1: done.
  by apply bounded_and;right;rewrite boundedE. 
qed.

lemma bounded_mul5 i w : bounded (i-4) w => bounded i (w * (W64.of_uint 5)).
proof.
  move=> h; have -> : i = (i - 4) + 4 by ring.
  by apply bounded_mul => //; rewrite boundedE.
qed.

hoare carry_reduceWF : Poly1305_amd64_5x.M.carry_reduce : true ==> wf5 res.
proof.
  proc; wp; skip; rewrite /wf5 => &m1 &m2 /=.
  smt (bounded_and_2p26 bounded_add bounded_shr bounded_mul5 bounded_w64).
qed.

equiv carry_reduceP : Poly1305_amd64_5x.M.carry_reduce ~ Poly1305_avx_5x.M.carry_reduce : 
        ={x} ==> ={res} /\ wf5 res{1}.
proof.
  conseq (_: ={res}) carry_reduceWF.
  by proc; wp; skip => &m1 &m2 /= ->.
qed.

hoare clampWF : Poly1305_amd64_5x.M.clamp : true ==> wf5 res.
proof.
  proc;wp; conseq (_:true);last done.
  rewrite /wf5 /= => ?.
  do !(split || by apply bounded_and;right;rewrite boundedE).
qed.

equiv clampP : Poly1305_amd64_5x.M.clamp ~ Poly1305_avx_5x.M.clamp : 
  ={global_mem, k} ==> ={res} /\ wf5 res{1}.
proof.
  conseq (_: ={res}) clampWF.
  proc; sim.
qed.

axiom pack_mulu_32 w1 w2 : 
  pack_2u32 (W32.mulu w1 w2) = (zeroext_32_64 w1) * (zeroext_32_64 w2).

hint simplify pack_mulu_32.

axiom zeroext_bounded w : bounded 32 w => zeroext_32_64 (unpack_2u32 w).`1 = w.

lemma zeroext_of_uint i : zeroext_32_64 (W32.of_uint i) = W64.of_uint (i %% W32.modulus).
proof. by rewrite zeroext_32_64E. qed.

hint simplify zeroext_of_uint.

equiv add_carryP : Poly1305_amd64_5x.M.add_carry ~ Poly1305_avx_5x.M.add_carry : 
   ={x,y} ==> ={res}.
proof.
  proc => /=.
  conseq (_: Array5.all_eq x{1} x{2}).
  + move=> ??? ??;apply Array5.ext_eq_all.
  unroll for {1} 3; unroll for {2} 3.
  wp; skip; cbv delta => />.
qed.

equiv hadd_u128P : Poly1305_amd64_5x.M.add_carry ~ Poly1305_avx_5x.M.hadd_u128 :  
  rela5 x{1} y{1} x{2} ==> ={res}.
proof.
  proc *.
  inline{2} Poly1305_avx_5x.M.hadd_u128; wp.
  call (add_carryP) => /=.
  conseq (_: Array5.all_eq x{1} h{2} /\ Array5.all_eq y{1} t{2}).
  + by move=> ?????;rewrite !Array5.ext_eq_all.
  by unroll for {2} 5; wp; skip => &m1 &m2; cbv delta => [#] 5!->.
qed.

hint simplify (VPAND_128_64, VPOR_128_64, VPXOR_128_64)@0. 

lemma VPAND_128_64_l w1 w2 : 
   pack_2u64 w1 `&` w2 = 
     pack_2u64(w1.`1 `&` (unpack_2u64 w2).`1, w1.`2 `&` (unpack_2u64 w2).`2).
proof. by rewrite -(pack_unpack_2u64 w2) VPAND_128_64. qed.

hint simplify VPAND_128_64_l@1.

equiv final_mulP : Poly1305_amd64_5x.M.final_mul ~ Poly1305_avx_5x.M.final_mul : 
  wf5 hx{1} /\ wf5 hy{1} /\ wf5 s_r2{1} /\ wf4 s_r2x5{1} /\ wf5 s_r{1} /\ wf4 s_rx5{1} /\
  rela5 hx{1} hy{1} hxy{2} /\
  rela5 s_r2{1} s_r{1} s_r2r{2} /\
  rela4 s_r2x5{1} s_rx5{1} s_r2rx5{2} ==> ={res}.
proof.
  proc => /=.
  call hadd_u128P => /=.
  swap{1} 7 3. swap{1} 6 2. swap{1} 6 -1; wp.
  seq 7 2 : (#post).   
  + inline *; wp; skip; cbv delta.
    move=> &m1 &m2 [#] X0 X1 X2 X3 X4 Y0 Y1 Y2 Y3 Y4.
    move=> R20 R21 R22 R23 R24 R2x0 R2x1 R2x2 R2x3.
    move=> R0 R1 R2 R3 R4 Rx0 Rx1 Rx2 Rx3 14!-> />.
    rewrite (zeroext_bounded hx{m1}.[0]). by move: X0;apply: bounded_weak.
    rewrite (zeroext_bounded hx{m1}.[1]). by move: X1;apply: bounded_weak.
    rewrite (zeroext_bounded hx{m1}.[2]). by move: X2;apply: bounded_weak.
    rewrite (zeroext_bounded hx{m1}.[3]). by move: X3;apply: bounded_weak.
    rewrite (zeroext_bounded hx{m1}.[4]). by move: X4;apply: bounded_weak.
    rewrite (zeroext_bounded hy{m1}.[0]). by move: Y0;apply: bounded_weak.
    rewrite (zeroext_bounded hy{m1}.[1]). by move: Y1;apply: bounded_weak.
    rewrite (zeroext_bounded hy{m1}.[2]). by move: Y2;apply: bounded_weak.
    rewrite (zeroext_bounded hy{m1}.[3]). by move: Y3;apply: bounded_weak.
    rewrite (zeroext_bounded hy{m1}.[4]). by move: Y4;apply: bounded_weak.
    rewrite (zeroext_bounded s_r2{m1}.[0]). by move: R20;apply: bounded_weak.
    rewrite (zeroext_bounded s_r2{m1}.[1]). by move: R21;apply: bounded_weak.
    rewrite (zeroext_bounded s_r2{m1}.[2]). by move: R22;apply: bounded_weak.
    rewrite (zeroext_bounded s_r2{m1}.[3]). by move: R23;apply: bounded_weak.
    rewrite (zeroext_bounded s_r2{m1}.[4]). by move: R24;apply: bounded_weak.
    rewrite (zeroext_bounded s_r2x5{m1}.[0]). by move: R2x0;apply: bounded_weak.
    rewrite (zeroext_bounded s_r2x5{m1}.[1]). by move: R2x1;apply: bounded_weak.
    rewrite (zeroext_bounded s_r2x5{m1}.[2]). by move: R2x2;apply: bounded_weak.
    rewrite (zeroext_bounded s_r2x5{m1}.[3]). by move: R2x3;apply: bounded_weak.
    rewrite (zeroext_bounded s_r{m1}.[0]). by move: R0;apply: bounded_weak.
    rewrite (zeroext_bounded s_r{m1}.[1]). by move: R1;apply: bounded_weak.
    rewrite (zeroext_bounded s_r{m1}.[2]). by move: R2;apply: bounded_weak.
    rewrite (zeroext_bounded s_r{m1}.[3]). by move: R3;apply: bounded_weak.
    rewrite (zeroext_bounded s_r{m1}.[4]). by move: R4;apply: bounded_weak.
    rewrite (zeroext_bounded s_rx5{m1}.[0]). by move: Rx0;apply: bounded_weak.
    rewrite (zeroext_bounded s_rx5{m1}.[1]). by move: Rx1;apply: bounded_weak.
    rewrite (zeroext_bounded s_rx5{m1}.[2]). by move: Rx2;apply: bounded_weak.
    rewrite (zeroext_bounded s_rx5{m1}.[3]). by move: Rx3;apply: bounded_weak.
    done.



 X0.
s_r2{m2}.[1])
    rewrite !zeroext_bounded. 
    admit.
  inline *.
  wp; skip; cbv delta => &m1 &m2 [#] 5!->; cbv delta.
  admit. (* again we need condition on size *)
qed.

phoare unpack_u26x5x2P x0 y0:
   [Poly1305_avx_5x.M.unpack_u26x5x2_to_u26x5x2 :
    s = x0 /\ t = y0 ==> rela5 x0 y0 res] = 1%r.
proof.
  proc.
  (* FIXME "unroll for 3", should work *)
  unroll 3; rcondt 3; 1: by auto.
  unroll 7; rcondt 7; 1: by auto.
  unroll 11; rcondt 11; 1: by auto.
  unroll 15; rcondt 15; 1: by auto.
  unroll 19; rcondt 19; 1: by auto.
  rcondf 23; 1: by auto.
  wp;skip;cbv delta => />.
qed.

equiv remaining_blocksP : Poly1305_amd64_5x.M.remaining_blocks ~ Poly1305_avx_5x.M.remaining_blocks :
   ={global_mem, in_0} /\ rela5 hx{1} hy{1} hxy{2} /\ 
            rela5 s_r2{1} s_r2{1} s_r2r2{2} /\ 
            rela5 s_r4{1} s_r4{1} s_r4r4{2} /\ 
            rela4 s_r2x5{1} s_r2x5{1} s_r2r2x5{2} /\
            rela4 s_r4x5{1} s_r4x5{1} s_r4r4x5{2} ==>
   res{1}.`3 = res{2}.`2 /\
   rela5 res{1}.`1 res{1}.`2 res{2}.`1.
proof.
  proc => /=.
  swap{1}16 9. swap{1} 15 8; wp.
  seq 22 9 : (#post). 
  + admit.
  inline *.
  wp; skip; cbv delta => &m1 &m2 [#] 5!->; cbv delta.
admitted.

equiv first_blockP : Poly1305_amd64_5x.M.first_block ~ Poly1305_avx_5x.M.first_block :
   ={global_mem, in_0} /\
   rela5 s_r2{1} s_r2{1} s_r2r2{2} /\
   rela4 s_r2x5{1} s_r2x5{1} s_r2r2x5{2} ==>
   res{1}.`3 = res{2}.`2 /\
   rela5 res{1}.`1 res{1}.`2 res{2}.`1.
admitted.

(* axiom W64_leNgt (w1 w2: W64.t) : (w1 `<=` w2) = ! (w2 `<` w1). *)


unpack 26 26 26 26 24
r4 : 26 26 26 26 24
r4x5 : 30 30 30 28

mulmod 56 
61       

equiv poly1305_amd64_avx_5x :
  Poly1305_amd64_5x.M.poly1305 ~ Poly1305_avx_5x.M.poly1305 :
   ={arg} ==> ={res}.
proof.
  proc=> /=. sim.
  seq 20 26 : 
    (#pre /\ (r=s_r){1} /\ bounded_32_5 r{1} /\
    ={s_out, s_in, s_inlen, s_k, r, s_r, s_rx5, s_r2x5, h}).
  + wp. call clampP => /=. 
    conseq (_ :
      ={global_mem, out, in_0, inlen, k, s_out, s_in, s_inlen, s_k, s_rx5, s_r2x5, h}) => //.
    by sim.
  seq 2 2 : (#pre /\  (is_x5 r s_rx5){1}).
  + conseq />;unroll for {1} 2; unroll for {2} 2.
    by wp;skip;cbv delta => />.
  seq 4 4 : (#pre /\ ={b64}).
  + by sim />.
  if => //.
  seq 0 0 : (#[/:-1]pre); 1: by auto. 
  seq 5 5 : (#pre /\ ={r2, s_b64, s_r2} /\ (r2 = s_r2){1} /\ bounded_32_5 r2{1}).
  + conseq |>; wp; call carry_reduceP.
    by conseq (_: ={r2, s_b64}) => //; sim.
  seq 2 2 : (#pre /\ (is_x5 r2 s_r2x5){1}).
  + conseq />;unroll for {1} 2; unroll for {2} 2.
    by wp;skip;cbv delta => />.
  seq 0 1 : (#pre); 1: by auto.
  seq 0 2 : (#pre /\ (r2r = s_r2r){2} /\ rela5 r2{1} r{1} r2r{2}).
  + wp.
    exists * r2{2}, r{2}; elim * => r2_R r_R.
    by call{2} (unpack_u26x5x2P r2_R r_R); skip => />.
  seq 0 2 : (#pre /\ rela4 s_r2x5{1} s_rx5{1} s_r2rx5{2}).
  + conseq />;unroll for {2} 2.
    wp;skip => /> &m2 ????? 4!-> ????? 4!-> ? 4!->.
    cbv delta.
    rewrite (zeroext_bounded s_r2{m2}.[1]) // (zeroext_bounded s_r2{m2}.[2]) //.
    rewrite (zeroext_bounded s_r2{m2}.[3]) // (zeroext_bounded s_r2{m2}.[4]) //.
    rewrite (zeroext_bounded s_r{m2}.[1]) // (zeroext_bounded s_r{m2}.[2]) //.
    by rewrite (zeroext_bounded s_r{m2}.[3]) // (zeroext_bounded s_r{m2}.[4]).
  seq 0 2 : (#pre /\ (r2r2 = s_r2r2){2} /\ rela5 r2{1} r2{1} r2r2{2}).
  + wp; conseq />.
    exists * r2{2}; elim * => r2_R.
    by call{2} (unpack_u26x5x2P r2_R r2_R); skip => />.
  seq 0 2 : (#pre /\ rela4 s_r2x5{1} s_r2x5{1} s_r2r2x5{2}).
  + conseq />;unroll for {2} 2.
    wp;skip => /> &m2 ????? 4!-> ????? 4!-> ????? ???? ? 4!->.
    cbv delta.
    rewrite (zeroext_bounded s_r2{m2}.[1]) // (zeroext_bounded s_r2{m2}.[2]) //.
    by rewrite (zeroext_bounded s_r2{m2}.[3]) // (zeroext_bounded s_r2{m2}.[4]).
  seq 1 1 : (#pre /\ (b64 = s_b64){1}); 1: by auto. 
  if => //.
  + seq 4 3 : (#pre /\ ={r4} /\ (r4 = s_r4){1} /\ bounded_32_5 r4{1}).
      + conseq |>; wp;call carry_reduceP.
        by conseq (_: ={r4}) => //; sim.
      seq 0 2 : (#pre /\ (r4r4=s_r4r4){2} /\ rela5 r4{1} r4{1} r4r4{2}).
      + wp; exists * r4{2}; elim * => r4_R.
      by call{2} (unpack_u26x5x2P r4_R r4_R); skip => />.
    seq 2 2 : (#pre /\ rela4 s_r4x5{1} s_r4x5{1} s_r4r4x5{2}).
    + unroll for {1} 2. unroll for {2} 2.
      wp; skip => /> &m1 &m2 ????? ???? ????? ???? ????? ???? ????? ???? ? ????? ? 4!->.
      cbv delta.
      rewrite (zeroext_bounded s_r4{m1}.[1]) // (zeroext_bounded s_r4{m1}.[2]) //.
      by rewrite (zeroext_bounded s_r4{m1}.[3]) // (zeroext_bounded s_r4{m1}.[4]).
    call final_mulP; conseq (_ : rela5 hx{1} hy{1} hxy{2} /\ ={in_0}) => //.
    while (={global_mem, b64, in_0} /\ 
            rela5 hx{1} hy{1} hxy{2} /\ 
            rela5 s_r2{1} s_r2{1} s_r2r2{2} /\ 
            rela5 s_r4{1} s_r4{1} s_r4r4{2} /\ 
            rela4 s_r2x5{1} s_r2x5{1} s_r2r2x5{2} /\
            rela4 s_r4x5{1} s_r4x5{1} s_r4r4x5{2}).
    + by wp; call remaining_blocksP; wp; skip.
    by wp; call first_blockP; wp; skip.  
  rcondf{1} 5.  
  + move=> &m2; wp; conseq (_: true) => //.
    move=> |> ????????. admit. (* would be simpler if we use unsigned comparison *)
  rcondf{2} 5.
  + move=> &m1; wp; conseq (_: true) => //.
    move=> |> ????????.  admit. (* would be simpler if we use unsigned comparison *) 
  call final_mulP; conseq (_ : rela5 hx{1} hy{1} hxy{2} /\ ={in_0}) => //.
  by wp; call first_blockP; wp; skip.  
qed.

