require import AllCore IntDiv List CoreMap Jasmin_model.
require import Poly1305_amd64_5x Poly1305_avx_5x Poly1305_avx_5xp.

hint simplify pow_le0.
hint simplify powS_minus@1.
hint simplify
  (pow2_1, pow2_2, pow2_3, pow2_4, pow2_5, pow2_6, pow2_7, pow2_8)@0.

lemma pow2_32 : 2 ^ 32 = 4294967296.
proof. by cbv delta. qed.

lemma pow2_64 : 2 ^ 64 = 18446744073709551616.
proof. by cbv delta. qed.

lemma pow2_128 : 2 ^ 128 = 340282366920938463463374607431768211456.
proof. by cbv delta. qed.

hint simplify (pow2_32, pow2_64, pow2_128)@0.

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
(* AVX and its optimized version                                                  *)
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

op is_x5 (z zx5 : W64.t Array5.t) = 
  zx5.[0] = z.[1] * W64.of_uint 5 /\
  zx5.[1] = z.[2] * W64.of_uint 5 /\
  zx5.[2] = z.[3] * W64.of_uint 5 /\
  zx5.[3] = z.[4] * W64.of_uint 5.

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

op bounded_32 (w:W64.t) = W64.to_uint w < 2^32.

op bounded_32_5 (z: W64.t Array5.t) = 
  bounded_32 z.[0] /\
  bounded_32 z.[1] /\
  bounded_32 z.[2] /\
  bounded_32 z.[3] /\
  bounded_32 z.[4].

(* axiom to_uint_pos w : 0 <= W64.to_uint w. *)
axiom to_uint_LAND_r (w1 w2:W64.t) : W64.to_uint (w1 `&` w2) <= W64.to_uint w2.

import StdOrder.IntOrder.

lemma bounded_32_LAND_r (w1 w2:W64.t) : W64.to_uint w2 < 2^32 => bounded_32 (w1 `&` w2).
proof.
  rewrite /bounded_32 => h. 
  apply (ler_lt_trans (to_uint w2)) => //.
  by apply to_uint_LAND_r.
qed.

equiv carry_reduceP : Poly1305_amd64_5x.M.carry_reduce ~ Poly1305_avx_5x.M.carry_reduce : 
        ={x} ==> ={res} /\ bounded_32_5 res{1}.
proof.
  proc; wp; skip; rewrite /bounded_32_5 => &m1 &m2 /= -> /=.
  split; 1: by apply bounded_32_LAND_r; cbv delta.
  split.
  + admit.
  split; 1: by apply bounded_32_LAND_r; cbv delta.
  split; 1: by apply bounded_32_LAND_r; cbv delta.
  admit.
admitted.

equiv clampP : Poly1305_amd64_5x.M.clamp ~ Poly1305_avx_5x.M.clamp : 
  ={global_mem, k} ==> ={res} /\ bounded_32_5 res{1}.
proof.
  proc.
  seq 2 2 : (={r}); 1: by sim.
  auto; rewrite /bounded_32_5 /= => ?? -> /=.
  by rewrite !bounded_32_LAND_r; cbv delta.
qed.
  
axiom pack_mulu_32 w1 w2 : 
  pack_2u32 (W32.mulu w1 w2) = (zeroext_32_64 w1) * (zeroext_32_64 w2).

hint simplify pack_mulu_32.

axiom zeroext_bounded w : bounded_32 w => zeroext_32_64 (unpack_2u32 w).`1 = w.

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
  unroll for {2} 5; wp; skip => &m1 &m2; cbv delta => [#] 5!-> /=.
  admit. (* We need to have a symmetry in the code *)
qed.

hint simplify (VPAND_128_64, VPOR_128_64, VPXOR_128_64)@0.

lemma VPAND_128_64_l w1 w2 : 
   pack_2u64 w1 `&` w2 = 
     pack_2u64(w1.`1 `&` (unpack_2u64 w2).`1, w1.`2 `&` (unpack_2u64 w2).`2).
proof. by rewrite -(pack_unpack_2u64 w2) VPAND_128_64. qed.

hint simplify VPAND_128_64_l@1.

equiv final_mulP : Poly1305_amd64_5x.M.final_mul ~ Poly1305_avx_5x.M.final_mul : 
  rela5 hx{1} hy{1} hxy{2} /\
  rela5 s_r2{1} s_r{1} s_r2r{2} /\
  rela4 s_r2x5{1} s_rx5{1} s_r2rx5{2} ==> ={res}.
proof.
  proc => /=.
  call hadd_u128P => /=.
  swap{1} 7 3. swap{1} 6 2. swap{1} 6 -1; wp.
  seq 7 2 : (#post).   
  + inline *; wp; skip. cbv delta.
    move=> &m1 &m2 [#] 14!-> />.
  inline *.
  wp; skip; cbv delta => &m1 &m2 [#] 5!->; cbv delta.
  admit. (* again we need condition on size *)
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

axiom W64_leNgt (w1 w2: W64.t) : (w1 `<=` w2) = ! (w2 `<` w1).

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

