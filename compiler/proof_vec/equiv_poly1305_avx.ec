require import Int IntDiv CoreMap Jasmin_model.
require import Poly1305_amd64_5x Poly1305_avx_5x Poly1305_avx_5xp.

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

op rela5 (x y: (int, W64.t) map) 
     (xy : (int, W128.t) map) = 
  xy.[0] = pack_2u64 (y.[0], x.[0]) /\
  xy.[1] = pack_2u64 (y.[1], x.[1]) /\
  xy.[2] = pack_2u64 (y.[2], x.[2]) /\
  xy.[3] = pack_2u64 (y.[3], x.[3]) /\
  xy.[4] = pack_2u64 (y.[4], x.[4]).

equiv poly1305_amd64_avx_5x :
  Poly1305_amd64_5x.M.poly1305 ~ Poly1305_avx_5x.M.poly1305 :
   ={arg} ==> ={res}.
proof.
  proc=> /=. sim.
  seq 27 33 : 
    (#pre /\ ={s_out, s_in, s_inlen, s_k,
               r, s_r, s_rx5, h, b64, r2, s_r2, s_r2x5} /\ (r=s_r){1}).
  + seq 21 27 : (#post);last by sim />.
    while (={i,s_r, r} /\ (r=s_r){1}).
    + wp;skip => />.
    
search "_.[_<-_]".
    

    admit.
    sim />.
 sim.
;1:by sim.
  if => //.
  + sim.
  seq  
