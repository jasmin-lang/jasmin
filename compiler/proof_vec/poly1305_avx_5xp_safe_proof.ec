require import AllCore List Jasmin_model Int IntDiv CoreMap Poly1305_avx_5xp_safe.

hint simplify (oget_some, oget_none).

hoare packS : M.pack : M.safe ==> M.safe.
proof. by proc; wp; skip; cbv delta. qed.

hoare add_carryS : M.add_carry : M.safe ==> M.safe.
proof. 
  proc. 
  rcondt 6; 1: by auto.
  rcondt 25; 1: by auto.
  rcondt 44; 1: by auto.
  rcondt 63; 1: by auto.
  rcondf 82; 1: by auto.
  by wp;skip; cbv delta. 
qed.

hoare unpackS : M.unpack : M.safe ==> M.safe.
proof. by proc; wp; skip; cbv delta. qed.

hoare freezeS : M.freeze : M.safe ==> M.safe.
proof. 
  proc; wp. 
  call add_carryS; wp.
  by skip; cbv delta.
qed.

hoare carry_reduceS : M.carry_reduce : M.safe ==> M.safe.
proof. by proc; wp; skip; cbv delta. qed.

hoare mulmod_12S : M.mulmod_12 : M.safe ==> M.safe.
proof. by proc; wp; skip; cbv delta. qed.

hoare addS : M.add : M.safe ==> M.safe.
proof. 
  proc.
  rcondt 2; 1: by auto.
  rcondt 7; 1: by auto.
  rcondt 12; 1: by auto.
  rcondt 17; 1: by auto.
  rcondt 22; 1: by auto.
  rcondf 27; 1: by auto.
  by wp; skip; cbv delta. 
qed.

hoare load_lastS : M.load_last : M.safe ==> M.safe.
proof. 
  proc; wp.
  conseq (_: M.safe /\ is_init m). 
  + by cbv delta => />.
  seq 4: (M.safe /\ is_init m).
  + rcondt 4; 1: by auto. 
    rcondt 8; 1: by auto.
    rcondf 12; 1: by auto.
    by wp; skip; cbv delta.
  if.
  + wp; conseq (_ : M.safe /\ is_init n /\ is_init m).
    + by cbv delta => />.
    while (M.safe /\ is_init n /\ is_init m /\ is_init c).
    + wp; skip; cbv delta => />.
    by wp; skip; cbv delta => />.
  wp; conseq (_ : M.safe /\ is_init n /\ is_init m).
  + by cbv delta => />.
  while (M.safe /\ is_init n /\ is_init m /\ is_init c).
  + wp; skip; cbv delta => />.
  by wp; skip; cbv delta => />.
qed.
   
hoare loadS: M.load : M.safe ==> M.safe.
proof.
  proc.
  wp; call unpackS.
  by wp; skip; cbv delta.  
qed.

hoare clampS : M.clamp : M.safe ==> M.safe.
proof.
  proc; wp.
  call unpackS; wp.
  by skip; cbv delta.  
qed.

hoare unpack_u26x5x2_to_u26x5x2S : M.unpack_u26x5x2_to_u26x5x2 : M.safe ==> M.safe.
proof.
  proc.
  rcondt 3; 1: by auto.
  rcondt 15; 1: by auto.
  rcondt 27; 1: by auto.
  rcondt 39; 1: by auto.
  rcondt 51; 1: by auto.
  rcondf 63; 1: by auto.
  by wp; skip; cbv delta.
qed.

hoare hadd_u128S : M.hadd_u128 : M.safe ==> M.safe.
proof. 
  proc.  
  wp; call add_carryS.
  rcondt 4; 1: by auto.
  rcondt 13; 1: by auto.
  rcondt 22; 1: by auto.
  rcondt 31; 1: by auto.
  rcondt 40; 1: by auto.
  rcondf 49; 1: by auto.
  by wp; skip; cbv delta.
qed.

hoare carry_reduce_u128S : M.carry_reduce_u128 : M.safe ==> M.safe.
proof. by proc; wp; skip; cbv delta => />. qed.

hoare mulmod_u128S : M.mulmod_u128 : M.safe ==> M.safe.
proof. by proc; wp; skip; cbv delta => />. qed.

hoare add_u128S : M.add_u128 : M.safe ==> M.safe.
proof. 
  proc.
  rcondt 2; 1: by auto.
  rcondt 7; 1: by auto.
  rcondt 12; 1: by auto.
  rcondt 17; 1: by auto.
  rcondt 22; 1: by auto.
  rcondf 27; 1: by auto.
  by wp; skip; cbv delta.
qed.

hoare unpack_u128x2_to_u26x5x2S : M.unpack_u128x2_to_u26x5x2 : M.safe ==> M.safe.
proof. by proc; wp; skip; cbv delta => />. qed.

hoare final_mulS : M.final_mul : M.safe ==> M.safe.
proof.
  proc; wp.
  call hadd_u128S; wp.
  call carry_reduce_u128S; wp.
  by call mulmod_u128S; wp; skip => />; cbv delta.
qed.
  
hoare first_blockS : M.first_block : M.safe ==> M.safe.
proof.
  proc; wp.
  call carry_reduce_u128S; wp.
  call add_u128S; wp.
  call unpack_u128x2_to_u26x5x2S; wp.
  call mulmod_u128S; wp.
  call unpack_u128x2_to_u26x5x2S; wp.
  by skip => />; cbv delta.
qed.

hoare mulmod_add_u128_prefetchS : M.mulmod_add_u128_prefetch : M.safe ==> M.safe.
proof.
  proc; wp.
  call unpack_u128x2_to_u26x5x2S; wp.
  by call add_u128S; wp; skip; cbv delta.
qed.

hoare mulmod_u128_prefetchS : M.mulmod_u128_prefetch : M.safe ==> M.safe.
proof.
  proc; wp.
  by call unpack_u128x2_to_u26x5x2S; wp; skip; cbv delta.
qed.

hoare remaining_blocksS : M.remaining_blocks : M.safe ==> M.safe.
proof.
  proc; wp.
  call carry_reduce_u128S; wp.
  call add_u128S; wp.
  call mulmod_add_u128_prefetchS; wp.
  call mulmod_u128_prefetchS; wp.
  by skip; cbv delta.
qed.

hoare poly1305S : M.poly1305 : M.safe ==> M.safe.
proof.
  proc.
  call packS; wp.
  call add_carryS; wp.
  call unpackS; wp.
  call freezeS; wp.
  seq 61: (M.safe /\ is_init h /\ is_init s_k /\ is_init s_out); last first.
  + skip; cbv delta => />.
  seq 60: (M.safe /\ is_init h /\ is_init s_k /\ is_init s_r /\ is_init s_rx5 /\ is_init s_out); last first.
  + if => //.
    wp. 
    call carry_reduceS; wp.
    call mulmod_12S; wp.
    call addS; wp.
    call load_lastS; wp.
    by skip; cbv delta => />.
  wp. 
  while (M.safe /\ is_init b16 /\ is_init h /\ is_init s_rx5 /\ is_init s_r /\ 
        is_init s_k /\ is_init s_out /\ is_init s_inlen).
  + wp.
    call carry_reduceS; wp.
    call mulmod_12S; wp.
    call addS; wp.
    call loadS; wp.
    by skip; cbv delta => />.
  wp.
  conseq (_: M.safe /\ is_init s_rx5 /\ is_init h /\
             is_init s_r /\ is_init s_k /\ is_init s_out /\ is_init s_inlen).
  + by cbv delta => />. 
  seq 33 : (M.safe /\  is_init s_k /\ is_init s_out /\ is_init s_inlen /\
               is_init r /\ is_init s_r /\ is_init s_in).
  + by wp; call clampS; wp; skip; cbv delta.
  seq 2 : (#pre /\ is_init s_rx5).
  + rcondt 2; 1: by auto.
    rcondt 10; 1: by auto.
    rcondt 18; 1: by auto.
    rcondt 26; 1: by auto.
    rcondf 34; 1: by auto.
    by wp; skip; cbv delta => />.
  seq 2 : (#pre /\ is_init h).
  + rcondt 2; 1: by auto.
    rcondt 6; 1: by auto.
    rcondt 10; 1: by auto.
    rcondt 14; 1: by auto.
    rcondt 18; 1: by auto.
    rcondf 22; 1: by auto.
    by wp; skip; cbv delta => />.
  seq 6 : (#pre /\ is_init b64).
  + by wp; skip; cbv delta.
  if => //.
  seq 15 : (#pre /\ is_init s_b64 /\ is_init r2 /\ is_init s_r2 /\ b64 = s_b64).
  + wp. 
    call carry_reduceS; wp. 
    call mulmod_12S; wp.
    by skip; cbv delta => />  &1; case (b64{1}); cbv delta. 
  seq 2 : (#pre /\ is_init s_r2x5).
  + rcondt 2; 1: by auto.
    rcondt 10; 1: by auto.
    rcondt 18; 1: by auto.
    rcondt 26; 1: by auto.
    rcondf 34; 1: by auto.
    by wp; skip; cbv delta => />.
  seq 9 : (#pre /\ is_init r2r /\ is_init s_r2r).
  + by wp; call unpack_u26x5x2_to_u26x5x2S; wp; skip; cbv delta => />.
  seq 2 : (#pre /\ is_init s_r2rx5).
  + rcondt 2; 1: by auto.
    rcondt 10; 1: by auto.
    rcondt 18; 1: by auto.
    rcondt 26; 1: by auto.
    rcondf 34; 1: by auto.
    by wp; skip; cbv delta => />.
  seq 6 : (#pre /\ is_init r2r2 /\ is_init s_r2r2).
  + wp; call unpack_u26x5x2_to_u26x5x2S; wp.
    by skip; cbv delta => />.  
  seq 2 : (#pre /\ is_init s_r2r2x5).  
  + rcondt 2; 1: by auto.
    rcondt 10; 1: by auto.
    rcondt 18; 1: by auto.
    rcondt 26; 1: by auto.
    rcondf 34; 1: by auto.
    by wp; skip; cbv delta => />.
  seq 4 : (#pre).
  + by wp; skip => /> => &1; case (s_b64{1}); cbv delta. 
  seq 1 : (#pre /\ (W64.of_uint 1 \ult oget b64 => 
                     is_init r4 /\ is_init r4r4 /\ is_init s_r4r4 /\ is_init s_r4r4x5)).
  + if => //.
    seq 15 : (#pre /\ is_init r4 /\ is_init r4r4 /\ is_init s_r4r4).
    + wp. call unpack_u26x5x2_to_u26x5x2S; wp.
      call carry_reduceS; wp.
      call mulmod_12S; wp.
      by skip => />; cbv delta => />.
    rcondt 2; 1: by auto.
    rcondt 10; 1: by auto.
    rcondt 18; 1: by auto.
    rcondt 26; 1: by auto.
    rcondf 34; 1: by auto.
    by wp; skip => />; cbv delta => />.
  wp; call final_mulS; wp.
  seq 7 : (#pre /\ is_init hxy).
  + by wp; call first_blockS; wp; skip => />; cbv delta.
  case : ((of_uint 1)%W64 \ult oget b64).
  + while (M.safe /\ is_init s_b64 /\ is_init b64 /\
            is_init s_r2r2x5 /\ is_init s_r2r2 /\ 
            is_init s_r4r4x5 /\ is_init s_r4r4 /\ is_init hxy).
    + by wp; call remaining_blocksS; wp; skip; cbv delta => />.
    wp; skip => />; cbv delta => /#.
  rcondf 8.
  + wp.
    conseq (_:true) => //.  
    move => &1 /> _ _ _ _ _ _ _ _ _ _ h1 _ _ _ _ _ _ _ _ _ _ _ _ h2.
    admit. (* stuff on comparison *)
  by wp; skip => />; cbv delta.
qed.
