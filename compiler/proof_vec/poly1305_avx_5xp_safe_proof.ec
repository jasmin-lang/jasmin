require import AllCore List Jasmin_model Int IntDiv CoreMap Poly1305_avx_5xp_safe.

op is_align : wsize -> W64.t -> bool.

op valid_range (w:wsize) (mem:global_mem_t) (ptr:W64.t) (len:int) =
  forall i, i < len => is_valid mem (ptr + W64.of_int (wsize_i w * i)) w.

axiom valid_range_size_le w1 w2 mem ptr len : 
   wsize_i w1 <= wsize_i w2 => 
   valid_range w2 mem ptr len =>
   valid_range w1 mem ptr (len * wsize_i w2 %/ wsize_i w1).

axiom valid_range_size_ge w1 w2 mem ptr len1 len2 :
  is_align w2 ptr => 
  wsize_i w1 <= wsize_i w2 =>  
  (wsize_i w2 %/ wsize_i w1) * len2 <= len1 =>
  valid_range w1 mem ptr len1 =>
  valid_range w2 mem ptr len2.

lemma ult_of_int x y :
   (W64.of_int x \ult W64.of_int y) = (x %% W64.modulus < y %% W64.modulus).
proof. by rewrite W64.ultE /=. qed.

hint simplify ult_of_int.

(*
(* TODO : move this *)  
lemma is_init_Some4 (t:'a Array4.t) : is_init (map Some t).
proof. by cbv delta. qed.

lemma is_init_Some5 (t:'a Array5.t) : is_init (map Some t).
proof. by cbv delta. qed.

hint simplify (is_init_Some4, is_init_Some5)@0.
*)


hoare packS : M.pack : M.safe /\ valid_range W64 Glob.mem y 2 ==> M.safe.
proof. 
  proc; wp; skip => /> &1 _ hv. 
  by have := hv 0; have := hv 1.
qed.

hoare add_carryS : M.add_carry : M.safe ==> M.safe.
proof. by proc; unroll for 6; wp; skip. qed.

hoare unpackS : M.unpack : M.safe /\ valid_range W64 Glob.mem m 2 ==> M.safe.
proof. 
  proc; wp; skip; cbv delta => /> &1 _ hv. 
  by have := hv 0; have := hv 1.
qed.

hoare freezeS : M.freeze : M.safe ==> M.safe.
proof. 
  by proc; wp; call add_carryS; wp; skip; cbv delta.
qed.

hoare carry_reduceS : M.carry_reduce : M.safe ==> M.safe.
proof. by proc; wp; skip. qed.

hoare mulmod_12S : M.mulmod_12 : M.safe ==> M.safe.
proof. by proc; wp; skip. qed.

hoare addS : M.add : M.safe ==> M.safe.
proof. by proc; unroll for 2; wp; skip. qed.

(* TODO: move this *)
lemma nltgeE (x y: W64.t) : (! x \ult y) = (y \ule x).
proof.
  rewrite W64.ultE W64.uleE; smt ().
qed.

(* TODO: move this *)
lemma to_uint_minus (x y: W64.t) : y \ule x => to_uint (x - y) = to_uint x - to_uint y.
proof.
  rewrite W64.addE W64.oppE /ilift2 /ilift1.
admitted.

hoare load_lastS : M.load_last : 
   M.safe /\ valid_range W8 Glob.mem in_0 (W64.to_uint inlen) /\ is_align W64 in_0 ==> M.safe.
proof. 
  proc => /=; wp.
  conseq (_: M.safe /\ is_init m). 
  + by cbv delta => />.
  seq 5: (#pre /\ is_init m).
  + conseq />.  
    by unroll for 4; wp; skip; cbv delta.
  if.
  + wp. 
    while (M.safe /\ is_init n /\ is_init m /\ is_init c /\ 
           valid_range W8 Glob.mem in_0 (to_uint inlen)).
    + wp; skip; cbv delta => /> &1 _ _ _ _ _ hv.
      move: (odflt _ _) => c1; rewrite W64.ultE => hlt.
      by rewrite -(W64.to_uintK c1) hv.
    by wp; skip; cbv delta => />.
  wp. 
  while (M.safe /\ is_init n /\ is_init m /\ is_init c /\ 
         valid_range W8 Glob.mem in_0 (to_uint inlen)).
  + wp; skip; cbv delta => /> &1 _ _ _ _ _ hv.
    move: (odflt _ _) => c1; rewrite W64.ultE => hlt.
    by rewrite -(W64.to_uintK c1) hv.
  wp; skip; cbv delta => /> &1 _ hv ha _ _.
  rewrite nltgeE => ^ hule; rewrite W64.uleE /= => hle.
  split.
  + have h := (valid_range_size_ge W8 W64 Glob.mem{1} in_0{1} 
                   (to_uint inlen{1}) 1 ha _ _ hv) => //.
    by have /= := h 0 _.
admitted.
(*
  move=> i; rewrite to_uint_minus 1:// (W64.to_uint_small 8) 1:// => h.
  by rewrite -addwA add_of; apply hv => /#.
qed. *)
hoare loadS: M.load : M.safe /\ valid_range W64 Glob.mem in_0 2 ==> M.safe.
proof.
  by proc; wp; call unpackS; wp; skip; cbv delta.  
qed.

hoare clampS : M.clamp : M.safe /\ valid_range W64 Glob.mem k 2 ==> M.safe.
proof.
  by proc; wp; call unpackS; wp; skip; cbv delta.  
qed.

hoare unpack_u26x5x2_to_u26x5x2S : M.unpack_u26x5x2_to_u26x5x2 : M.safe ==> M.safe.
proof.
  by proc; unroll for 3; wp; skip; cbv delta.
qed.

hoare hadd_u128S : M.hadd_u128 : M.safe ==> M.safe.
proof. 
  proc.  
  wp; call add_carryS; unroll for 4.
  by wp; skip; cbv delta.
qed.

hoare carry_reduce_u128S : M.carry_reduce_u128 : M.safe ==> M.safe.
proof. by proc; wp; skip. qed.

hoare mulmod_u128S : M.mulmod_u128 : M.safe ==> M.safe.
proof. by proc; wp; skip. qed.

hoare add_u128S : M.add_u128 : M.safe ==> M.safe.
proof. by proc; unroll for 2; wp; skip. qed.

hoare unpack_u128x2_to_u26x5x2S : M.unpack_u128x2_to_u26x5x2 : 
   M.safe /\ valid_range W64 Glob.mem m 4 ==> M.safe.
proof. 
  proc; wp; skip; cbv delta => /> &1 _ hv. 
  by have := hv 0; have := hv 1; have := hv 2; have := hv 3.
qed.

hoare final_mulS : M.final_mul : M.safe ==> M.safe.
proof.
  proc; wp.
  call hadd_u128S; wp.
  call carry_reduce_u128S; wp.
  by call mulmod_u128S; wp; skip.
qed.

(* TODO: move this *)
lemma valid_range_add (k:int) w mem ptr len :
  k <= len =>   
  valid_range w mem ptr len =>
  valid_range w mem (ptr + W64.of_int (k * wsize_i w)) (len - k).
proof.
  move=> hk hv i hi. 
admitted.
(*
  rewrite -addwA add_of. 
  have -> : k * wsize_i w + wsize_i w * i = wsize_i w * (k + i) by ring.
  apply hv => /#.
qed.
*)
(* TODO: move this *)
lemma valid_range_le (len1 len2:int) w mem ptr  :
  len1 <= len2 =>   
  valid_range w mem ptr len2 =>
  valid_range w mem ptr len1.
proof. by move=> hle hv i hlt; apply hv => /#. qed.
  
lemma valid_range_add32 mem ptr :
  valid_range W64 mem ptr 8 =>
  valid_range W64 mem ptr 4 /\
  valid_range W64 mem (ptr + W64.of_int 32) 4.
proof.
  move=> hv;split.
  + by apply: valid_range_le hv.
  by apply (valid_range_add 4 W64 mem ptr 8).
qed.

lemma valid_range_add16 mem ptr :
  valid_range W64 mem ptr 4 =>
  valid_range W64 mem ptr 2 /\
  valid_range W64 mem (ptr + W64.of_int 16) 2.
proof.
  move=> hv;split.
  + by apply: valid_range_le hv.
  by apply (valid_range_add 2 W64 mem ptr 4).
qed.

hoare first_blockS in0 : M.first_block : 
  M.safe /\ valid_range W64 Glob.mem in_0 8 /\ in_0 = in0 ==>
  M.safe /\ res.`2 = in0 + W64.of_int 64.
proof.
  proc; wp.
  call carry_reduce_u128S; wp.
  call add_u128S; wp.
  call unpack_u128x2_to_u26x5x2S; wp.
  call mulmod_u128S; wp.
  call unpack_u128x2_to_u26x5x2S; wp.
  skip => /> &1 _ /valid_range_add32 /> *; ring. 
qed.

hoare mulmod_add_u128_prefetchS : M.mulmod_add_u128_prefetch : 
  M.safe /\ valid_range W64 Glob.mem in_0 4 ==> M.safe.
proof.
  proc; wp.
  call unpack_u128x2_to_u26x5x2S; wp.
  by call add_u128S; wp; skip => />; cbv delta.
qed.

hoare mulmod_u128_prefetchS : M.mulmod_u128_prefetch : 
  M.safe /\ valid_range W64 Glob.mem in_0 4 ==> M.safe.
proof.
  proc; wp.
  by call unpack_u128x2_to_u26x5x2S; wp; skip => />.
qed.

hoare remaining_blocksS in0 : M.remaining_blocks : 
  M.safe /\ valid_range W64 Glob.mem in_0 8 /\ in_0 = in0 ==> 
  M.safe /\ res.`2 = in0 + W64.of_int 64.
proof.
  proc; wp.
  call carry_reduce_u128S; wp.
  call add_u128S; wp.
  call mulmod_add_u128_prefetchS; wp.
  call mulmod_u128_prefetchS; wp.
  skip => /> &1 _ /valid_range_add32 /> *; ring.
qed.


(* TODO move this *)
axiom is_align_add w ptr ofs: 
  wsize_i w %| W64.to_uint ofs => is_align w ptr => is_align w (ptr + ofs).

(*
lemma to_uint0 : to_uint (W64.of_int 0) = 0.
proof. by rewrite W64.to_uint_small. qed.

lemma to_uint1 : to_uint (W64.of_int 1) = 1.
proof. by rewrite W64.to_uint_small. qed.

hint simplify (to_uint0, to_uint1)@0.

axiom to_uint_bounded (w:W64.t) : 0 <= to_uint w < W64.modulus. 
*)
hoare poly1305S : M.poly1305 :
    M.safe /\
    valid_range W64 Glob.mem k 4 /\
    valid_range W8 Glob.mem in_0 (W64.to_uint inlen) /\
    valid_range W64 Glob.mem out 2 /\
    is_align W64 in_0
    ==> 
    M.safe.
proof.
  proc => /=.
  seq 30 : (M.safe /\
    valid_range W64 Glob.mem (oget s_k + W64.of_int 16) 2 /\
    valid_range W8 Glob.mem (oget s_in) (W64.to_uint (oget s_inlen)) /\
    valid_range W64 Glob.mem (oget s_out) 2 /\
    is_align W64 in_0 /\ 
    is_init s_out /\ is_init s_in /\ is_init s_inlen /\ is_init s_k /\ is_init r /\ 
    s_inlen = Some inlen /\ s_in = Some in_0).
  + by wp; call clampS; wp; skip => /> &hr _ /valid_range_add16. 
  seq 6 : (#pre /\ is_init s_r /\ is_init s_rx5).
  + by conseq />; unroll for 5; wp; skip; cbv delta.
  seq 9 : (#pre /\ is_init h /\ is_init b64 /\ 
            to_uint (oget b64) = to_uint inlen %/ 64).
  + conseq />; unroll for 2; wp; skip => /> &1.
    by rewrite (shr_mod inlen{1} (W8.of_int 6)) //=; cbv delta.
  seq 1 : (M.safe /\
           valid_range W64 Glob.mem (oget s_k + (of_int 16)%W64) 2 /\
           valid_range W8 Glob.mem in_0 (to_uint (oget s_inlen) %% 64) /\
           valid_range W64 Glob.mem (oget s_out) 2 /\
           is_align W64 in_0 /\ is_init s_out /\ is_init s_in /\ is_init s_inlen /\ 
           is_init s_k /\ is_init s_r /\ is_init s_rx5 /\ is_init h).
  + if; last first.
    + skip => /> &1 ?? hv ?????????????.
      apply: valid_range_le hv.  
      by rewrite {2} (divz_eq (to_uint inlen{1}) 64); smt (divz_ge0 to_uint_bounded).
    seq 18 : (#pre /\ is_init s_b64 /\ is_init r2 /\ is_init s_r2 /\ is_init s_r2x5 /\
              oget s_b64 = oget b64).
    + conseq />; unroll for 17.
      wp; call carry_reduceS.
      wp; call mulmod_12S.
      by wp; skip => />; cbv delta.
    seq 12 : (#pre /\ is_init s_r2r /\ is_init s_r2rx5).
    + conseq />; unroll for 11.
      by wp; call unpack_u26x5x2_to_u26x5x2S; wp; skip => />; cbv delta.
    seq 9 : (#pre /\ is_init s_r2r2 /\ is_init s_r2r2x5).
    + conseq />; unroll for 8.    
      by wp; call unpack_u26x5x2_to_u26x5x2S; wp; skip => />; cbv delta.
    seq 4 : (#pre).
    + by wp; skip => /> &1 ?    ??????????????????? ->.
    seq 1 : (#pre /\ 
         (W64.of_int 1 \ult oget b64 => (is_init s_r4r4 /\ is_init s_r4r4x5))).
    + conseq />; if => //.
      unroll for 17.
      wp; call unpack_u26x5x2_to_u26x5x2S.
      wp; call carry_reduceS.
      by wp; call mulmod_12S; wp; skip => />; cbv delta.
    wp; call final_mulS; wp.
    conseq (_: M.safe /\ is_align W64 in_0 /\ is_init hxy /\
               valid_range W8 Glob.mem in_0 (to_uint (oget s_inlen) %% 64)) => //.
    while (M.safe /\ is_align W64 in_0 /\ 
           is_init b64 /\
           is_init s_r2r2 /\ is_init s_r2r2x5 /\ is_init hxy /\
           (W64.of_int 0 \ult oget b64 => is_init s_r4r4x5 /\ is_init s_r4r4) /\
           valid_range W8 Glob.mem in_0 (to_uint (oget b64) * 64 + to_uint (oget s_inlen) %% 64)).
    + wp. exists * in_0; elim * => in0.
      call (remaining_blocksS in0); wp; skip => /> &hr _ ha ???? h hv ^ /h /> ??.
      rewrite !W64.ultE /= => ?;split.
      + apply: valid_range_size_ge hv=> //=. 
        by rewrite (_:8 %/ 1 * 8 = 64) 1://; smt (modz_ge0).
      move=> ????? ->; rewrite is_align_add //=.
      have := valid_range_add 64 _ _ _ _ _ hv; 1:smt (modz_ge0).
      rewrite to_uint_minus 1:W64.uleE /= /#. 
    wp. exists * (oget s_in); elim * => in0.      
    call (first_blockS in0); wp; skip => /> &1 _ ? hv ??????????? hd.
    rewrite !W64.ultE /= => h0gt ???? -> ???? h1.
    move:hv; have := divz_eq (to_uint inlen{1}) 64.
    rewrite -hd => {1}-> hv;split.
    + apply: valid_range_size_ge hv => //=.
      by rewrite (_:8 %/ 1 * 8 = 64) 1://; smt (modz_ge0).
    move=> ???? -> />;split.
    + rewrite to_uint_minus 1:W64.uleE /= 1:/# is_align_add //=.
      split; 1: smt().
      by have := valid_range_add 64 _ _ _ _ _ hv; smt (modz_ge0).
    move=> ????; rewrite nltgeE W64.uleE /=.
    smt (to_uint_bounded).
      
  seq 16 : (M.safe /\
           valid_range W64 Glob.mem (oget s_k + (of_int 16)%W64) 2 /\
           valid_range W8 Glob.mem in_0 (to_uint inlen) /\
           valid_range W64 Glob.mem (oget s_out) 2 /\ is_align W64 in_0 /\
           is_init s_out /\ is_init s_in /\ is_init s_inlen /\ 
           is_init s_k /\ is_init s_r /\ is_init s_rx5 /\ is_init h).
  + wp.
    while (M.safe /\
           valid_range W8 Glob.mem in_0 
              (to_uint (oget b16) * 16 + to_uint (oget s_inlen) %% 16) /\
           is_align W64 in_0 /\ is_init s_r /\ is_init s_rx5 /\ is_init h /\ is_init b16). 
    + wp; call carry_reduceS.
      wp; call mulmod_12S.
      wp; call addS.
      wp; call loadS; wp; skip => /> &1 _ hv ha _ _ _ _.
      rewrite W64.ultE /= => ?;split.
      + apply: valid_range_size_ge hv => //.
        have ->: wsize_i W64 %/ wsize_i W8 = 8 by done.
        smt (modz_ge0).
      move=> _; rewrite is_align_add 1://= 1://.
      have := valid_range_add 16 W8 _ _ _ _ hv; 1: smt (modz_ge0).
      rewrite (_: 16 * wsize_i W8 = 16) 1://.
      have -> />: 
        to_uint (oget b16{1} - (of_int 1)%W64) * 16 + to_uint (oget s_inlen{1}) %% 16 = 
        to_uint (oget b16{1}) * 16 + to_uint (oget s_inlen{1}) %% 16 - 16.
      rewrite to_uint_minus; 2: by ring. 
      by rewrite W64.uleE /= /#.
    wp; skip => /> &hr _ _ hv _ ha _ _ _ _ _ _ _;split.
    + have heq : forall x, x %/ 16 %% 4 = x %% 64 %/ 16.
      + move=> x; rewrite {1} (divz_eq x 64) {1}(divz_eq (x%%64) 16).
        rewrite addzA divzDl.
        + by apply dvdzD; apply dvdz_mull.
        rewrite (divz_small (x %% 64 %% 16) 16).
        + by have []:= edivzP (x %% 64) 16.
        rewrite addz0 divzDr; 1: by apply dvdz_mull.
        rewrite mulzK 1:// {2}(_:64 = 4 * 16) 1:// -mulzA mulzK 1:// modzMDl.
        rewrite modz_small 2://;split.
        + by rewrite divz_ge0 1:// modz_ge0.
        by move=> _;rewrite ltz_divLR //; apply ltz_pmod.
      have := and_mod 2 (oget s_inlen{hr} `>>` (of_int 4)%W8) _; 1:by done.
      rewrite (_: 2^2-1 = 3) 1:// /= => ->.
      rewrite shr_mod 1:// (_ : 2 ^ to_uint ((W8.of_int 4)) = 16) 1:// heq.  
      have <- := modz_dvd (to_uint (oget s_inlen{hr})) 64 16 _; 1: done.
      by rewrite -divz_eq hv.   
    have /= -> := and_mod 4 (oget s_inlen{hr}) _; 1: done.
    move=> ? b16 ? ?; rewrite nltgeE W64.uleE /= => ? _ h1 _ _ _.
    apply: valid_range_le h1; smt (to_uint_bounded).

  call packS; wp. 
  call add_carryS; wp.
  call unpackS; wp. 
  call freezeS; wp.
  conseq (_: M.safe /\ 
             valid_range W64 Glob.mem (oget s_k + (of_int 16)%W64) 2 /\
             valid_range W64 Glob.mem (oget s_out) 2 /\
             is_init h /\ is_init s_k /\ is_init s_out).
  + by move=> />; cbv delta.
  if => //.
  wp; call carry_reduceS.
  wp; call mulmod_12S.
  wp; call addS.
  by wp; call load_lastS; skip. 
qed.

