require import AllCore Jasmin_model Gimli_ref Gimli_ref1 Gimliv1 Gimliv CoreMap.




hint simplify (W32.xor_zero_l, W32.xor_zero_r)@0. 
hint simplify (W8.of_uintK, W8.to_uintK', W32.of_uintK, W32.to_uintK')@0.
(*hint simplify (pack_unpack_4u32, unpack_pack_4u32)@0.
  hint simplify (VPAND_128_32, VPOR_128_32, VPXOR_128_32)@0. *)

axiom rol32_xor (x:W32.t) i : 0 <= i < 32 => 
 (x86_ROL_32 x ((of_uint i)%W8)).`3  = (x `<<` (W8.of_uint i)) `^` (x `>>` (W8.of_uint (32 - i))).

equiv rotate_ref_ref1 : Gimli_ref.M.rotate ~ Gimli_ref1.M.rotate : ={x,bits} /\ 0 <= bits{1} < 32 ==> ={res}.
proof.
 by proc;auto => &m1 &m2 /> ??; apply (rol32_xor x{m2} bits{m2}). 
qed. 

equiv Gimli_ref_ref1 : Gimli_ref.M.gimli_body ~ Gimli_ref1.M.gimli_body : ={state} ==> ={res}.
proof.
  proc.
  while (={round, state});last by auto.
  sim; while (={round, state, column}); last by auto.
  sim; do 2! (call rotate_ref_ref1; sim />).
qed.

equiv ref1_vec1 : Gimli_ref1.M.gimli_body ~ Gimliv1.M.gimli_body1 : 
   pack_4u32 (state.[0], state.[1], state.[2] , state.[3] ){1} = x{2} /\
   pack_4u32 (state.[4], state.[5], state.[6] , state.[7] ){1} = y{2} /\
   pack_4u32 (state.[8], state.[9], state.[10], state.[11]){1} = z{2} 
   ==>
   pack_4u32 (res.[0], res.[1], res.[2] , res.[3] ){1} = res.`1{2} /\
   pack_4u32 (res.[4], res.[5], res.[6] , res.[7] ){1} = res.`2{2} /\
   pack_4u32 (res.[8], res.[9], res.[10], res.[11]){1} = res.`3{2}.
proof.
  proc; inline * => /=.
  while (#pre /\ ={round}); last by auto.
  unroll for {1} 2.
  wp; skip => &m1 &m2 [#].
  cbv delta => 4!<- _ _; cbv delta => />.
qed.

axiom rotate24E w :
    x86_VPSHUFB_128  w (W128.of_uint 16028905388486802350658220295983399425)
  = x86_VPSLL_4u32 w (W8.of_uint 24) `^` x86_VPSRL_4u32 w (W8.of_uint 8).

hint simplify rotate24E.

equiv vec1_vec : Gimliv1.M.gimli_body1 ~ Gimliv.M.gimli_body : 
   ={x,y,z} ==> ={res}.
proof.
  proc. sim (_:true).
  proc => /=; inline *;wp;skip => />.
qed.

equiv ref_vec : Gimli_ref.M.gimli_body ~ Gimliv.M.gimli_body : 
   pack_4u32 (state.[0], state.[1], state.[2] , state.[3] ){1} = x{2} /\
   pack_4u32 (state.[4], state.[5], state.[6] , state.[7] ){1} = y{2} /\
   pack_4u32 (state.[8], state.[9], state.[10], state.[11]){1} = z{2} 
   ==>
   pack_4u32 (res.[0], res.[1], res.[2] , res.[3] ){1} = res.`1{2} /\
   pack_4u32 (res.[4], res.[5], res.[6] , res.[7] ){1} = res.`2{2} /\
   pack_4u32 (res.[8], res.[9], res.[10], res.[11]){1} = res.`3{2}.
proof.
  transitivity Gimli_ref1.M.gimli_body 
    (={state} ==> ={res})
    (pack_4u32 (state.[0], state.[1], state.[2] , state.[3] ){1} = x{2} /\
   pack_4u32 (state.[4], state.[5], state.[6] , state.[7] ){1} = y{2} /\
   pack_4u32 (state.[8], state.[9], state.[10], state.[11]){1} = z{2} 
   ==>
   pack_4u32 (res.[0], res.[1], res.[2] , res.[3] ){1} = res.`1{2} /\
   pack_4u32 (res.[4], res.[5], res.[6] , res.[7] ){1} = res.`2{2} /\
   pack_4u32 (res.[8], res.[9], res.[10], res.[11]){1} = res.`3{2}) => //.
  + by move=> &m1 &m2 [#]???; exists state{m1}.  
  by apply Gimli_ref_ref1.
  transitivity Gimliv1.M.gimli_body1
   (pack_4u32 (state.[0], state.[1], state.[2] , state.[3] ){1} = x{2} /\
   pack_4u32 (state.[4], state.[5], state.[6] , state.[7] ){1} = y{2} /\
   pack_4u32 (state.[8], state.[9], state.[10], state.[11]){1} = z{2} 
   ==>
   pack_4u32 (res.[0], res.[1], res.[2] , res.[3] ){1} = res.`1{2} /\
   pack_4u32 (res.[4], res.[5], res.[6] , res.[7] ){1} = res.`2{2} /\
   pack_4u32 (res.[8], res.[9], res.[10], res.[11]){1} = res.`3{2})
   (={x,y,z} ==> ={res}) => //.
  + by move=> &m1 &m2 [#]???; exists (x,y,z){m2}.
  + by apply ref1_vec1.
  by apply vec1_vec.   
qed.
