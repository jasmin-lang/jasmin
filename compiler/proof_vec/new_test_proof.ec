require import Int IntDiv Jasmin_model Gimli_ref Gimli_ref1 Gimliv CoreMap.

axiom rol32_xor (x:W32.t) i : 0 <= i < 32 => 
 (x86_ROL_32 x ((of_int i)%W8)).`3  = (x `<<` (W8.of_int i)) `^` (x `>>` (W8.of_int (32 - i))).

equiv rotate_ref_ref1 : Gimli_ref.M.rotate ~ Gimli_ref1.M.rotate : ={x,bits} /\ 0 <= bits{1} < 32 ==> ={res}.
proof.
by proc;auto => &m1 &m2 /> ??;apply (rol32_xor x{m2} bits{m2}). qed. 


equiv Gimli_ref_ref1 : Gimli_ref.M.gimli_body ~ Gimli_ref1.M.gimli_body : ={state} ==> ={res}.
proof.
  proc.
  while (={round, state});last by auto.
  sim; while (={round, state, column}); last by auto.
  sim; do 2! (call rotate_ref_ref1; sim />).
qed.

op of32 : W32.t -> W32.t -> W32.t -> W32.t -> W128.t.
op to32 : W128.t -> W32.t -> W32.t -> W32.t.


equiv ref1_vec1 : Gimli_ref1.M.gimli_body ~ Gimliv.M.gimli_body : 
   (of32 state.[0] state.[1] state.[2]  state.[3] ){1} = x{2} /\
   (of32 state.[4] state.[5] state.[6]  state.[7] ){1} = y{2} /\
   (of32 state.[8] state.[9] state.[10] state.[11]){1} = z{2} 
   ==>
   (of32 res.[0] res.[1] res.[2]  res.[3] ){1} = res.`1{2} /\
   (of32 res.[4] res.[5] res.[6]  res.[7] ){1} = res.`2{2} /\
   (of32 res.[8] res.[9] res.[10] res.[11]){1} = res.`3{2}.
proof.
  proc; inline * => /=.
  while (#pre /\ ={round}); last by auto.
  unroll for {1} 2.
  wp; skip => &m1 &m2 [#].
pragma verbose.
  cbv delta => 4!<- _ _; cbv delta => />.
qed.