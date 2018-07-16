require import AllCore Jasmin_model Gimli_ref Gimli_ref1 Gimliv1 Gimliv CoreMap IntDiv List.

equiv rotate_ref_ref1 : Gimli_ref.M.rotate ~ Gimli_ref1.M.rotate : ={x,bits} /\ 1 <= bits{1} < 32 ==> ={res}.
proof.
  proc;auto => &m1 &m2 /> ??.
  rewrite x86_ROL_32_E /= rol_xor.
  + by rewrite modz_small /#.
  rewrite /(`<<`) /(`>>`) !of_uintK /= !modz_small /#.
qed. 

equiv Gimli_ref_ref1_body : Gimli_ref.M.gimli_body ~ Gimli_ref1.M.gimli_body : ={state} ==> ={res}.
proof.
  proc.
  while (={round, state});last by auto.
  sim; while (={round, state, column}); last by auto.
  sim; do 2! (call rotate_ref_ref1; sim />).
qed.

equiv Gimli_ref_ref1 : Gimli_ref.M.gimli ~ Gimli_ref1.M.gimli : 
   ={istate, Glob.mem } ==> ={Glob.mem}.
proof.
  proc.
  sim 4 4.
  call Gimli_ref_ref1_body; conseq />.
  sim.
qed.

equiv ref1_vec1_body : Gimli_ref1.M.gimli_body ~ Gimliv1.M.gimli_body1 : 
   pack4 [state.[0]; state.[1]; state.[2] ; state.[3] ]{1} = x{2} /\
   pack4 [state.[4]; state.[5]; state.[6] ; state.[7] ]{1} = y{2} /\
   pack4 [state.[8]; state.[9]; state.[10]; state.[11]]{1} = z{2} 
   ==>
   pack4 [res.[0]; res.[1]; res.[2] ; res.[3] ]{1} = res.`1{2} /\
   pack4 [res.[4]; res.[5]; res.[6] ; res.[7] ]{1} = res.`2{2} /\
   pack4 [res.[8]; res.[9]; res.[10]; res.[11]]{1} = res.`3{2}.
proof.
  proc; inline * => /=.
  while (#pre /\ ={round}); last by auto.
  seq 2 47 : (#pre).
  + by unroll for {1} 2; auto. 
  seq 1 1 : (#[/:-2]pre); 1: by auto.
  seq 1 1 : (#pre); 1: by auto.
  auto.
qed.

equiv ref1_vec1 : Gimli_ref1.M.gimli ~ Gimliv1.M.gimli1 : 
   istate{1} = state{2} /\ ={Glob.mem} ==> ={Glob.mem}.
proof.
  proc.
  seq 3 3 : 
   (pack4 [state.[0]; state.[1]; state.[2] ; state.[3] ]{1} = x{2} /\
    pack4 [state.[4]; state.[5]; state.[6] ; state.[7] ]{1} = y{2} /\
    pack4 [state.[8]; state.[9]; state.[10]; state.[11]]{1} = z{2} /\
    ={Glob.mem} /\ istate{1} = state{2}).
  + unroll for{1} 3.
    by wp; skip => /> &2; rewrite -!load4u32.
  seq 1 1 : #pre.
  + by call ref1_vec1_body; skip.
  unroll for{1} 2.
  wp; skip => /> &1 &2.
  by rewrite !store4u32.
qed.

lemma bits8_div_of_int x i : 0 <= i =>
  (W128.of_int x \bits8 i) = W8.of_int (to_uint (W128.of_int x) %/ (2^(8*i))).
proof. by move=> hi;rewrite bits8_div. qed.

hint simplify bits8_div_of_int.

lemma false_eq_not_b b: (false = ! b) = b.
proof. by case b. qed.

lemma b_eq_true b : (b = true) = b.
proof. by case b. qed.

hint simplify (false_eq_not_b, b_eq_true). 

lemma rotate24E w :
    (x86_VPSHUFB_128  w (W128.of_int 16028905388486802350658220295983399425))
  = (x86_VPSLL_4u32 w (W8.of_int 24) `^` x86_VPSRL_4u32 w (W8.of_int 8)).
proof.
  by rewrite -W128.ext_eq_all; cbv delta.
qed.  
hint simplify rotate24E.

equiv vec1_vec : Gimliv1.M.gimli1 ~ Gimliv.M.gimli : 
   ={state, Glob.mem} ==> ={Glob.mem}.
proof.
  proc. sim (_:true).
  proc => /=; inline *;wp;skip => />.
qed.

equiv ref_vec : Gimli_ref.M.gimli ~ Gimliv.M.gimli : 
  istate{1} = state{2} /\ ={Glob.mem} ==> ={Glob.mem}.
  transitivity Gimli_ref1.M.gimli
    (={istate, Glob.mem} ==> ={Glob.mem})
    (istate{1} = state{2} /\ ={Glob.mem} ==> ={Glob.mem}) => //.
  + by move=> &1 &2 />; exists Glob.mem{2} state{2}.  
  + by apply Gimli_ref_ref1.
  transitivity Gimliv1.M.gimli1
    (istate{1} = state{2} /\ ={Glob.mem} ==> ={Glob.mem}) 
    (={state,Glob.mem} ==> ={Glob.mem}) => //.
  + by move=> &1 &2 />; exists Glob.mem{2} state{2}.  
  + by apply ref1_vec1.
  by apply vec1_vec.   
qed.
