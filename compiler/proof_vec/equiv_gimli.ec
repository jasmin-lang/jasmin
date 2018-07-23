require import AllCore Jasmin_model Gimli_ref Gimli_ref1 Gimliv1 Gimliv CoreMap IntDiv List.

(* --------------------------------------------------------------------------- *)

hint simplify (x86_ROL_32_E, W32.rol_xor_simplify).

(* --------------------------------------------------------------------------- *)
(* FIXME: improve the proof *)
equiv rotate_ref_ref1 : Gimli_ref.M.rotate ~ Gimli_ref1.M.rotate : ={x,bits} /\ 1 <= bits{1} < 32 ==> ={res}.
proof.
  proc;auto => &m1 &m2 /> ??.
  rewrite rol_xor.
  + rewrite modz_small /#.
  rewrite /(`<<`) /(`>>`) /= !modz_small /#.
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
  + unroll for {1} 2; wp;skip => &1 &2 [#] hx hy hz hr hlt ?.
    rewrite -$hx -$hy -$hz -$hr.
    by cbv x86_VPSLL_4u32 x86_VPSRL_4u32;rewrite hlt.
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

equiv vec1_vec : Gimliv1.M.gimli1 ~ Gimliv.M.gimli : 
   ={state, Glob.mem} ==> ={Glob.mem}.
proof.
  proc. sim (_:true).
  proc => /=; inline *;wp;skip => /> &2.
  rewrite -(W4u32.unpack32K r{2}).
  by cbv W4u32.unpack32 x86_VPSLL_4u32 x86_VPSRL_4u32 W32.(`>>`) W32.(`<<`) (%%).
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
