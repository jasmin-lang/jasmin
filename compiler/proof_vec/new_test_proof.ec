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

op zero   : W32.t.

axiom xor_zero_l x : zero `^` x = x.
axiom xor_zero_r x : x `^` zero = x.

axiom of32_shl x0 x1 x2 x3 i: 
  (of32 x0 x1 x2 x3) `<<` i = 
  of32 (x0 `<<` i) (x1 `<<` i) (x2 `<<` i) (x3 `<<` i).

axiom of32_shr x0 x1 x2 x3 i: 
  of32 x0 x1 x2 x3 `>>` i = 
  of32 (x0 `>>` i) (x1 `>>` i) (x2 `>>` i) (x3 `>>` i).

axiom of32_xor x0 x1 x2 x3 y0 y1 y2 y3 : 
  of32 x0 x1 x2 x3 `^` of32 y0 y1 y2 y3 = 
  of32 (x0 `^` y0) (x1 `^` y1) (x2 `^` y2) (x3 `^` y3).

axiom of32_and x0 x1 x2 x3 y0 y1 y2 y3 : 
  of32 x0 x1 x2 x3 `&` of32 y0 y1 y2 y3 = 
  of32 (x0 `&` y0) (x1 `&` y1) (x2 `&` y2) (x3 `&` y3).

axiom of32_or x0 x1 x2 x3 y0 y1 y2 y3 : 
  of32 x0 x1 x2 x3 `|` of32 y0 y1 y2 y3 = 
  of32 (x0 `|` y0) (x1 `|` y1) (x2 `|` y2) (x3 `|` y3).

axiom shuffle4_u32_2301 x0 x1 x2 x3 : 
  x86_VPSHUFD_128 (of32 x0 x1 x2 x3) (W8.of_int 177) (*shuffle 2 3 0 1*) = 
  of32 x1 x0 x3 x2.

axiom shuffle4_u32_1032 x0 x1 x2 x3 : 
  x86_VPSHUFD_128 (of32 x0 x1 x2 x3) (W8.of_int 78) (*shuffle 1 0 3 2*) = 
  of32 x2 x3 x0 x1.

axiom of32_x86_VPSLL x0 x1 x2 x3 i :
  x86_VPSLL_4u32 (of32 x0 x1 x2 x3) i =
  of32 (x0 `<<` i) (x1 `<<` i) (x2 `<<` i) (x3 `<<` i).

axiom of32_x86_VPSRL x0 x1 x2 x3 i :
  x86_VPSRL_4u32 (of32 x0 x1 x2 x3) i =
  of32 (x0 `>>` i) (x1 `>>` i) (x2 `>>` i) (x3 `>>` i).

axiom rotate24E w :
    x86_VPSHUFB_128  w (W128.of_int 16028905388486802350658220295983399425)
  = ((w `<<` (W8.of_int 24)) `^` (w `>>` (W8.of_int 8))).

hint simplify xor_zero_l.
hint simplify xor_zero_r.
hint simplify of32_shl.
hint simplify of32_shr.
hint simplify of32_xor.
hint simplify of32_and.
hint simplify of32_or.
(*hint simplify shuffle4_u32_2301.
hint simplify shuffle4_u32_1032.*)
hint simplify of32_x86_VPSLL.
hint simplify of32_x86_VPSRL.
hint simplify rotate24E.

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
  cbv delta => 4!<- _ _; cbv delta => />.
split; move => h1.
rewrite h1. split. auto.
move => _.
+ rewrite shuffle4_u32_2301.
  admit.
+ by rewrite shuffle4_u32_1032.
qed.
