require import Int IntDiv CoreMap.

(* uint 32 operations *)

theory U32.
type u32.

op zero   : u32.
op rol32  : u32 -> int -> u32.
op (`<<`) : u32 -> int -> u32.
op (`>>`) : u32 -> int -> u32.
op (^)    : u32 -> u32 -> u32.
op (&)    : u32 -> u32 -> u32.
op (`|`)  : u32 -> u32 -> u32.
op ofint  : int -> u32.

axiom rol32_xor x i : 0 <= i < 32 => 
  rol32 x i = (x `<<` i) ^ (x `>>` (32 - i)).

axiom xor_zero_l x : zero ^ x = x.
axiom xor_zero_r x : x ^ zero = x.

axiom shl_0 w : w `<<` 0 = w.
axiom shr_0 w : w `>>` 0 = w.
axiom shr_32 w : w `>>` 32 = zero.

end U32. import U32.

(* vector 128 bits *)
theory U128.

type u128.

op (`<<`) : u128 -> int -> u128.
op (`>>`) : u128 -> int -> u128.
op (^)    : u128 -> u128 -> u128.
op (&)    : u128 -> u128 -> u128.
op (`|`)  : u128 -> u128 -> u128.



op shuffle16_u8 : u128 -> int -> u128.

op shuffle a b c d = a * 64 + b * 16 + c * 4 + d.
op shuffle4_u32 : u128 -> int -> u128.

op of32 : u32 -> u32 -> u32 -> u32 -> u128.

op to32 : u128 -> u32 * u32 * u32 * u32.

op zeroextend w = of32 w U32.zero U32.zero U32.zero.

axiom of32_shl x0 x1 x2 x3 i: 
  (of32 x0 x1 x2 x3) `<<` i = 
  of32 (x0 `<<` i) (x1 `<<` i) (x2 `<<` i) (x3 `<<` i).

axiom of32_shr x0 x1 x2 x3 i: 
  of32 x0 x1 x2 x3 `>>` i = 
  of32 (x0 `>>` i) (x1 `>>` i) (x2 `>>` i) (x3 `>>` i).

axiom of32_xor x0 x1 x2 x3 y0 y1 y2 y3 : 
  of32 x0 x1 x2 x3 ^ of32 y0 y1 y2 y3 = 
  of32 (x0 ^ y0) (x1 ^ y1) (x2 ^ y2) (x3 ^ y3).

axiom of32_and x0 x1 x2 x3 y0 y1 y2 y3 : 
  of32 x0 x1 x2 x3 & of32 y0 y1 y2 y3 = 
  of32 (x0 & y0) (x1 & y1) (x2 & y2) (x3 & y3).

axiom of32_or x0 x1 x2 x3 y0 y1 y2 y3 : 
  of32 x0 x1 x2 x3 `|` of32 y0 y1 y2 y3 = 
  of32 (x0 `|` y0) (x1 `|` y1) (x2 `|` y2) (x3 `|` y3).

axiom shuffle4_u32_2301 x0 x1 x2 x3 : 
  shuffle4_u32 (of32 x0 x1 x2 x3) 177 (*shuffle 2 3 0 1*) = 
  of32 x1 x0 x3 x2.

axiom shuffle4_u32_1032 x0 x1 x2 x3 : 
  shuffle4_u32 (of32 x0 x1 x2 x3) 78 (*shuffle 1 0 3 2*) = 
  of32 x2 x3 x0 x1.

end U128. import U128.

hint simplify xor_zero_l.
hint simplify xor_zero_r.
hint simplify of32_shl.
hint simplify of32_shr.
hint simplify of32_xor.
hint simplify of32_and.
hint simplify of32_or.
hint simplify shuffle4_u32_2301.
hint simplify shuffle4_u32_1032.
hint simplify shl_0.
hint simplify shr_0.
hint simplify shr_32.

(* -------------------------------------------------------------------- *)

module XOR = {
  proc xor (x, y: (int, u32) map) = {
    var i : int = 0;
    var z : (int, u32) map;
    while (i < 4) { 
      z.[i] <- x.[i] ^ y.[i];
      i <- i + 1;
    }
    return z;
  }
}.

module VXOR = {
  proc xor (x,y: u128) = {
    return x ^ y;
  }
}.

op veq32 (x:(int,u32) map) (v:u128) = 
   of32 x.[0] x.[1] x.[2] x.[3] = v.

equiv XOR_VXOR : XOR.xor ~ VXOR.xor : veq32 x{1} x{2} /\ veq32 y{1} y{2} ==> veq32 res{1} res{2}.
proof.
  proc.
  unroll for {1} 2; wp; skip=> &m1 &m2;cbv delta => />.
qed.

(* ---------------------------------------------------------------------- *)

(* Gimli reference implementation *)
module type Rotate = { 
  proc rotate (x:u32, bits:int) : u32
}.

op Ox9e377900 = ofint 2654435584.

module Gimli_gen (O:Rotate) = {
  proc gimli(state : (int, u32) map) = {
    var round, column : int;
    var x, y, z : u32;
  
    round <- 24;
    while (0 < round) {
      column <- 0;
      while (column < 4) { 
        x <- state.[column];
        x <@ O.rotate(x, 24);
        y <- state.[4 + column];
        y <@ O.rotate(y, 9);
        z <- state.[8 + column];
  
        state.[8 + column] <- x ^ (z `<<` 1) ^ ((y & z) `<<` 2);
        state.[4 + column] <- y ^ x ^ ((x `|` z) `<<` 1);
        state.[column]     <- z ^ y ^((x & y) `<<` 3);
        column <- column + 1;
      }
      if (round %% 4 = 0) { 
        x <- state.[0];  
        y <- state.[1];
        state.[0] <- y;
        state.[1] <- x;

        x <- state.[2];
        y <- state.[3];
        state.[2] <- y;
        state.[3] <- x;
      }

      if (round %% 4 = 2) { 
        x <- state.[0]; 
        y <- state.[2];
        state.[0] <- y;
        state.[2] <- x;

        x <- state.[1];
        y <- state.[3];
        state.[1] <- y;
        state.[3] <- x;
      }

      if (round %% 4 = 0) state.[0] <- state.[0] ^ (Ox9e377900 ^ ofint round);
      
      round <- round - 1;
    }
    return state;
  }
}.

module Gimli_ref = {
  module R = {
    proc rotate (x : u32, bits : int) : u32 = {
      return rol32 x bits;
    }
  }
  include Gimli_gen(R)
}.

module Gimli_ref1 = {
  module R = {
    proc rotate (x : u32, bits : int) : u32 = {
      return (x `<<` bits) ^ (x `>>` (32 - bits));
    }
  }
  include Gimli_gen(R)
}.

equiv rotate_ref_ref1 : Gimli_ref.R.rotate ~ Gimli_ref1.R.rotate : ={x,bits} /\ 0 <= bits{1} < 32 ==> ={res}.
proof. by proc; auto => &m1 &m2 /> ??; rewrite rol32_xor. qed. 

equiv Gimli_ref_ref1 : Gimli_ref.gimli ~ Gimli_ref1.gimli : ={state} ==> ={res}.
proof.
  proc.
  while (={round, state});last by auto.
  sim; while (={round, state, column}); last by auto.
  sim; do 2! (call rotate_ref_ref1; sim />).
qed.

(* ------------------------------------------------------------------- *)
op rotate (r: u128) (count : int) = (r `<<` count) ^ (r `>>` (32 - count)).

module type Rot24 = {
  proc rotate (x:u128) : u128
}.

module Gimli_vec_gen (R:Rot24) = { 
  proc gimli (x : u128, y: u128, z : u128) = {
    var a, b, c, d, e : u128;
    var m : u32;
    var round, pattern : int;
(*    var w0, w1, w2, w3 : u32; *)

 (* x = of32 state.[0] state.[1] state.[2] state.[3];  
    y = of32 state.[4] state.[5] state.[6] state.[7];  
    z = of32 state.[8] state.[9] state.[10] state.[11]; *)

    round = 24;
    while (0 < round) { 
      x <@ R.rotate(x);
      y <- rotate y 9;
      z <- rotate z 0;

      a <- z `<<` 1;
      b <- y & z;
      c <- b `<<` 2;
      d <- x ^ a;
      e <- d ^ c;

      a <- x `|` z;
      b <- a `<<` 1;
      c <- y ^ x;
      d <- c ^ b;

      a <- x & y;
      b <- a `<<` 3;
      c <- z ^ y;

      x <- c ^ b;
      y <- d;
      z <- e;

      if (round %% 4 = 0) { 
        pattern <- shuffle 2 3 0 1; 
        x <- shuffle4_u32 x pattern;
      }

      if (round %% 4 = 2) { 
        pattern <- shuffle 1 0 3 2;
        x <- shuffle4_u32 x pattern;
      }

      if (round %% 4 = 0) { 
        m <- Ox9e377900 ^ ofint round;
        a <- zeroextend m;
        x <- x ^ a;
      }
      
      round <- round - 1;
    }
    
 (*   (w0,w1,w2,w3) =  to32 x;
    state.[0] = w0;
    state.[1] = w1;
    state.[2] = w2;
    state.[3] = w3;
    (w0,w1,w2,w3) =  to32 y;
    state.[4] = w0;
    state.[5] = w1;
    state.[6] = w2;
    state.[7] = w3;
    (w0,w1,w2,w3) =  to32 z;
    state.[8] = w0;
    state.[9] = w1;
    state.[10] = w2;
    state.[11] = w3; *)

    return (x,y,z);
  }

}.

module Gimli_vec1 = {
  module R = {
    proc rotate (x:u128) = {
      return rotate x 24;
    }
  }
  include Gimli_vec_gen(R)
}.


equiv ref1_vec1 : Gimli_ref1.gimli ~ Gimli_vec1.gimli : 
   (of32 state.[0] state.[1] state.[2]  state.[3] ){1} = x{2} /\
   (of32 state.[4] state.[5] state.[6]  state.[7] ){1} = y{2} /\
   (of32 state.[8] state.[9] state.[10] state.[11]){1} = z{2} 
   ==>
   (of32 res.[0] res.[1] res.[2]  res.[3] ){1} = res.`1{2} /\
   (of32 res.[4] res.[5] res.[6]  res.[7] ){1} = res.`2{2} /\
   (of32 res.[8] res.[9] res.[10] res.[11]){1} = res.`3{2}.
proof.
  proc; inline * => /=.
  while (#pre /\ ={round});last by auto.
  unroll for {1} 2.
  wp;skip => &m1 &m2 [#].
  by cbv delta => 4!<- _ _; cbv delta => />.
qed.


