require import AllCore SmtMap Int IntDiv List FSet.
require import Ring.
import IntID.

(* We have a ring *)

clone import ComRing as Zp.

instance ring with Zp.t
  op rzero = Zp.zeror
  op rone  = Zp.oner
  op add   = Zp.(+)
  op opp   = Zp.([-])
  op mul   = Zp.( * )
  op expr  = Zp.exp

  proof oner_neq0 by apply Zp.oner_neq0 
  proof addr0     by apply Zp.addr0
  proof addrA     by apply Zp.addrA
  proof addrC     by apply Zp.addrC
  proof addrN     by apply Zp.addrN
  proof mulr1     by apply Zp.mulr1
  proof mulrA     by apply Zp.mulrA
  proof mulrC     by apply Zp.mulrC
  proof mulrDl    by apply Zp.mulrDl
  proof expr0     by apply Zp.expr0
  proof exprS     by apply Zp.exprS.

(* 


print ZP.


type Zp.

op zero : Zp.
op one : Zp.
op ( + ) : Zp -> Zp -> Zp.
op ( * ) : Zp -> Zp -> Zp.
op [-] : Zp -> Zp.
op 



type Rep.

op decode : Rep -> Zp.
op endoce : Zp -> Rep.

op add : Rep -> Rep -> Rep.
op mul_mod : Rep -> Rep -> Rep.

op safe_mul : Rep -> Rep -> bool.
op safe_add : Rep -> Rep -> bool.

axiom addm0 x : x + zero = x.
axiom add0m x : zero + x = x.

axiom add_correct x y :
   safe_add x y =>
     decode (add x y) = (decode x) + (decode y).

axiom mul_correct x y :
   safe_mul x y => 
     decode (mul_mod x y) = (decode x) * (decode y).
*)
(***********************************************)
(********* Reference implementation ************)

type Zp_msg = (int,Zp.t) fmap. (* an array *)

op ref (m : Zp_msg) (n : int) r =
  foldl (fun h i => (h + oget m.[i]) * r) zeror (iota_ 0 n).

lemma ref0 m r : ref m 0 r = zeror.
proof. by rewrite /ref iota0. qed.

lemma refS m n r : 0 <= n =>
  ref m (n + 1) r = (ref m n r + oget m.[n]) * r.
proof. by move=> ge0_n; rewrite /ref iotaSr // -cats1 foldl_cat. qed.

hint simplify ref0.
hint simplify refS.

module Poly1305_Ref = {

   proc fold(r:Zp.t, m : Zp_msg) = {
       var h,n,i;

       n <- size (elems (fdom m));
       i <- 0;
       h <- zeror;

       while (i < n) {
         h <- (h + oget m.[i]) * r;
         i <- i + 1;
       }
       return h;
   }
}.

(***********************************************)
(******************* Unfold ********************)
module Poly1305_Hop1 = {

   proc fold(r:Zp.t, m : Zp_msg) = {
       var h,n,i;

       n <- size (elems (fdom m));
       i <- 0;
       h <- zeror;

       (* we will go in four parallel tracks,
          4 steps at a time but need at least 
          extra 4+delta to merge *)
       if (8 <= n - i) {
          h <- (oget (m.[0])) * r;
          h <- (h + oget (m.[1])) * r;
          h <- (h + oget (m.[2])) * r;
          h <- (h + oget (m.[3])) * r;
          i <- 4;

          (* Can take four more ? *)
          while (8 <= n - i) {
             h <- (h + oget (m.[i])) * r;
             h <- (h + oget (m.[i+1])) * r;
             h <- (h + oget (m.[i+2])) * r;
             h <- (h + oget (m.[i+3])) * r;
             i <- i + 4;
          }

          (* These will be needed to merge *)
          h <- (h + oget (m.[i])) * r;
          h <- (h + oget (m.[i+1])) * r;
          h <- (h + oget (m.[i+2])) * r;
          h <- (h + oget (m.[i+3])) * r;
          i <- i + 4;
       }

       (* Leftovers *)
       while (i < n) {
          h <- (h + oget (m.[i])) * r;
          i <- i + 1;
       }

       return h;
   }
}.

(* Parallel tracks *)

module Poly1305_Hop2 = {

   proc fold(r : Zp.t, m : Zp_msg) = {
       var h,n,i;
       var h1,h2,h3,h4;
       var r2,r3,r4;

       n <- size (elems (fdom m));
       i <- 0;
       h <- zeror;

       (* we will go in four parallel tracks,
          4 steps at a time but need at least 
          extra 4+delta to merge *)
       if (8 <= n - i) {

          r2 <- r * r;
          r3 <- r2 * r;
          r4 <- r2 * r2;         

          h1 <- (oget (m.[0])) * r4;
          h2 <- (oget (m.[1])) * r4;
          h3 <- (oget (m.[2])) * r4;
          h4 <- (oget (m.[3])) * r4;
          i <- 4;

          (* Invariant: h*r4 = (h1*r4 + h2*r3 + h3*r2 + h4*r) *)

          (* Can take four more ? *)
          while (8 <= n - i) {
             h1 <- (h1 + oget (m.[i])) * r4;
             h2 <- (h2 + oget (m.[i+1])) * r4;
             h3 <- (h3 + oget (m.[i+2])) * r4;
             h4 <- (h4 + oget (m.[i+3])) * r4;
             i <- i + 4;
          }

          (* Invariant: h*r4 = (h1*r4 + h2*r3 + h3*r2 + h4*r) *)

          (* Merging is done by setting shifts right *)
          h1 <- (h1 + oget (m.[i])) * r4;
          h2 <- (h2 + oget (m.[i+1])) * r3;
          h3 <- (h3 + oget (m.[i+2])) * r2;
          h4 <- (h4 + oget (m.[i+3])) * r;
          i <- i + 4;

          h <- h1 + h2 + h3 + h4;
       }

       (* Leftovers *)
       while (i < n) {
          h <- (h + oget (m.[i])) * r;
          i <- i + 1;
       }

       return h;
   }
}.

(* -------------------------------------------------------------------- *)
lemma ref_ok m0 r0 :
  hoare [ Poly1305_Ref.fold :
    m = m0 /\ r = r0 ==> res = ref m0 (size (elems (fdom m0))) r0 ].
proof.
proc; sp.
conseq (_ :
      0 <= i /\ i <= n /\ h = ref m i r
  ==> h = ref m n r) => />.
+ by move=> /> &hr; rewrite size_ge0.
while (#pre); auto => />.
+ by move=> &hr /= ge0i; rewrite refS //#.
+ smt().
qed.

(* -------------------------------------------------------------------- *)
lemma ref_ll : islossless Poly1305_Ref.fold.
proof. by islossless; while true (n-i) => *; auto => /#. qed.

(* -------------------------------------------------------------------- *)
lemma ref_ok_ll m0 r0 :
  phoare [ Poly1305_Ref.fold :
    m = m0 /\ r = r0 ==> res = ref m0 (size (elems (fdom m0))) r0 ] = 1%r.
proof. by conseq ref_ll (ref_ok m0 r0). qed.

(* -------------------------------------------------------------------- *)
lemma hop1_ok m0 r0:
  hoare [ Poly1305_Hop1.fold :
    m = m0 /\ r = r0 ==> res = ref m0 (size (elems (fdom m0))) r0 ].
proof.
proc; sp.
conseq (_ :
      i = 0 /\ 0 <= i /\ i <= n /\ h = ref m i r
  ==> h = ref m n r) => />.
+ by move=> /> &hr; rewrite size_ge0.
seq 1 : #[2:]pre; [if => //|]; last first.
+ while (#pre); auto => />.
  * by move=> &hr /= ge0i; rewrite refS //#.
  * smt().
seq 6 : (#post /\ i <= n - 4); last first.
+ by auto => />; smt(refS).
seq 5 : #post; first auto => />.
  (* FIXME: hint rewrite should work here *)
+ move=> &hr; rewrite (refS _ 3) // (refS _ 2) //.
  by rewrite (refS _ 1) // (refS _ 0) // ref0 add0r /#.
by while (#pre) => //; auto; smt(refS).
qed.

(* -------------------------------------------------------------------- *)
lemma hop1_ll : islossless Poly1305_Hop1.fold.
proof. islossless.
+ by while true (n-i) => //= *; auto => /#.
+ by while true (n-i) => //= *; auto => /#.
qed.

(* -------------------------------------------------------------------- *)
lemma hop1_ok_ll m0 r0 :
  phoare [ Poly1305_Hop1.fold :
    m = m0 /\ r = r0 ==> res = ref m0 (size (elems (fdom m0))) r0 ] = 1%r.
proof. by conseq hop1_ll (hop1_ok m0 r0). qed.

(* -------------------------------------------------------------------- *)
lemma ref_hop1 :
  equiv [Poly1305_Ref.fold ~ Poly1305_Hop1.fold :
    ={m,r} ==> ={res}
  ].
proof.                          
proc*; exists* m{1}, r{1}; elim* => m1 r1.
call {1} (ref_ok_ll m1 r1); call {2} (hop1_ok_ll m1 r1); auto => />. (* WTF *)
by move=> &1 &2 !->.
qed.

(* -------------------------------------------------------------------- *)
(* Try to prove the equivalence between hop1 and hop2 using equiv       *)

equiv Hop1 : Poly1305_Ref.fold ~ Poly1305_Hop1.fold : 
                   ={m,r} ==> ={res}.
proof.
  proc.
  seq 3 3 : (={m,r,n,h,i} /\ i{1} = 0 /\ h{1} = Zp.zeror); 1: by auto.
  if{2}; last by sim.
  rcondt{1} 1; 1: by move=> &1;auto => /#.
  rcondt{1} 3; 1: by move=> &1;auto => /#.
  rcondt{1} 5; 1: by move=> &1;auto => /#.
  rcondt{1} 7; 1: by move=> &1;auto => /#.
  seq 8 5 : (={m,r,n,h,i} /\ i{2} = 4 /\ (8 <=  n){2}).
  + by auto => /> &m2 ?; ring.
  splitwhile{1} 1 : (8 <= n - i \/ ! (4 %| i)).
  seq 1 1 : (={m,r,n,h,i} /\ (4 <= n - i < 8){2}).
  + async while [ (fun r => i%r < r), (i{1}+4)%r ] 
                [ (fun r => i%r < r), (i{2}+4)%r ] 
                ( (8 <= n - i \/ ! (4 %| i)){1} /\ (8 <= n - i){2})
                (!(8 <= n - i){2}) :
                (={m,r,n,h,i} /\ 4 %| i{2} /\ 4 <= (n - i){2}).
    + by move=> /> /#.
    + by move=> /> /#.
    + by move=> /> /#.        
    + by move=> &m2;exfalso => &m1 [#] !->> /#.
    + by move=> &m2;exfalso => &m1 [#] !->> /#.
    + move=> v1 v2 /=.
      rcondt{2} 1;1: by auto => /> /#.
      rcondf{2} 6;1: by auto => /> /#.
      rcondt{1} 1;1: by auto => /> /#.
      rcondt{1} 3. 
      + move=> &m1;auto => /> hd h4 [#] h{h} h8;split; 2: smt().
        split;[smt() | right].
        apply /negP => /(dvdzB _ _ _ hd).
        by rewrite (_: i{m1} - (i{m1} + 1) = -1) //; 1:ring.
      rcondt{1} 5. 
      + move=> &m1;auto => /> hd h4 [#] h{h} h8;split; 2: smt().
        split;[smt() | right].
        apply /negP => /(dvdzB _ _ _ hd).
        by rewrite (_: i{m1} - (i{m1} + 1 + 1) = -2) //; 1:ring.
      rcondt{1} 7. 
      + move=> &m1;auto => /> hd h4 [#] h{h} h8;split; 2: smt().
        split;[smt() | right].
        apply /negP => /(dvdzB _ _ _ hd).
        by rewrite (_: i{m1} - (i{m1} + 1 + 1 + 1) = -3) //; 1:ring.
      rcondf{1} 9; 1: by move=> &m1;auto => /> /#.
      auto => /> &m2 hd hle h{h} h8;split; 1: smt().
      split; 2: smt().
      by apply dvdzD.
    + by islossless; while true (n-i); auto => /#.
    + by islossless; while true (n-i); auto => /#.
    by auto => /> /#.
  rcondt{1} 1; 1: by move=> &1;auto => /#.
  rcondt{1} 3; 1: by move=> &1;auto => /#.
  rcondt{1} 5; 1: by move=> &1;auto => /#.
  rcondt{1} 7; 1: by move=> &1;auto => /#.
  sim;auto => /> /#.
qed.

(* -------------------------------------------------------------------- *)
equiv Hop2 : Poly1305_Hop1.fold ~ Poly1305_Hop2.fold : ={m,r} ==> ={res}.
proof.
  proc.
  while (={h,i,n,m,r}); 1: by sim.
  seq 3 3 : (={h,i,n,m,r}); 1: by sim.
  if => //; wp.
  while (={i,n,m,r} /\ h{1}*r4{2} = (h1*r4 + h2*r3 + h3*r2 + h4*r){2} /\
         (r4 = exp r 4 /\ r3 = exp r 3 /\ r2 = exp r 2) {2}).
  + by wp;skip => /> &m1 &m2 heq hle; ring heq.
  wp;skip => /> &m2 hle;split.
  + by do !(split;try by ring).
  by move=> h h1 h2 h3 h4 i _ _ heq _ _ _;ring heq.
qed.

