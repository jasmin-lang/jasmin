require import SmtMap Int List FSet.

type Zp.

op zero : Zp.
op one : Zp.
op ( + ) : Zp -> Zp -> Zp.
op ( * ) : Zp -> Zp -> Zp.

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

(***********************************************)
(********* Reference implementation ************)

type Zp_msg = (int,Zp) fmap. (* an array *)

op ref (m : Zp_msg) (n : int) r =
  foldl (fun h i => (h + oget m.[i]) * r) zero (iota_ 0 n).

lemma ref0 m r : ref m 0 r = zero.
proof. by rewrite /ref iota0. qed.

lemma refS m n r : 0 <= n =>
  ref m (n + 1) r = (ref m n r + oget m.[n]) * r.
proof. by move=> ge0_n; rewrite /ref iotaSr // -cats1 foldl_cat. qed.

hint simplify ref0.
hint simplify refS.

module Poly1305_Ref = {
   var r : Zp

   proc fold(m : Zp_msg) = {
       var h,n,i;

       n <- size (elems (fdom m));
       i <- 0;
       h <- zero;

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
   var r : Zp

   proc fold(m : Zp_msg) = {
       var h,n,i;

       n <- size (elems (fdom m));
       i <- 0;
       h <- zero;

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
   var r : Zp

   proc fold(m : Zp_msg) = {
       var h,n,i;
       var h1,h2,h3,h4;
       var r2,r3,r4;

       n <- size (elems (fdom m));
       i <- 0;
       h <- zero;

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
lemma ref_ok m0 :
  hoare [ Poly1305_Ref.fold :
    m = m0 ==> res = ref m0 (size (elems (fdom m0))) Poly1305_Ref.r ].
proof.
proc; sp.
conseq (_ :
      0 <= i /\ i <= n /\ h = ref m i Poly1305_Ref.r
  ==> h = ref m n Poly1305_Ref.r) => />.
+ by move=> /> &hr; rewrite size_ge0.
while (#pre); auto => />.
+ by move=> &hr /= ge0i; rewrite refS //#.
+ smt().
qed.

(* -------------------------------------------------------------------- *)
lemma ref_ll : islossless Poly1305_Ref.fold.
proof. by islossless; while true (n-i) => *; auto => /#. qed.

(* -------------------------------------------------------------------- *)
lemma ref_ok_ll m0 :
  phoare [ Poly1305_Ref.fold :
    m = m0 ==> res = ref m0 (size (elems (fdom m0))) Poly1305_Ref.r ] = 1%r.
proof. by conseq ref_ll (ref_ok m0). qed.

(* -------------------------------------------------------------------- *)
lemma hop1_ok m0 :
  hoare [ Poly1305_Hop1.fold :
    m = m0 ==> res = ref m0 (size (elems (fdom m0))) Poly1305_Hop1.r ].
proof.
proc; sp.
conseq (_ :
      i = 0 /\ 0 <= i /\ i <= n /\ h = ref m i Poly1305_Hop1.r
  ==> h = ref m n Poly1305_Hop1.r) => />.
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
  by rewrite (refS _ 1) // (refS _ 0) // ref0 add0m /#.
by while (#pre) => //; auto; smt(refS).
qed.

(* -------------------------------------------------------------------- *)
lemma hop1_ll : islossless Poly1305_Hop1.fold.
proof. islossless.
+ by while true (n-i) => //= *; auto => /#.
+ by while true (n-i) => //= *; auto => /#.
qed.

(* -------------------------------------------------------------------- *)
lemma hop1_ok_ll m0 :
  phoare [ Poly1305_Hop1.fold :
    m = m0 ==> res = ref m0 (size (elems (fdom m0))) Poly1305_Hop1.r ] = 1%r.
proof. by conseq hop1_ll (hop1_ok m0). qed.

(* -------------------------------------------------------------------- *)
lemma ref_hop1 :
  equiv [Poly1305_Ref.fold ~ Poly1305_Hop1.fold :
    ={arg} /\ Poly1305_Ref.r{1} = Poly1305_Hop1.r{2} ==> ={res}
  ].
proof.                          (* WTF? *)
proc*; exists* m{1}, m{2}; elim* => m1 m2.
call {1} (_ : m = m1 ==> res = ref m1 (size (elems (fdom m1))) Poly1305_Ref.r).
* by conseq ref_ll (ref_ok m1).
call {2} (_ : m = m2 ==> res = ref m2 (size (elems (fdom m2))) Poly1305_Hop1.r).
* by conseq hop1_ll (hop1_ok m2).
by auto.
qed.
