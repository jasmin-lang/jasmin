require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2 Array8.
require import WArray8.



module M = {
  proc main (x:W32.t, y:W32.t) : W32.t = {
    var aux_1: W8.t Array8.t;
    var aux_0: W8.t Array8.t;
    
    var t1:W32.t Array2.t;
    var pt1:W32.t Array2.t;
    var t2:W32.t Array2.t;
    var pt2:W32.t Array2.t;
    var aux:W32.t;
    pt1 <- witness;
    pt2 <- witness;
    t1 <- witness;
    t2 <- witness;
    pt1 <- t1;
    pt2 <- t2;
    (pt1, pt2) <- swap_ pt1 pt2;
    aux <- (W32.of_int 0);
    pt1.[0] <- aux;
    aux <- (W32.of_int 1);
    pt1.[1] <- aux;
    aux <- (W32.of_int 0);
    pt2.[0] <- aux;
    aux <- (W32.of_int 1);
    pt2.[1] <- aux;
    (pt1, pt2) <- swap_ pt1 pt2;
    (x, y) <- swap_ x y;
    aux <- pt1.[0];
    x <- (x + aux);
    aux <- pt1.[1];
    x <- (x + aux);
    aux <- pt2.[0];
    x <- (x + aux);
    aux <- pt2.[1];
    x <- (x + aux);
    t1 <- pt1;
    t2 <- pt2;
    aux <- t1.[0];
    x <- (x + aux);
    aux <- t1.[1];
    x <- (x + aux);
    aux <- t2.[0];
    x <- (x + aux);
    aux <- t2.[1];
    x <- (x + aux);
    x <- x;
    return (x);
  }
}.

