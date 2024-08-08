require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array4.
require import WArray16.

abbrev g = Array4.of_list witness [W32.of_int 1; W32.of_int 2; W32.of_int 3; W32.of_int 4].


module M = {
  proc all_kinds () : W32.t = {
    var aux: int;
    
    var x:W32.t;
    var a:W32.t Array4.t;
    var b:W32.t Array4.t;
    var c:W32.t Array4.t;
    var d:W32.t Array4.t;
    var i:int;
    var p:W32.t Array4.t;
    var q:W32.t Array4.t;
    a <- witness;
    b <- witness;
    c <- witness;
    d <- witness;
    p <- witness;
    q <- witness;
    a <- copy_32 g;
    b <- copy_32 a;
    c <- copy_32 b;
    d <- copy_32 c;
    a <- copy_32 d;
    x <- (W32.of_int 0);
    i <- 0;
    while (i < 4) {
      x <- (x + a.[i]);
      i <- i + 1;
    }
    p <- c;
    q <- p;
    p <- copy_32 a;
    q <- copy_32 p;
    d <- copy_32 q;
    p <- copy_32 d;
    a <- copy_32 a;
    i <- 0;
    while (i < 4) {
      x <- (x + a.[i]);
      i <- i + 1;
    }
    return (x);
  }
}.

