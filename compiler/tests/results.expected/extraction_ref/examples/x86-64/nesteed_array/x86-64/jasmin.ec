require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array256.
require import WArray2048.



module M = {
  proc foo (x:W64.t) : W64.t = {
    var aux: int;
    
    var r:W64.t;
    var j:int;
    var i:int;
    var a:W64.t Array256.t;
    a <- witness;
    i <- 0;
    while (i < 32) {
      j <- 0;
      while (j < 8) {
        a.[((8 * i) + j)] <- x;
        j <- j + 1;
      }
      i <- i + 1;
    }
    r <- (W64.of_int 0);
    i <- 0;
    while (i < 256) {
      r <- (r + a.[i]);
      i <- i + 1;
    }
    return (r);
  }
}.

