require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array16.
require import WArray512.



module M = {
  proc foo () : W256.t = {
    var aux: int;
    
    var xmm0:W256.t;
    var i:int;
    var xmm:W256.t Array16.t;
    xmm <- witness;
    i <- 0;
    while (i < 16) {
      xmm.[i] <- set0_256 ;
      i <- i + 1;
    }
    i <- 0;
    while (i < 16) {
      xmm.[0] <- (xmm.[0] `^` xmm.[i]);
      i <- i + 1;
    }
    xmm0 <- xmm.[0];
    return (xmm0);
  }
}.

