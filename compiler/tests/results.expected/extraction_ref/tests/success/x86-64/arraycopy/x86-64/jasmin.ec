require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array4.
require import WArray32.



module M = {
  proc test (x:W64.t) : W64.t = {
    var aux: int;
    
    var q:W64.t;
    var i:int;
    var s:W64.t Array4.t;
    var r:W64.t Array4.t;
    r <- witness;
    s <- witness;
    i <- 0;
    while (i < 4) {
      s.[i] <- x;
      i <- i + 1;
    }
    r <- copy_64 s;
    q <- x;
    i <- 0;
    while (i < 4) {
      q <- (q + r.[i]);
      i <- i + 1;
    }
    return (q);
  }
}.

