require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_cqo (x:W64.t) : W64.t = {
    
    var r:W64.t;
    var u:W16.t;
    var v:W16.t;
    var y:W32.t;
    var z:W64.t;
    
    u <- (truncateu16 x);
    u <- CQO_16 u;
    v <- u;
    y <- (truncateu32 x);
    y <- CQO_32 y;
    v <- (v `|` (truncateu16 y));
    z <- x;
    z <- CQO_64 z;
    v <- (v `|` (truncateu16 z));
    r <- (zeroextu64 v);
    return (r);
  }
}.

