require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array4.
require import WArray32.



module M = {
  proc mul5 (x:W64.t) : W64.t = {
    var aux: int;
    
    var i:int;
    var t:W64.t Array4.t;
    t <- witness;
    i <- 0;
    while (i < 4) {
      t.[i] <- x;
      i <- i + 1;
    }
    i <- 0;
    while (i < 4) {
      x <- (x + t.[i]);
      i <- i + 1;
    }
    return (x);
  }
  
  proc main (in_0:W64.t) : W64.t = {
    
    var r:W64.t;
    var x:W64.t;
    
    x <- in_0;
    x <@ mul5 (x);
    x <@ mul5 (x);
    x <@ mul5 (x);
    r <- x;
    return (r);
  }
}.

