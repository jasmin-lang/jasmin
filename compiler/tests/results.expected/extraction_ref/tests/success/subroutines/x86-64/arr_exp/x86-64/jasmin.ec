require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray16.



module M = {
  proc test (t:W64.t Array2.t) : W64.t Array2.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 2) {
      t.[i] <- (t.[i] + (W64.of_int 1));
      i <- i + 1;
    }
    return (t);
  }
  
  proc main () : W64.t = {
    var aux: int;
    
    var r:W64.t;
    var i:int;
    var t:W64.t Array2.t;
    t <- witness;
    i <- 0;
    while (i < 2) {
      t.[i] <- (W64.of_int i);
      i <- i + 1;
    }
    t <@ test (t);
    t.[0] <- (t.[0] + t.[1]);
    r <- t.[0];
    return (r);
  }
}.

