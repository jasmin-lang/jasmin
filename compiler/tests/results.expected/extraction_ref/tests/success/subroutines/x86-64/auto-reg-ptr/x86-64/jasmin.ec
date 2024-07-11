require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray16.

abbrev g = Array2.of_list witness [W64.of_int 1; W64.of_int 0].


module M = {
  proc load (p:W64.t Array2.t, i:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r <- p.[(W64.to_uint i)];
    return (r);
  }
  
  proc main (z:W64.t) : W64.t = {
    var aux: int;
    
    var result:W64.t;
    var i:int;
    var stk:W64.t Array2.t;
    var n:W64.t;
    stk <- witness;
    i <- 0;
    while (i < 2) {
      stk.[i] <- z;
      i <- i + 1;
    }
    n <- (W64.of_int 0);
    n <@ load (g, n);
    result <@ load (stk, n);
    return (result);
  }
}.

