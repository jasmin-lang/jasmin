require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array4.
require import WArray32.

abbrev glob_t = Array4.of_list witness [W64.of_int 0; W64.of_int 1; W64.of_int 2; W64.of_int 3].


module M = {
  proc sum (x:W64.t) : W64.t = {
    var aux: int;
    
    var r:W64.t;
    var i1:int;
    var gt1:W64.t Array4.t;
    var gt2:W64.t Array4.t;
    var i:W64.t;
    gt1 <- witness;
    gt2 <- witness;
    i1 <- 0;
    while (i1 < 4) {
      gt1.[i1] <- (W64.of_int i1);
      i1 <- i1 + 1;
    }
    gt2 <- gt1;
    r <- (W64.of_int 0);
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int 4))) {
      r <- (r + gt1.[(W64.to_uint i)]);
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int 4))) {
      r <- (r + gt2.[(W64.to_uint i)]);
      i <- (i + (W64.of_int 1));
    }
    return (r);
  }
}.

