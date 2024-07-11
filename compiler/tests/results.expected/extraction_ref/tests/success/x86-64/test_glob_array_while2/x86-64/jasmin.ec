require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array4.
require import WArray32.

abbrev glob_t = Array4.of_list witness [W64.of_int 0; W64.of_int 1; W64.of_int 2; W64.of_int 3].


module M = {
  proc sum (x:W64.t) : W64.t = {
    
    var r:W64.t;
    var i:W64.t;
    var gt1:W64.t Array4.t;
    gt1 <- witness;
    r <- (W64.of_int 0);
    i <- (W64.of_int 0);
    gt1 <- glob_t;
    
    while ((i \ult (W64.of_int 4))) {
      r <- (r + gt1.[(W64.to_uint i)]);
      i <- (i + (W64.of_int 1));
    }
    return (r);
  }
}.

