require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray16.

abbrev g = Array2.of_list witness [W64.of_int 1; W64.of_int 2].


module M = {
  proc main () : W64.t = {
    
    var res_0:W64.t;
    var s:W64.t Array2.t;
    var r:W64.t Array2.t;
    r <- witness;
    s <- witness;
    s <- g;
    r <- s;
    res_0 <- r.[0];
    return (res_0);
  }
}.

