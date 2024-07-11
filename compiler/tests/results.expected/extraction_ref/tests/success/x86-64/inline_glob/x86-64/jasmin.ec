require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray16.

abbrev g = Array2.of_list witness [W64.of_int 1; W64.of_int 2].


module M = {
  proc f (a:W64.t Array2.t) : W64.t = {
    
    var res_0:W64.t;
    
    res_0 <- a.[1];
    return (res_0);
  }
  
  proc main () : W64.t = {
    
    var res_0:W64.t;
    
    res_0 <@ f (g);
    return (res_0);
  }
}.

