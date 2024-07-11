require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray16.

abbrev glob_0 = Array2.of_list witness [W64.of_int 1; W64.of_int 2].


module M = {
  proc load (p:W64.t Array2.t) : W64.t = {
    
    var r:W64.t;
    
    r <- p.[0];
    return (r);
  }
  
  proc test () : W64.t = {
    
    var x:W64.t;
    
    x <@ load (glob_0);
    return (x);
  }
}.

