require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc one (a:W64.t Array1.t) : W64.t * W64.t Array1.t = {
    
    var result:W64.t;
    
    a.[0] <- (W64.of_int 1);
    result <- a.[0];
    return (result, a);
  }
  
  proc main () : W64.t = {
    
    var n:W64.t;
    var s:W64.t Array1.t;
    s <- witness;
    (n, s) <@ one (s);
    return (n);
  }
}.

