require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc zerofill (x:W64.t Array1.t) : W64.t Array1.t = {
    
    
    
    x.[0] <- (W64.of_int 0);
    return (x);
  }
  
  proc main () : W64.t = {
    
    var r:W64.t;
    var s:W64.t Array1.t;
    s <- witness;
    s <@ zerofill (s);
    r <- s.[0];
    return (r);
  }
}.

