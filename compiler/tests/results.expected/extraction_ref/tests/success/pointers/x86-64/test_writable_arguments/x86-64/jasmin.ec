require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc f (t:W64.t Array1.t) : W64.t Array1.t = {
    
    
    
    t.[0] <- (W64.of_int 1);
    return (t);
  }
  
  proc g () : W64.t = {
    
    var r:W64.t;
    var s:W64.t Array1.t;
    var t:W64.t Array1.t;
    s <- witness;
    t <- witness;
    t <- s;
    s <@ f (((0 <= 1) ? t : t));
    r <- s.[0];
    return (r);
  }
}.

