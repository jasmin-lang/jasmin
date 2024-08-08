require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc main () : W64.t = {
    
    var a:W64.t;
    var s:W64.t Array1.t;
    var p:W64.t Array1.t;
    p <- witness;
    s <- witness;
    s.[0] <- (W64.of_int 42);
    p <- s;
    a <- s.[0];
    return (a);
  }
}.

