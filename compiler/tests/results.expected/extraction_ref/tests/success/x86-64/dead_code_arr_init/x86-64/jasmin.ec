require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc foo (x:W64.t) : W64.t = {
    
    var t:W64.t Array1.t;
    t <- witness;
    t <- witness;
    t <- witness;
    t <- witness;
    t.[0] <- x;
    x <- t.[0];
    return (x);
  }
}.

