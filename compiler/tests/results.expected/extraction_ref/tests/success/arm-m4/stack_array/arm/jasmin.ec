require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array4.
require import WArray16.



module M = {
  proc id_by_stack (x:W32.t) : W32.t = {
    
    var s:W32.t Array4.t;
    s <- witness;
    s.[1] <- x;
    x <- s.[1];
    return (x);
  }
}.

