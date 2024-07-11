require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array5.
require import WArray20.



module M = {
  proc foo () : W32.t = {
    
    var z:W32.t;
    var x:W32.t Array5.t;
    x <- witness;
    x.[0] <- (W32.of_int 0);
    x.[1] <- (W32.of_int 0);
    x.[2] <- (W32.of_int 0);
    x.[3] <- (W32.of_int 0);
    x.[4] <- (W32.of_int 0);
    z <- x.[0];
    return (z);
  }
}.

