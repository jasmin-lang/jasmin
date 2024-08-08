require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc copy (dst:W64.t Array1.t, src:W64.t Array1.t) : W64.t Array1.t = {
    
    var tmp:W64.t;
    
    tmp <- src.[0];
    dst.[0] <- tmp;
    return (dst);
  }
  
  proc main (x:W64.t) : W64.t = {
    
    var result:W64.t;
    var a:W64.t Array1.t;
    var b:W64.t Array1.t;
    a <- witness;
    b <- witness;
    a.[0] <- x;
    b <@ copy (b, a);
    result <- b.[0];
    return (result);
  }
}.

