require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray32.



module M = {
  proc xor (a:W256.t, b:W256.t) : W256.t = {
    
    var c:W256.t;
    
    c <- (a `^` b);
    return (c);
  }
  
  proc main (x:W256.t) : W256.t = {
    
    var a:W256.t Array1.t;
    a <- witness;
    a.[0] <- x;
    x <@ xor (a.[0], a.[0]);
    return (x);
  }
}.

