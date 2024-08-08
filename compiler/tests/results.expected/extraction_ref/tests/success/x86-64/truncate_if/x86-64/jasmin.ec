require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc a (x:W64.t, y:W64.t) : W32.t = {
    
    var z:W32.t;
    
    z <- (truncateu32 x);
    z <- ((y \ult (W64.of_int 0)) ? (truncateu32 x) : z);
    return (z);
  }
  
  proc b (x:W64.t, y:W64.t) : W32.t = {
    
    var z:W32.t;
    
    z <- (truncateu32 x);
    z <- ((y \ult (W64.of_int 0)) ? (truncateu32 x) : z);
    return (z);
  }
}.

