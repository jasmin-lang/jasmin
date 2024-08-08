require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc foo (x:W128.t, y:W128.t) : W256.t = {
    
    var z:W256.t;
    
    z <- zeroextu256(VPAND_128 x y);
    return (z);
  }
}.

