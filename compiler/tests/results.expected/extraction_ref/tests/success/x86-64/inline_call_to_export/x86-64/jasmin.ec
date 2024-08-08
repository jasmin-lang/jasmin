require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc sum (x:W64.t, y:W64.t) : W64.t = {
    
    var z:W64.t;
    
    z <- LEA_64 (x + y);
    return (z);
  }
}.

