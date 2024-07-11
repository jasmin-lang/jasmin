require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test (x:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r <- x;
    if (((W64.of_int 5) \ult r)) {
      if (((W64.of_int 6) \ult r)) {
        
      } else {
        
      }
    } else {
      if (((W64.of_int 2) \ult r)) {
        
      } else {
        
      }
    }
    return (r);
  }
}.

