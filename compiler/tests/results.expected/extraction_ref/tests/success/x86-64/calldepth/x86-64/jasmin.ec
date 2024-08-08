require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f () : W64.t = {
    
    var res_0:W64.t;
    
    res_0 <- (W64.of_int 0);
    return (res_0);
  }
  
  proc g (x:W64.t) : W64.t = {
    
    var res_0:W64.t;
    
    if ((x = (W64.of_int 0))) {
      res_0 <- (W64.of_int 0);
    } else {
      res_0 <@ f ();
    }
    return (res_0);
  }
}.

