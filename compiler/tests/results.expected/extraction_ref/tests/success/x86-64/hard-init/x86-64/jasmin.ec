require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (input:W64.t) : W64.t = {
    
    var result:W64.t;
    var b:bool;
    
    b <- (input = (W64.of_int 0));
    if (b) {
      result <- (W64.of_int 0);
    } else {
      
    }
    if ((! b)) {
      result <- (W64.of_int 1);
    } else {
      
    }
    return (result);
  }
}.

