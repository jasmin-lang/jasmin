require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc aux (x:W64.t) : W64.t = {
    
    
    
    
    return (x);
  }
  
  proc main (x:W64.t) : W64.t = {
    
    var result:W64.t;
    
    result <- x;
    result <@ aux (result);
    while (((W64.of_int 0) \ult x)) {
      result <@ aux (result);
      x <- (x - (W64.of_int 1));
      result <@ aux (result);
    }
    return (result);
  }
}.

