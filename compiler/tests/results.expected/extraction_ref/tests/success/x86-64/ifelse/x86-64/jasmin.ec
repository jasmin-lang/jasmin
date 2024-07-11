require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test (x:W64.t, y:W64.t) : W64.t = {
    
    var result:W64.t;
    
    if ((x <> (W64.of_int 0))) {
      result <- x;
    } else {
      if ((y <> (W64.of_int 0))) {
        result <- y;
      } else {
        result <- (W64.of_int 0);
      }
    }
    return (result);
  }
}.

