require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc nested_ifs (x:W64.t, y:W64.t, z:W64.t) : W64.t = {
    
    var r:W64.t;
    var i:W64.t;
    
    i <- (W64.of_int 0);
    if ((x \ult y)) {
      if ((y \ult z)) {
        r <- (W64.of_int 0);
      } else {
        if ((x \ult z)) {
          r <- (W64.of_int 1);
        } else {
          r <- (W64.of_int 2);
        }
      }
    } else {
      if ((x \ult z)) {
        r <- (W64.of_int 3);
      } else {
        if ((y \ult z)) {
          r <- (W64.of_int 4);
        } else {
          r <- (W64.of_int 5);
        }
      }
    }
    
    while ((i \ult (W64.of_int 0))) {
      i <- (i + (W64.of_int 1));
    }
    return (r);
  }
}.

