require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc neg (x:W32.t) : W32.t = {
    
    
    
    x <- x;
    x <- (- x);
    return (x);
  }
}.

