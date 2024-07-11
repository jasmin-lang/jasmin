require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc main (x:W32.t, y:W32.t) : W32.t = {
    
    
    
    (x, y) <- swap_ x y;
    x <- x;
    return (x);
  }
}.

