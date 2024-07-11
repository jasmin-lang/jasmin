require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.



abbrev r = W32.of_int 0.


module M = {
  proc fok (r_0:W32.t) : W32.t = {
    
    var x:W32.t;
    
    x <- r_0;
    return (x);
  }
  
  proc f (y:W32.t) : W32.t = {
    
    var x:W32.t;
    var y_0:W32.t;
    
    x <- y;
    if ((x = (W32.of_int 0))) {
      y_0 <- x;
      x <- y_0;
    } else {
      
    }
    return (x);
  }
  
  proc g (z:W32.t) : W32.t = {
    
    var x:W32.t;
    
    x <- z;
    return (x);
  }
}.

