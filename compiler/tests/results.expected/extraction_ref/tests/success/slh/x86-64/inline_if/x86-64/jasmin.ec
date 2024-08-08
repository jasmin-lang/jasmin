require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc main (x:W64.t) : W64.t = {
    
    var y:W64.t;
    var msf:W64.t;
    var b:bool;
    
    msf <- init_msf ;
    b <- true;
    if (b) {
      x <- (x + (W64.of_int 1));
    } else {
      
    }
    if ((! b)) {
      x <- (x + (W64.of_int 1));
    } else {
      
    }
    y <- x;
    y <- protect_64 y msf;
    return (y);
  }
}.

