require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc foo (x:W64.t) : W64.t = {
    
    var r:W64.t;
    var msf:W64.t;
    var b:bool;
    
    msf <- init_msf ;
    b <- (x = x);
    if (b) {
      msf <- update_msf b msf;
    } else {
      msf <- update_msf (! b) msf;
    }
    r <- x;
    r <- protect_64 r msf;
    return (r);
  }
}.

