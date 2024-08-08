require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc foo () : W64.t = {
    
    var x:W64.t;
    var msf:W64.t;
    var msf1:W64.t;
    
    x <- (W64.of_int 0);
    msf <- init_msf ;
    x <- protect_64 x msf;
    msf <- mov_msf msf;
    x <- protect_64 x msf;
    msf1 <- mov_msf msf;
    x <- protect_64 x msf;
    x <- protect_64 x msf1;
    return (x);
  }
}.

