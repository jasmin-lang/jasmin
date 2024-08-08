require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc foo (x:W256.t) : W256.t = {
    
    var y:W256.t;
    var msf:W64.t;
    
    msf <- init_msf ;
    y <- protect_256 x msf;
    return (y);
  }
}.

