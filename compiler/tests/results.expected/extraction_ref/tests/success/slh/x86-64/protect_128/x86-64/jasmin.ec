require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc foo (x:W128.t) : W128.t = {
    
    var y:W128.t;
    var msf:W64.t;
    
    msf <- init_msf ;
    y <- protect_128 x msf;
    return (y);
  }
}.

