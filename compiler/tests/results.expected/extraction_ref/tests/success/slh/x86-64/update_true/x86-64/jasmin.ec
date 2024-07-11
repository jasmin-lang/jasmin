require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc main (x:W64.t) : W64.t = {
    
    var y:W64.t;
    var msf:W64.t;
    
    msf <- init_msf ;
    msf <- update_msf true msf;
    y <- x;
    y <- protect_64 y msf;
    return (y);
  }
}.

