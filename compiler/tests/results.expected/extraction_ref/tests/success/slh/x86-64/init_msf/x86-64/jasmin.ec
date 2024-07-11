require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc foo () : W64.t = {
    
    var msf:W64.t;
    
    msf <- init_msf ;
    return (msf);
  }
  
  proc foo2 () : unit = {
    
    var  _0:W64.t;
    
     _0 <- init_msf ;
    return ();
  }
}.

