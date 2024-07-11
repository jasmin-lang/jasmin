require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc inc (x:W64.t) : W64.t = {
    
    
    
    x <- LEA_64 (x + (W64.of_int 1));
    return (x);
  }
  
  proc one () : W64.t = {
    
    var r:W64.t;
    
    r <@ inc ((W64.of_int 0));
    return (r);
  }
}.

