require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc id (x:W32.t) : W32.t = {
    
    
    
    
    return (x);
  }
  
  proc main (a:W32.t) : W32.t = {
    
    var r:W32.t;
    
    r <- a;
    r <@ id (r);
    return (r);
  }
}.

