require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc id (x:W32.t) : W32.t = {
    
    
    
    x <- x;
    return (x);
  }
  
  proc whynot (a:W32.t) : W32.t = {
    
    
    
    a <@ id (a);
    return (a);
  }
}.

