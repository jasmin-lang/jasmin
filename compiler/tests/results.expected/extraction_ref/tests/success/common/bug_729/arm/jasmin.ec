require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





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

