require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc add (x:W32.t, y:W32.t) : W32.t = {
    
    var r:W32.t;
    
    r <- (x + y);
    return (r);
  }
  
  proc main (x:W32.t, y:W32.t) : W32.t = {
    
    var r2:W32.t;
    var r1:W32.t;
    
    r1 <@ add (x, y);
    r2 <- r1;
    return (r2);
  }
}.

