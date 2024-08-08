require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc aux (x:W32.t) : W32.t = {
    
    var y:W32.t;
    
    y <- x;
    return (y);
  }
  
  proc main (a:W32.t) : W32.t = {
    
    
    
    a <@ aux (a);
    return (a);
  }
}.

