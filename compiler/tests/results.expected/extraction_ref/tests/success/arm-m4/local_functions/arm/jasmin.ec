require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc inc (x:W32.t) : W32.t = {
    
    var y:W32.t;
    
    y <- x;
    y <- (y + (W32.of_int 1));
    return (y);
  }
  
  proc dec (x:W32.t) : W32.t = {
    
    var y:W32.t;
    
    y <- x;
    y <- (y - (W32.of_int 1));
    return (y);
  }
  
  proc main (a:W32.t) : W32.t = {
    
    var r:W32.t;
    
    r <@ inc (a);
    r <@ dec (r);
    return (r);
  }
}.

