require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc load (p:W64.t) : W64.t = {
    
    var x:W64.t;
    
    x <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    return (x);
  }
  
  proc main (cptr:W64.t) : W64.t = {
    
    var result:W64.t;
    var tmp:W64.t;
    
    tmp <- cptr;
    result <@ load (tmp);
    result <- (result + tmp);
    return (result);
  }
}.

