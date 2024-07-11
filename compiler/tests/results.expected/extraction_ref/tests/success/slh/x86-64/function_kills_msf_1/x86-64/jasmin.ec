require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f () : unit = {
    
    var x:W64.t;
    
    x <- (W64.of_int 0);
    if ((x = (W64.of_int 0))) {
      
    } else {
      
    }
    return ();
  }
  
  proc main (x:W64.t) : unit = {
    
    var msf:W64.t;
    
    msf <- init_msf ;
    f ();
    x <- protect_64 x msf;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (x + (W64.of_int 0))) ((W64.of_int 0));
    return ();
  }
}.

