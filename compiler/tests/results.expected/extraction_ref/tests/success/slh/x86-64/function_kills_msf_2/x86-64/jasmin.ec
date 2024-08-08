require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (x:W64.t) : unit = {
    
    
    
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (x + (W64.of_int 0))) (x);
    return ();
  }
  
  proc main (x:W64.t, r:W64.t) : W64.t = {
    
    var ms:W64.t;
    
    ms <- init_msf ;
    f (x);
    r <- protect_64 r ms;
    r <- r;
    return (r);
  }
}.

