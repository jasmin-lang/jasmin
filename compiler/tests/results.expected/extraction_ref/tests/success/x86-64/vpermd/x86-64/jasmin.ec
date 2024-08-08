require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_vpermd (tmp:W64.t) : unit = {
    
    var t0:W256.t;
    var t1:W256.t;
    
    t0 <- set0_256 ;
    t1 <- set0_256 ;
    t0 <- VPERMD t0 t1;
    t0 <- VPERMD t0 (loadW256 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))));
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (t0);
    return ();
  }
}.

