require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_vpblendvb (rp:W64.t) : unit = {
    
    var f0:W256.t;
    var f1:W256.t;
    var m:W256.t;
    var h0:W128.t;
    var h1:W128.t;
    var n:W128.t;
    
    f0 <- set0_256 ;
    f1 <- set0_256 ;
    m <- set0_256 ;
    f0 <- VPBLENDVB_256 f0 f1 m;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (rp + (W64.of_int 0))) (f0);
    h0 <- set0_128 ;
    h1 <- set0_128 ;
    n <- set0_128 ;
    h0 <- VPBLENDVB_128 h0 h1 n;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (rp + (W64.of_int 32))) (h0);
    return ();
  }
}.

