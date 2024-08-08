require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_pmaddwd (rp:W64.t) : unit = {
    
    var f0:W256.t;
    var f1:W256.t;
    var f2:W256.t;
    var f3:W256.t;
    var t0:W128.t;
    var t1:W128.t;
    var t2:W128.t;
    var t3:W128.t;
    
    f0 <- set0_256 ;
    f1 <- set0_256 ;
    f2 <- VPMADDWD_256 f0 f1;
    f3 <- VPMADDWD_256 f2 (loadW256 Glob.mem (W64.to_uint (rp + (W64.of_int 0))));
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (rp + (W64.of_int 0))) (f3);
    t0 <- set0_128 ;
    t1 <- set0_128 ;
    t2 <- VPMADDWD_128 t0 t1;
    t3 <- VPMADDWD_128 t2 (loadW128 Glob.mem (W64.to_uint (rp + (W64.of_int 32))));
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (rp + (W64.of_int 32))) (t3);
    return ();
  }
}.

