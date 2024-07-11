require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_vmovlpd (tmp:W64.t) : unit = {
    
    var x:W128.t;
    
    x <- set0_128 ;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (VMOVLPD x);
    return ();
  }
  
  proc vmovlpd_to_stack (x:W128.t) : W64.t = {
    
    var z:W64.t;
    var y:W64.t;
    
    y <- VMOVLPD x;
    z <- y;
    return (z);
  }
}.

