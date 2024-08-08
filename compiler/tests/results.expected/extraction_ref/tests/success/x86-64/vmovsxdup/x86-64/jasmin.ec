require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test (p:W64.t) : unit = {
    
    var a:W128.t;
    var b:W128.t;
    var x:W256.t;
    var y:W256.t;
    
    a <- VMOVSLDUP_128 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- VMOVSLDUP_128 a;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (b);
    a <- VMOVSHDUP_128 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    b <- VMOVSHDUP_128 a;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (b);
    x <- VMOVSLDUP_256 (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y <- VMOVSLDUP_256 x;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) ((truncateu128 y));
    x <- VMOVSHDUP_256 (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    y <- VMOVSHDUP_256 x;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) ((truncateu128 y));
    return ();
  }
}.

