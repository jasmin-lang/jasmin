require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc imm256 (zero256:W256.t, zero128:W128.t, c:int) : W256.t = {
    var aux: int;
    
    var r:W256.t;
    var t:W128.t;
    var j:int;
    var i:int;
    var n:W64.t;
    
    r <- zero256;
    t <- zero128;
    i <- 0;
    while (i < 2) {
      j <- 0;
      while (j < 2) {
        n <- (truncateu64 (((W256.of_int c) `>>` (W8.of_int (64 * ((2 * i) + j)))) `&` (((W256.of_int 1) `<<` (W8.of_int 64)) - (W256.of_int 1))));
        t <- VPINSR_2u64 t n (W8.of_int j);
        j <- j + 1;
      }
      r <- VINSERTI128 r t (W8.of_int i);
      i <- i + 1;
    }
    return (r);
  }
  
  proc test (p:W64.t) : unit = {
    
    var z256:W256.t;
    var z128:W128.t;
    var x:W256.t;
    
    z256 <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    z128 <- (truncateu128 z256);
    x <@ imm256 (z256, z128, 77708886481439537502114023296838182342452070989719098857970983598064258152311);
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (x);
    return ();
  }
}.

