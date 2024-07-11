require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc imm256 (zero256:W256.t, zero128:W128.t, c:int) : W256.t = {
    var aux_1: int;
    var aux_2: W64.t;
    var aux_0: W128.t;
    var aux: W256.t;
    
    var r:W256.t;
    var t:W128.t;
    var j:int;
    var i:int;
    var n:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- zero256;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- zero128;
    t <- aux_0;
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
      j <- 0;
      while (j < 2) {
        leakages <- LeakAddr([]) :: leakages;
        aux <- (((W256.of_int c) `>>` (W8.of_int (64 * ((2 * i) + j)))) `&` (((W256.of_int 1) `<<` (W8.of_int 64)) - (W256.of_int 1)));
        n <- (truncateu64 aux);
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- VPINSR_2u64 t n (W8.of_int j);
        t <- aux_0;
        j <- j + 1;
      }
      leakages <- LeakAddr([]) :: leakages;
      aux <- VINSERTI128 r t (W8.of_int i);
      r <- aux;
      i <- i + 1;
    }
    return (r);
  }
  
  proc test (p:W64.t) : unit = {
    var aux_0: W128.t;
    var aux: W256.t;
    
    var z256:W256.t;
    var z128:W128.t;
    var x:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    z256 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- z256;
    z128 <- (truncateu128 aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <@ imm256 (z256, z128, 77708886481439537502114023296838182342452070989719098857970983598064258152311);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    return ();
  }
}.

