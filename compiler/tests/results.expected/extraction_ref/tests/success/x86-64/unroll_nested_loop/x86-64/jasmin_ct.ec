require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test (buffer:W64.t) : unit = {
    var aux: int;
    var aux_0: W8.t;
    
    var j:int;
    var i:int;
    
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakFor(0,(1 `<<` i)) :: LeakAddr([]) :: leakages;
      aux <- (1 `<<` i);
      j <- 0;
      while (j < aux) {
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (W8.of_int 1);
        leakages <- LeakAddr([(W64.to_uint (buffer + (W64.of_int ((16 * i) + j))))]) :: leakages;
        Glob.mem <- storeW8 Glob.mem (W64.to_uint (buffer + (W64.of_int ((16 * i) + j)))) (aux_0);
        j <- j + 1;
      }
      i <- i + 1;
    }
    return ();
  }
}.

