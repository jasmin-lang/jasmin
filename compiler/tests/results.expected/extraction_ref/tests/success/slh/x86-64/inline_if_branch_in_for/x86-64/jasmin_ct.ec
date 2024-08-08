require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc branch_in_loop (p:W64.t) : W64.t = {
    var aux_0: int;
    var aux: W64.t;
    
    var x:W64.t;
    var msf:W64.t;
    var i:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    msf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    x <- aux;
    leakages <- LeakFor(0,10) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 10) {
      leakages <- LeakCond((i < 5)) :: LeakAddr([]) :: leakages;
      if ((i < 5)) {
        leakages <- LeakAddr([]) :: leakages;
        aux <- (W64.of_int i);
        leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int i)))]) :: leakages;
        Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int i))) (aux);
        leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int i)))]) :: leakages;
        aux <- (x + (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int i)))));
        x <- aux;
      } else {
        leakages <- LeakAddr([]) :: leakages;
        aux <- (W64.of_int 10);
        leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int i)))]) :: leakages;
        Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int i))) (aux);
        leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int i)))]) :: leakages;
        aux <- (x + (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int i)))));
        x <- aux;
      }
      i <- i + 1;
    }
    return (x);
  }
}.

