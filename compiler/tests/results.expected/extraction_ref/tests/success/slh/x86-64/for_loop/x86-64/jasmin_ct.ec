require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc main (p:W64.t) : unit = {
    var aux_0: int;
    var aux: W64.t;
    
    var msf:W64.t;
    var i:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    msf <- aux;
    leakages <- LeakFor(0,10) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 10) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- update_msf (i < 10) msf;
      msf <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- protect_64 p msf;
      p <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int i);
      leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int i)))]) :: leakages;
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int i))) (aux);
      i <- i + 1;
    }
    return ();
  }
}.

