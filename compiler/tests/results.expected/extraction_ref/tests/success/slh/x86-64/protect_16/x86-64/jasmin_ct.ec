require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc foo (p:W64.t) : unit = {
    var aux_0: W16.t;
    var aux: W64.t;
    
    var msf:W64.t;
    var x:W16.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    msf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W16.of_int 0);
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- protect_16 x msf;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux_0);
    return ();
  }
}.

