require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_vpermd (tmp:W64.t) : unit = {
    var aux: W256.t;
    
    var t0:W256.t;
    var t1:W256.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- set0_256 ;
    t0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- set0_256 ;
    t1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPERMD t0 t1;
    t0 <- aux;
    leakages <- LeakAddr([(W64.to_uint (tmp + (W64.of_int 0)))]) :: leakages;
    aux <- VPERMD t0 (loadW256 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))));
    t0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- t0;
    leakages <- LeakAddr([(W64.to_uint (tmp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (aux);
    return ();
  }
}.

