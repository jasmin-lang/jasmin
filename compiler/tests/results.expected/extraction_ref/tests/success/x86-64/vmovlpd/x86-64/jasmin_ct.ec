require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_vmovlpd (tmp:W64.t) : unit = {
    var aux_0: W64.t;
    var aux: W128.t;
    
    var x:W128.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- set0_128 ;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VMOVLPD x;
    leakages <- LeakAddr([(W64.to_uint (tmp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (tmp + (W64.of_int 0))) (aux_0);
    return ();
  }
  
  proc vmovlpd_to_stack (x:W128.t) : W64.t = {
    var aux: W64.t;
    
    var z:W64.t;
    var y:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- VMOVLPD x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- y;
    z <- aux;
    return (z);
  }
}.

