require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_vpblendvb (rp:W64.t) : unit = {
    var aux_0: W128.t;
    var aux: W256.t;
    
    var f0:W256.t;
    var f1:W256.t;
    var m:W256.t;
    var h0:W128.t;
    var h1:W128.t;
    var n:W128.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- set0_256 ;
    f0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- set0_256 ;
    f1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- set0_256 ;
    m <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPBLENDVB_256 f0 f1 m;
    f0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- f0;
    leakages <- LeakAddr([(W64.to_uint (rp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (rp + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- set0_128 ;
    h0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- set0_128 ;
    h1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- set0_128 ;
    n <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPBLENDVB_128 h0 h1 n;
    h0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- h0;
    leakages <- LeakAddr([(W64.to_uint (rp + (W64.of_int 32)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (rp + (W64.of_int 32))) (aux_0);
    return ();
  }
}.

