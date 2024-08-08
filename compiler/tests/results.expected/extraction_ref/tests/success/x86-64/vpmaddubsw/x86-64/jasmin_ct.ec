require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_pmaddubsw (rp:W64.t) : unit = {
    var aux_0: W128.t;
    var aux: W256.t;
    
    var f0:W256.t;
    var f1:W256.t;
    var f2:W256.t;
    var t0:W128.t;
    var t1:W128.t;
    var t2:W128.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- set0_256 ;
    f0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- set0_256 ;
    f1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPMADDUBSW_256 f0 f1;
    f2 <- aux;
    leakages <- LeakAddr([(W64.to_uint (rp + (W64.of_int 0)))]) :: leakages;
    aux <- VPMADDUBSW_256 f2 (loadW256 Glob.mem (W64.to_uint (rp + (W64.of_int 0))));
    f0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- f0;
    leakages <- LeakAddr([(W64.to_uint (rp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (rp + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- set0_128 ;
    t0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- set0_128 ;
    t1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VPMADDUBSW_128 t0 t1;
    t2 <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (rp + (W64.of_int 32)))]) :: leakages;
    aux_0 <- VPMADDUBSW_128 t2 (loadW128 Glob.mem (W64.to_uint (rp + (W64.of_int 32))));
    t0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- t0;
    leakages <- LeakAddr([(W64.to_uint (rp + (W64.of_int 32)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (rp + (W64.of_int 32))) (aux_0);
    return ();
  }
}.

