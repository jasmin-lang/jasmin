require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test (p:W64.t) : unit = {
    var aux: W128.t;
    var aux_0: W256.t;
    
    var a:W128.t;
    var b:W128.t;
    var x:W256.t;
    var y:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VMOVSLDUP_128 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VMOVSLDUP_128 a;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux <- VMOVSHDUP_128 (loadW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VMOVSHDUP_128 a;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_0 <- VMOVSLDUP_256 (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VMOVSLDUP_256 x;
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- y;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) ((truncateu128 aux_0));
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    aux_0 <- VMOVSHDUP_256 (loadW256 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VMOVSHDUP_256 x;
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- y;
    leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (p + (W64.of_int 0))) ((truncateu128 aux_0));
    return ();
  }
}.

