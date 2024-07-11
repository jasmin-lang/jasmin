require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc concat_2u128 (x:W64.t, y:W64.t, z:W64.t) : unit = {
    var aux: W128.t;
    var aux_0: W256.t;
    
    var a:W128.t;
    var b:W128.t;
    var c:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (x + (W64.of_int 0))));
    a <- aux;
    leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW128 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W256.of_int ((W128.to_uint b) %% 2^128 + 2^128 * (W128.to_uint a)));
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- c;
    leakages <- LeakAddr([(W64.to_uint (z + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (z + (W64.of_int 0))) (aux_0);
    return ();
  }
}.

