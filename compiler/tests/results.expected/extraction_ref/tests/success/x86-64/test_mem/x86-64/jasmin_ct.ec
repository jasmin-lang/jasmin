require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (p:W64.t, i:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    var x:W64.t;
    
    leakages <- LeakAddr([(W64.to_uint (p + ((W64.of_int 8) * i)))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (p + ((W64.of_int 8) * i))));
    r <- aux;
    leakages <- LeakAddr([(W64.to_uint (p + ((W64.of_int 8) * i)))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (p + ((W64.of_int 8) * i))));
    x <- aux;
    return (r);
  }
}.

