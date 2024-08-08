require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc main (y:W64.t) : unit = {
    var aux: W64.t;
    
    var x:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- MOV_64 y;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((x = (W64.of_int 0)) ? y : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (x + (W64.of_int 0))) (aux);
    return ();
  }
}.

