require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.

abbrev mINUS_Q = W32.of_int (-8380417).


module M = {
  var leakages : leakages_t
  
  proc __montgomery_reduce_8380417 (a:W32.t) : W32.t = {
    var aux: W32.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((a `<<` (W8.of_int 3)) - a);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((W32.of_int 2) - a);
    a <- aux;
    return (a);
  }
}.

