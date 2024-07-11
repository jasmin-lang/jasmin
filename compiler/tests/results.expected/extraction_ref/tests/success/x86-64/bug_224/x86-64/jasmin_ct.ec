require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc main (x:W64.t) : unit = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x - (W64.of_int 1));
    x <- aux;
    leakages <- LeakCond(((W64.of_int 0) \ult x)) :: LeakAddr([]) :: leakages;
    
    while (((W64.of_int 0) \ult x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (x - (W64.of_int 1));
      x <- aux;
    leakages <- LeakCond(((W64.of_int 0) \ult x)) :: LeakAddr([]) :: leakages;
    
    }
    return ();
  }
}.

