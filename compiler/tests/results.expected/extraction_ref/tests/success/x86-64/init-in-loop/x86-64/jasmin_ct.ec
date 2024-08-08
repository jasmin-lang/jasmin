require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc main () : W64.t = {
    var aux: W64.t;
    
    var y:W64.t;
    var x:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 2);
    x <- aux;
    
    leakages <- LeakCond(((W64.of_int 0) \ult x)) :: LeakAddr([]) :: leakages;
    
    while (((W64.of_int 0) \ult x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 1);
      y <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (x - (W64.of_int 1));
      x <- aux;
    leakages <- LeakCond(((W64.of_int 0) \ult x)) :: LeakAddr([]) :: leakages;
    
    }
    return (y);
  }
}.

