require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakCond(((W64.of_int 5) \ult r)) :: LeakAddr([]) :: leakages;
    if (((W64.of_int 5) \ult r)) {
      leakages <- LeakCond(((W64.of_int 6) \ult r)) :: LeakAddr([]) :: leakages;
      if (((W64.of_int 6) \ult r)) {
        
      } else {
        
      }
    } else {
      leakages <- LeakCond(((W64.of_int 2) \ult r)) :: LeakAddr([]) :: leakages;
      if (((W64.of_int 2) \ult r)) {
        
      } else {
        
      }
    }
    return (r);
  }
}.

