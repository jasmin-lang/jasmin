require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test (x:W64.t, y:W64.t) : W64.t = {
    var aux: W64.t;
    
    var result:W64.t;
    
    leakages <- LeakCond((x <> (W64.of_int 0))) :: LeakAddr([]) :: leakages;
    if ((x <> (W64.of_int 0))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- x;
      result <- aux;
    } else {
      leakages <- LeakCond((y <> (W64.of_int 0))) :: LeakAddr([]) :: leakages;
      if ((y <> (W64.of_int 0))) {
        leakages <- LeakAddr([]) :: leakages;
        aux <- y;
        result <- aux;
      } else {
        leakages <- LeakAddr([]) :: leakages;
        aux <- (W64.of_int 0);
        result <- aux;
      }
    }
    return (result);
  }
}.

