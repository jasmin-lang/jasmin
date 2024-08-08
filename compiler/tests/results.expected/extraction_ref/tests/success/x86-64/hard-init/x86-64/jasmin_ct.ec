require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (input:W64.t) : W64.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var result:W64.t;
    var b:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (input = (W64.of_int 0));
    b <- aux;
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    if (b) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 0);
      result <- aux_0;
    } else {
      
    }
    leakages <- LeakCond((! b)) :: LeakAddr([]) :: leakages;
    if ((! b)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 1);
      result <- aux_0;
    } else {
      
    }
    return (result);
  }
}.

