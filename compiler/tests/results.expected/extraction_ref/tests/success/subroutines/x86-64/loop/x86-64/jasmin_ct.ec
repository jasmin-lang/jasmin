require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc aux (x:W64.t) : W64.t = {
    
    
    
    
    return (x);
  }
  
  proc main (x:W64.t) : W64.t = {
    var aux_0: W64.t;
    
    var result:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    result <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ aux (result);
    result <- aux_0;
    leakages <- LeakCond(((W64.of_int 0) \ult x)) :: LeakAddr([]) :: leakages;
    
    while (((W64.of_int 0) \ult x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ aux (result);
      result <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (x - (W64.of_int 1));
      x <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ aux (result);
      result <- aux_0;
    leakages <- LeakCond(((W64.of_int 0) \ult x)) :: LeakAddr([]) :: leakages;
    
    }
    return (result);
  }
}.

