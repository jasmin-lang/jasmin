require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f () : W64.t = {
    var aux: W64.t;
    
    var res_0:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    res_0 <- aux;
    return (res_0);
  }
  
  proc g (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var res_0:W64.t;
    
    leakages <- LeakCond((x = (W64.of_int 0))) :: LeakAddr([]) :: leakages;
    if ((x = (W64.of_int 0))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 0);
      res_0 <- aux;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux <@ f ();
      res_0 <- aux;
    }
    return (res_0);
  }
}.

