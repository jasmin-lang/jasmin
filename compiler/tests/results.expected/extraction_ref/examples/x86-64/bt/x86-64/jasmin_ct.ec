require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (x:W64.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var y:W64.t;
    var cf:bool;
    var  _0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- BT_64 x (W64.of_int 4);
    cf <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_64 y x cf;
     _0 <- aux_0;
    y <- aux;
    return (y);
  }
}.

