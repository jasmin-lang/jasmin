require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test () : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var x2:W64.t;
    var x1:W64.t;
    var  _0:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    x1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    x2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_64 x1 x2 false;
     _0 <- aux_0;
    x1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- LEA_64 (x1 + (W64.of_int 1));
    x2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x2 + x1);
    x2 <- aux;
    return (x2);
  }
}.

