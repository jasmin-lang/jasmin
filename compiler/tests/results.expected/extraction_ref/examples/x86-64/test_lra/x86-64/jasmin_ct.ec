require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (x:W64.t) : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t;
    
    var r:W64.t;
    var y:W64.t;
    var  _0:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    r <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 1);
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- mulu_64 y x;
     _0 <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- r;
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    r <- aux_0;
    return (r);
  }
  
  proc g (x:W64.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var r:W64.t;
    var one:W64.t;
    var cf:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    one <- aux;
    
    leakages <- LeakCond((x \ult (W64.of_int 12))) :: LeakAddr([]) :: leakages;
    
    while ((x \ult (W64.of_int 12))) {
      leakages <- LeakAddr([]) :: leakages;
      (aux_0, aux) <- adc_64 x one false;
      cf <- aux_0;
      x <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- ((! cf) ? one : r);
      r <- aux;
    leakages <- LeakCond((x \ult (W64.of_int 12))) :: LeakAddr([]) :: leakages;
    
    }
    return (r);
  }
}.

