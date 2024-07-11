require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test (x:W64.t, y:W64.t) : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t;
    
    var z1:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- MULX_64 x y;
    hi <- aux_0;
    lo <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (hi `<<` (W8.of_int 1));
    z1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (z1 + lo);
    z1 <- aux_0;
    return (z1);
  }
  
  proc test_lo_hi (x:W64.t, y:W64.t) : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t;
    
    var z1:W64.t;
    var lo:W64.t;
    var hi:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- MULX_lo_hi_64 x y;
    lo <- aux_0;
    hi <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (hi `<<` (W8.of_int 1));
    z1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (z1 + lo);
    z1 <- aux_0;
    return (z1);
  }
  
  proc test_hi (x:W64.t, y:W64.t) : W64.t = {
    var aux: W64.t;
    
    var z1:W64.t;
    var hi:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- MULX_hi_64 x y;
    hi <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (hi `<<` (W8.of_int 1));
    z1 <- aux;
    return (z1);
  }
}.

