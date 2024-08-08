require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc adcx64 (x:W64.t, y:W64.t) : W64.t = {
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux_6: W64.t;
    var aux_5: W64.t;
    
    var r:W64.t;
    var of_0:bool;
    var cf:bool;
    var sf:bool;
    var pf:bool;
    var zf:bool;
    var aux:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux_6) <- ADD_64 x y;
    of_0 <- aux_4;
    cf <- aux_3;
    sf <- aux_2;
    pf <- aux_1;
    zf <- aux_0;
    x <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_6) <- ADCX_64 x y cf;
    cf <- aux_4;
    x <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_6) <- ADOX_64 x y of_0;
    of_0 <- aux_4;
    x <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    aux_6 <- y;
    aux <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    (aux_6, aux_5) <- MULX_64 aux x;
    hi <- aux_6;
    lo <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_6 <- (hi + lo);
    r <- aux_6;
    return (r);
  }
  
  proc adcx32 (x:W32.t, y:W32.t) : W32.t = {
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux_6: W32.t;
    var aux_5: W32.t;
    
    var r:W32.t;
    var of_0:bool;
    var cf:bool;
    var sf:bool;
    var pf:bool;
    var zf:bool;
    var aux:W32.t;
    var hi:W32.t;
    var lo:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_3, aux_2, aux_1, aux_0, aux_6) <- ADD_32 x y;
    of_0 <- aux_4;
    cf <- aux_3;
    sf <- aux_2;
    pf <- aux_1;
    zf <- aux_0;
    x <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_6) <- ADCX_32 x y cf;
    cf <- aux_4;
    x <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    (aux_4, aux_6) <- ADOX_32 x y of_0;
    of_0 <- aux_4;
    x <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    aux_6 <- y;
    aux <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    (aux_6, aux_5) <- MULX_32 aux x;
    hi <- aux_6;
    lo <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_6 <- (hi + lo);
    r <- aux_6;
    return (r);
  }
}.

