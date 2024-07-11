require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc umaal (a:W32.t, b:W32.t, c:W32.t, d:W32.t) : W32.t = {
    var aux: bool;
    var aux_1: W32.t;
    var aux_0: W32.t;
    
    var f:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (d \ult c);
    f <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <- UMAAL a b c d;
    a <- aux_1;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_1, aux_0) <- UMAALcc a b c d f a b;
    a <- aux_1;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (a `^` b);
    a <- aux_1;
    return (a);
  }
}.

