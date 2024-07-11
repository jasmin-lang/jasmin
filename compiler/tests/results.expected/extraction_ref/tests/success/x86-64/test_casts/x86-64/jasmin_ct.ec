require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc opsize_test (x:W64.t) : W8.t = {
    var aux_1: W8.t;
    var aux: W32.t;
    var aux_0: W64.t;
    
    var r:W8.t;
    var y:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    y <- (truncateu32 aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux <- (y + (truncateu32 x));
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((y \ult (W32.of_int 0)) ? (truncateu32 x) : y);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (x `>>` (W8.of_int 32));
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (x `|>>` (W8.of_int 8));
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    r <- (truncateu8 aux_0);
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (r `>>` (W8.of_int 1));
    r <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (r `^` (truncateu8 y));
    r <- aux_1;
    return (r);
  }
}.

