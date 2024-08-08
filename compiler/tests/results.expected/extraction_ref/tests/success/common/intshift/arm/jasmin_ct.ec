require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_int_shift (x:W32.t) : W32.t = {
    var aux_0: int;
    var aux: W32.t;
    
    var i:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    x <- aux;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (x + (W32.of_int (1 `<<` i)));
      x <- aux;
      i <- i + 1;
    }
    return (x);
  }
}.

