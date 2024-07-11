require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc main (x:W64.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var y:W64.t;
    var msf:W64.t;
    var b:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    msf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- true;
    b <- aux_0;
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    if (b) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (x + (W64.of_int 1));
      x <- aux;
    } else {
      
    }
    leakages <- LeakCond((! b)) :: LeakAddr([]) :: leakages;
    if ((! b)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (x + (W64.of_int 1));
      x <- aux;
    } else {
      
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- protect_64 y msf;
    y <- aux;
    return (y);
  }
}.

