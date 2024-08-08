require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc foo (x:W64.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var r:W64.t;
    var msf:W64.t;
    var b:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    msf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (x = x);
    b <- aux_0;
    leakages <- LeakCond(b) :: LeakAddr([]) :: leakages;
    if (b) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- update_msf b msf;
      msf <- aux;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux <- update_msf (! b) msf;
      msf <- aux;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- protect_64 r msf;
    r <- aux;
    return (r);
  }
}.

