require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc foo () : W64.t = {
    var aux: W64.t;
    
    var x:W64.t;
    var msf:W64.t;
    var msf1:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    msf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- protect_64 x msf;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- mov_msf msf;
    msf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- protect_64 x msf;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- mov_msf msf;
    msf1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- protect_64 x msf;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- protect_64 x msf1;
    x <- aux;
    return (x);
  }
}.

