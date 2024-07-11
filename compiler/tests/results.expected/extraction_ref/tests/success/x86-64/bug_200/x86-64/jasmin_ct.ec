require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc exp (e:W64.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var m:W64.t;
    var c:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    m <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (e <> (W64.of_int 0));
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? e : m);
    m <- aux;
    return (m);
  }
}.

