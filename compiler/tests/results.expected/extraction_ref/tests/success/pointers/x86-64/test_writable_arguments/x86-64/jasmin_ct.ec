require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc f (t:W64.t Array1.t) : W64.t Array1.t = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    return (t);
  }
  
  proc g () : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t Array1.t;
    
    var r:W64.t;
    var s:W64.t Array1.t;
    var t:W64.t Array1.t;
    s <- witness;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- s;
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ f (((0 <= 1) ? t : t));
    s <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- s.[0];
    r <- aux_0;
    return (r);
  }
}.

