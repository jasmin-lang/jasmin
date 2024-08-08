require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.
require import Array4.
require import WArray16.



module M = {
  var leakages : leakages_t
  
  proc id_by_stack (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    var s:W32.t Array4.t;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([1]) :: leakages;
    s.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- s.[1];
    x <- aux;
    return (x);
  }
}.

