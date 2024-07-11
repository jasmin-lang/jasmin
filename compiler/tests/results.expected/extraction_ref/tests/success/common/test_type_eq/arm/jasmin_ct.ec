require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.
require import Array1 Array8.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc f (x:W64.t Array1.t) : W64.t Array1.t = {
    
    
    
    
    return (x);
  }
  
  proc g () : unit = {
    var aux: W8.t Array8.t;
    var aux_0: W64.t Array1.t;
    
    var b:W64.t Array1.t;
    var a:W64.t Array1.t;
    a <- witness;
    b <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- copy_64 b;
    a <- aux_0;
    return ();
  }
}.

