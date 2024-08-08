require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc f (a:W64.t Array1.t, x:W64.t) : W64.t Array1.t * W64.t = {
    var aux: W64.t Array1.t;
    
    var s:W64.t Array1.t;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    s <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- s;
    a <- aux;
    return (a, x);
  }
  
  proc main () : unit = {
    var aux: W64.t;
    var aux_0: W64.t Array1.t;
    
    var x:W64.t;
    var a:W64.t Array1.t;
    var  _0:W64.t Array1.t;
    var  _1:W64.t;
     _0 <- witness;
    a <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakCond(false) :: LeakAddr([]) :: leakages;
    if (false) {
      leakages <- LeakAddr([]) :: leakages;
      (aux_0, aux) <@ f (a, x);
       _0 <- aux_0;
       _1 <- aux;
    } else {
      
    }
    return ();
  }
}.

