require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray4.

abbrev c = Array1.of_list witness [W32.of_int 1].


module M = {
  var leakages : leakages_t
  
  proc main () : W32.t = {
    var aux_0: W32.t;
    var aux: W32.t Array1.t;
    
    var c_0:W32.t;
    var cp:W32.t Array1.t;
    var cps:W32.t Array1.t;
    cp <- witness;
    cps <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- c;
    cp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- cp;
    cps <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- cps;
    cp <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- cp.[0];
    c_0 <- aux_0;
    return (c_0);
  }
}.

