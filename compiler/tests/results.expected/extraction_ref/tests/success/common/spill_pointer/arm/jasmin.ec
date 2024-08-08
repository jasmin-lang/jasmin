require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array1.
require import WArray4.

abbrev c = Array1.of_list witness [W32.of_int 1].


module M = {
  proc main () : W32.t = {
    
    var c_0:W32.t;
    var cp:W32.t Array1.t;
    var cps:W32.t Array1.t;
    cp <- witness;
    cps <- witness;
    cp <- c;
    cps <- cp;
    cp <- cps;
    c_0 <- cp.[0];
    return (c_0);
  }
}.

