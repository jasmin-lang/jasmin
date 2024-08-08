require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1 Array10.
require import WArray8 WArray80.



module M = {
  var leakages : leakages_t
  
  proc test () : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t Array1.t;
    
    var r:W64.t;
    var s:W64.t Array10.t;
    var t:W64.t Array1.t;
    s <- witness;
    t <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (Array1.init (fun i => s.[0 + i]));
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    t <- Array1.init (WArray8.get64 (WArray8.set64_direct (WArray8.init64 (fun i => (t).[i])) 0 (aux_0)));
    leakages <- LeakAddr([]) :: leakages;
    aux <- t;
    leakages <- LeakAddr([0]) :: leakages;
    s <- Array10.init (fun i => if 0 <= i < 0 + 1 then aux.[i-0] else s.[i]);
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- s.[0];
    r <- aux_0;
    return (r);
  }
}.

