require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2 Array4.
require import WArray16 WArray32.



module M = {
  var leakages : leakages_t
  
  proc f (r:W64.t Array2.t) : W64.t Array2.t = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux;
    return (r);
  }
  
  proc test (r:W64.t Array4.t) : W64.t Array4.t * W64.t = {
    var aux_0: W64.t;
    var aux: W64.t Array2.t;
    
    var res_0:W64.t;
    var r2:W64.t Array2.t;
    r2 <- witness;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (Array2.init (fun i => r.[1 + i]));
    r2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (* Erased call to spill *)
    leakages <- LeakAddr([]) :: leakages;
    aux <@ f (r2);
    r2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (* Erased call to unspill *)
    leakages <- LeakAddr([]) :: leakages;
    aux <- r2;
    leakages <- LeakAddr([1]) :: leakages;
    r <- Array4.init (fun i => if 1 <= i < 1 + 2 then aux.[i-1] else r.[i]);
    leakages <- LeakAddr([1]) :: leakages;
    aux_0 <- r.[1];
    res_0 <- aux_0;
    return (r, res_0);
  }
}.

