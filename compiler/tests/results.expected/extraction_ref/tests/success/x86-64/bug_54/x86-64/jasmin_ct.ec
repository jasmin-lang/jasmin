require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2 Array3 Array4.
require import WArray3 WArray4.



module M = {
  var leakages : leakages_t
  
  proc main () : W8.t = {
    var aux: W8.t;
    var aux_0: W8.t Array2.t;
    
    var res_0:W8.t;
    var b:W8.t Array4.t;
    var a:W8.t Array3.t;
    a <- witness;
    b <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W8.of_int 42);
    leakages <- LeakAddr([1]) :: leakages;
    b.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux_0 <- (Array2.init (fun i => b.[1 + i]));
    leakages <- LeakAddr([0]) :: leakages;
    a <- Array3.init (fun i => if 0 <= i < 0 + 2 then aux_0.[i-0] else a.[i]);
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    res_0 <- aux;
    return (res_0);
  }
}.

