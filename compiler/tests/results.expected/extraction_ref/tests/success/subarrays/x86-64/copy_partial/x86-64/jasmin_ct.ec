require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1 Array2.
require import WArray16.



module M = {
  var leakages : leakages_t
  
  proc test () : W64.t = {
    var aux: W64.t;
    var aux_1: W64.t Array1.t;
    var aux_0: W64.t Array2.t;
    
    var res_0:W64.t;
    var s:W64.t Array2.t;
    var r1:W64.t Array2.t;
    var r2:W64.t Array2.t;
    r1 <- witness;
    r2 <- witness;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    s.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    leakages <- LeakAddr([1]) :: leakages;
    s.[1] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s;
    r1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 2);
    leakages <- LeakAddr([0]) :: leakages;
    r1.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s;
    r2 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 3);
    leakages <- LeakAddr([1]) :: leakages;
    r2.[1] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_1 <- (Array1.init (fun i => r1.[0 + i]));
    leakages <- LeakAddr([0]) :: leakages;
    s <- Array2.init (fun i => if 0 <= i < 0 + 1 then aux_1.[i-0] else s.[i]);
    leakages <- LeakAddr([1]) :: leakages;
    aux_1 <- (Array1.init (fun i => r2.[1 + i]));
    leakages <- LeakAddr([1]) :: leakages;
    s <- Array2.init (fun i => if 1 <= i < 1 + 1 then aux_1.[i-1] else s.[i]);
    leakages <- LeakAddr([0]) :: leakages;
    aux <- s.[0];
    res_0 <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (res_0 + s.[1]);
    res_0 <- aux;
    return (res_0);
  }
}.

