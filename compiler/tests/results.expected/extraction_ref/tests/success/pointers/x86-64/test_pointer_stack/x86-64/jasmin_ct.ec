require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc incr (t:W64.t Array1.t) : W64.t Array1.t = {
    var aux: W64.t;
    
    
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (t.[0] + (W64.of_int 1));
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    return (t);
  }
  
  proc sum (a:W64.t Array1.t, b:W64.t Array1.t) : W64.t Array1.t = {
    var aux_0: W64.t;
    
    var d:W64.t Array1.t;
    var aux:W64.t;
    d <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- a.[0];
    aux <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- (aux + b.[0]);
    aux <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    d.[0] <- aux_0;
    return (d);
  }
  
  proc test () : W64.t = {
    var aux: W64.t;
    var aux_0: W64.t Array1.t;
    
    var res_0:W64.t;
    var a1:W64.t Array1.t;
    var a2:W64.t Array1.t;
    var a3:W64.t Array1.t;
    a1 <- witness;
    a2 <- witness;
    a3 <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    leakages <- LeakAddr([0]) :: leakages;
    a1.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    leakages <- LeakAddr([0]) :: leakages;
    a2.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ sum (a1, a2);
    a3 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ incr (a3);
    a3 <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a3.[0];
    res_0 <- aux;
    return (res_0);
  }
}.

