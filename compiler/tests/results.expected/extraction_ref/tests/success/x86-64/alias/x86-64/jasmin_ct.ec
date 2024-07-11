require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1 Array5 Array10.
require import WArray8 WArray40 WArray80.



module M = {
  var leakages : leakages_t
  
  proc test (x:W64.t) : W64.t = {
    var aux: W64.t;
    var aux_0: W64.t Array5.t;
    
    var result:W64.t;
    var bigA:W64.t Array10.t;
    var leftA:W64.t Array5.t;
    var rightA:W64.t Array5.t;
    var bigB:W64.t Array10.t;
    bigA <- witness;
    bigB <- witness;
    leftA <- witness;
    rightA <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([0]) :: leakages;
    bigA.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- (Array5.init (fun i => bigA.[0 + i]));
    leftA <- aux_0;
    leakages <- LeakAddr([5]) :: leakages;
    aux_0 <- (Array5.init (fun i => bigA.[5 + i]));
    rightA <- aux_0;
    leakages <- LeakCond(((W64.of_int 0) \ult x)) :: LeakAddr([]) :: leakages;
    if (((W64.of_int 0) \ult x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- x;
      leakages <- LeakAddr([0]) :: leakages;
      bigB.[0] <- aux;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- leftA;
      leakages <- LeakAddr([0]) :: leakages;
      bigB <- Array10.init (fun i => if 0 <= i < 0 + 5 then aux_0.[i-0] else bigB.[i]);
    }
    leakages <- LeakAddr([0]) :: leakages;
    aux <- bigB.[0];
    result <- aux;
    return (result);
  }
  
  proc toto (p:W64.t Array1.t, x:W64.t) : W64.t Array1.t = {
    var aux_0: W64.t;
    var aux: W64.t Array1.t;
    
    var a:W64.t Array1.t;
    a <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- p;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    leakages <- LeakAddr([0]) :: leakages;
    p.[0] <- aux_0;
    return (p);
  }
}.

