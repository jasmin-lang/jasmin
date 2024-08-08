require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_bt (x:W64.t, y:W64.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var r:W64.t;
    var c:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- BT_16 (truncateu16 x) (truncateu16 y);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? y : r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- BT_32 (truncateu32 x) (truncateu32 y);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? y : r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- BT_64 x y;
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? y : r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- BT_16 (truncateu16 x) (W16.of_int 5);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? y : r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- BT_32 (truncateu32 x) (W32.of_int 15);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? y : r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- BT_64 x (W64.of_int 15);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c ? y : r);
    r <- aux;
    return (r);
  }
}.

