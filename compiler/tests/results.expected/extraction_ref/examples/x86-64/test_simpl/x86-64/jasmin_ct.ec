require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array4.
require import WArray32.



module M = {
  var leakages : leakages_t
  
  proc add (x:W64.t Array4.t, ya:W64.t Array4.t) : W64.t Array4.t = {
    var aux_0: bool;
    var aux: int;
    var aux_1: W64.t;
    
    var y:W64.t Array4.t;
    var i:int;
    var cf:bool;
    y <- witness;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakCond((i = 0)) :: LeakAddr([]) :: leakages;
      if ((i = 0)) {
        leakages <- LeakAddr([0; 0]) :: leakages;
        (aux_0, aux_1) <- adc_64 x.[0] ya.[0] false;
        cf <- aux_0;
        leakages <- LeakAddr([0]) :: leakages;
        x.[0] <- aux_1;
      } else {
        leakages <- LeakAddr([i; i]) :: leakages;
        (aux_0, aux_1) <- adc_64 x.[i] ya.[i] cf;
        cf <- aux_0;
        leakages <- LeakAddr([i]) :: leakages;
        x.[i] <- aux_1;
      }
      i <- i + 1;
    }
    return (y);
  }
  
  proc eadd () : unit = {
    var aux: int;
    var aux_0: W64.t;
    var aux_1: W64.t Array4.t;
    
    var i:int;
    var x:W64.t Array4.t;
    var ya:W64.t Array4.t;
    var z:W64.t Array4.t;
    x <- witness;
    ya <- witness;
    z <- witness;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([i]) :: leakages;
      x.[i] <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 1);
      leakages <- LeakAddr([i]) :: leakages;
      ya.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ add (x, ya);
    z <- aux_1;
    return ();
  }
}.

