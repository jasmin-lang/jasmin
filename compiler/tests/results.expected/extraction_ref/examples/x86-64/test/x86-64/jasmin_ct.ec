require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array4.
require import WArray32.



module M = {
  var leakages : leakages_t
  
  proc add (x:W64.t Array4.t, ya:W64.t Array4.t) : W64.t Array4.t = {
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var y:W64.t Array4.t;
    var cf:bool;
    var add0:W64.t;
    var add1:W64.t;
    y <- witness;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- ya.[i];
      leakages <- LeakAddr([i]) :: leakages;
      y.[i] <- aux_0;
      leakages <- LeakCond((i = 0)) :: LeakAddr([]) :: leakages;
      if ((i = 0)) {
        leakages <- LeakAddr([0; 0]) :: leakages;
        (aux_1, aux_0) <- adc_64 x.[0] y.[0] false;
        cf <- aux_1;
        leakages <- LeakAddr([0]) :: leakages;
        x.[0] <- aux_0;
      } else {
        leakages <- LeakAddr([i; i]) :: leakages;
        (aux_1, aux_0) <- adc_64 x.[i] y.[i] cf;
        cf <- aux_1;
        leakages <- LeakAddr([i]) :: leakages;
        x.[i] <- aux_0;
      }
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    add0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 2);
    add1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- ((! cf) ? add0 : add1);
    add1 <- aux_0;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakCond((i = 0)) :: LeakAddr([]) :: leakages;
      if ((i = 0)) {
        leakages <- LeakAddr([0]) :: leakages;
        (aux_1, aux_0) <- adc_64 x.[0] add1 false;
        cf <- aux_1;
        leakages <- LeakAddr([0]) :: leakages;
        x.[0] <- aux_0;
      } else {
        leakages <- LeakAddr([i]) :: leakages;
        (aux_1, aux_0) <- adc_64 x.[i] add0 cf;
        cf <- aux_1;
        leakages <- LeakAddr([i]) :: leakages;
        x.[i] <- aux_0;
      }
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (cf ? add1 : add0);
    add0 <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- (x.[0] + add0);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux_0;
    return (x);
  }
  
  proc eadd (ad:W64.t, ax:W64.t, ay:W64.t) : unit = {
    var aux: int;
    var aux_0: W64.t;
    var aux_1: W64.t Array4.t;
    
    var i:int;
    var x:W64.t Array4.t;
    var y:W64.t Array4.t;
    x <- witness;
    y <- witness;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([(W64.to_uint (ax + (W64.of_int (8 * i))))]) :: leakages;
      aux_0 <- (loadW64 Glob.mem (W64.to_uint (ax + (W64.of_int (8 * i)))));
      leakages <- LeakAddr([i]) :: leakages;
      x.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([(W64.to_uint (ay + (W64.of_int (8 * i))))]) :: leakages;
      aux_0 <- (loadW64 Glob.mem (W64.to_uint (ay + (W64.of_int (8 * i)))));
      leakages <- LeakAddr([i]) :: leakages;
      y.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ add (x, y);
    x <- aux_1;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- x.[i];
      leakages <- LeakAddr([(W64.to_uint (ad + (W64.of_int (8 * i))))]) :: leakages;
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (ad + (W64.of_int (8 * i)))) (aux_0);
      i <- i + 1;
    }
    return ();
  }
}.

