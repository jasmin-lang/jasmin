require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1 Array8.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc squarea (x:W64.t Array1.t) : W64.t Array1.t = {
    var aux: int;
    var aux_0: W64.t;
    var aux_1: W8.t Array8.t;
    var aux_2: W64.t Array1.t;
    
    var ra:W64.t Array1.t;
    var i:int;
    var r:W64.t Array1.t;
    r <- witness;
    ra <- witness;
    leakages <- LeakFor(0,1) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 1) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- x.[i];
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- copy_64 r;
    ra <- aux_2;
    return (ra);
  }
  
  proc invert (xa:W64.t Array1.t) : unit = {
    var aux_0: W64.t;
    var aux: W64.t Array1.t;
    
    var t:W64.t Array1.t;
    var k:W64.t;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- xa;
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 1);
    k <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ squarea (t);
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (k + (W64.of_int 1));
    k <- aux_0;
    leakages <- LeakCond((k \ult (W64.of_int 5))) :: LeakAddr([]) :: leakages;
    
    while ((k \ult (W64.of_int 5))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <@ squarea (t);
      t <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (k + (W64.of_int 1));
      k <- aux_0;
    leakages <- LeakCond((k \ult (W64.of_int 5))) :: LeakAddr([]) :: leakages;
    
    }
    return ();
  }
  
  proc scalarmult () : unit = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var za:W64.t Array1.t;
    za <- witness;
    leakages <- LeakFor(0,1) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 1) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int i);
      leakages <- LeakAddr([i]) :: leakages;
      za.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    invert (za);
    return ();
  }
}.

