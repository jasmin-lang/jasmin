require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array4.
require import WArray32.



module M = {
  proc add (x:W64.t Array4.t, ya:W64.t Array4.t) : W64.t Array4.t = {
    var aux_0: bool;
    var aux: int;
    var aux_1: W64.t;
    
    var y:W64.t Array4.t;
    var i:int;
    var cf:bool;
    y <- witness;
    i <- 0;
    while (i < 4) {
      if ((i = 0)) {
        (aux_0, aux_1) <- adc_64 x.[0] ya.[0] false;
        cf <- aux_0;
        x.[0] <- aux_1;
      } else {
        (aux_0, aux_1) <- adc_64 x.[i] ya.[i] cf;
        cf <- aux_0;
        x.[i] <- aux_1;
      }
      i <- i + 1;
    }
    return (y);
  }
  
  proc eadd () : unit = {
    var aux: int;
    
    var i:int;
    var x:W64.t Array4.t;
    var ya:W64.t Array4.t;
    var z:W64.t Array4.t;
    x <- witness;
    ya <- witness;
    z <- witness;
    i <- 0;
    while (i < 4) {
      x.[i] <- (W64.of_int 0);
      ya.[i] <- (W64.of_int 1);
      i <- i + 1;
    }
    z <@ add (x, ya);
    return ();
  }
}.

