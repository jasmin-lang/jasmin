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
    
    var i:int;
    var y:W64.t Array4.t;
    var cf:bool;
    var add0:W64.t;
    var add1:W64.t;
    y <- witness;
    i <- 0;
    while (i < 4) {
      y.[i] <- ya.[i];
      if ((i = 0)) {
        (aux_0, aux_1) <- adc_64 x.[0] y.[0] false;
        cf <- aux_0;
        x.[0] <- aux_1;
      } else {
        (aux_0, aux_1) <- adc_64 x.[i] y.[i] cf;
        cf <- aux_0;
        x.[i] <- aux_1;
      }
      i <- i + 1;
    }
    add0 <- (W64.of_int 0);
    add1 <- (W64.of_int 2);
    add1 <- ((! cf) ? add0 : add1);
    i <- 0;
    while (i < 4) {
      if ((i = 0)) {
        (aux_0, aux_1) <- adc_64 x.[0] add1 false;
        cf <- aux_0;
        x.[0] <- aux_1;
      } else {
        (aux_0, aux_1) <- adc_64 x.[i] add0 cf;
        cf <- aux_0;
        x.[i] <- aux_1;
      }
      i <- i + 1;
    }
    add0 <- (cf ? add1 : add0);
    x.[0] <- (x.[0] + add0);
    return (x);
  }
  
  proc eadd (ad:W64.t, ax:W64.t, ay:W64.t) : unit = {
    var aux: int;
    
    var i:int;
    var x:W64.t Array4.t;
    var y:W64.t Array4.t;
    x <- witness;
    y <- witness;
    i <- 0;
    while (i < 4) {
      x.[i] <- (loadW64 Glob.mem (W64.to_uint (ax + (W64.of_int (8 * i)))));
      i <- i + 1;
    }
    i <- 0;
    while (i < 4) {
      y.[i] <- (loadW64 Glob.mem (W64.to_uint (ay + (W64.of_int (8 * i)))));
      i <- i + 1;
    }
    x <@ add (x, y);
    i <- 0;
    while (i < 4) {
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (ad + (W64.of_int (8 * i)))) (x.[i]);
      i <- i + 1;
    }
    return ();
  }
}.

