require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc squarea (x:W64.t Array1.t) : W64.t Array1.t = {
    var aux: int;
    
    var ra:W64.t Array1.t;
    var i:int;
    var r:W64.t Array1.t;
    r <- witness;
    ra <- witness;
    i <- 0;
    while (i < 1) {
      r.[i] <- x.[i];
      i <- i + 1;
    }
    ra <- copy_64 r;
    return (ra);
  }
  
  proc invert (xa:W64.t Array1.t) : unit = {
    
    var t:W64.t Array1.t;
    var k:W64.t;
    t <- witness;
    t <- xa;
    k <- (W64.of_int 1);
    t <@ squarea (t);
    k <- (k + (W64.of_int 1));
    while ((k \ult (W64.of_int 5))) {
      t <@ squarea (t);
      k <- (k + (W64.of_int 1));
    }
    return ();
  }
  
  proc scalarmult () : unit = {
    var aux: int;
    
    var i:int;
    var za:W64.t Array1.t;
    za <- witness;
    i <- 0;
    while (i < 1) {
      za.[i] <- (W64.of_int i);
      i <- i + 1;
    }
    invert (za);
    return ();
  }
}.

