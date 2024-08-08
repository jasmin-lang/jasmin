require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array7 Array8.
require import WArray56 WArray64.



module M = {
  proc zero () : W64.t = {
    var aux: int;
    
    var x:W64.t;
    var i:int;
    var t:W64.t Array7.t;
    t <- witness;
    i <- 0;
    while (i < 7) {
      t.[i] <- (W64.of_int i);
      i <- i + 1;
    }
    x <- (W64.of_int 0);
    i <- 0;
    while (i < 7) {
      x <- (x + t.[i]);
      i <- i + 1;
    }
    return (x);
  }
  
  proc one () : W64.t = {
    var aux: int;
    
    var y:W64.t;
    var i:int;
    var t:W64.t Array8.t;
    var x:W64.t;
    t <- witness;
    y <- (W64.of_int 0);
    aux <- (7 + 1);
    i <- 0;
    while (i < aux) {
      t.[i] <- (W64.of_int i);
      i <- i + 1;
    }
    x <- (W64.of_int 0);
    aux <- (7 + 1);
    i <- 0;
    while (i < aux) {
      x <- (x + t.[i]);
      i <- i + 1;
    }
    y <- (y + x);
    return (y);
  }
}.

