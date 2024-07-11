require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array2.
require import WArray8.



module M = {
  proc aux (out:W32.t Array2.t, in_0:W32.t Array2.t) : W32.t Array2.t = {
    var aux_1: W32.t;
    var aux_0: W32.t;
    
    var x:W32.t Array2.t;
    var y:W32.t Array2.t;
    x <- witness;
    y <- witness;
    x <- copy_32 in_0;
    (aux_1, aux_0) <- mulu_32 x.[0] x.[1];
    y.[0] <- aux_1;
    y.[1] <- aux_0;
    out <- copy_32 y;
    return (out);
  }
  
  proc test (t:W32.t) : W32.t = {
    var aux_0: int;
    
    var res_0:W32.t;
    var i:int;
    var a:W32.t Array2.t;
    var b:W32.t Array2.t;
    a <- witness;
    b <- witness;
    i <- 0;
    while (i < 2) {
      a.[i] <- t;
      i <- i + 1;
    }
    b <@ aux (b, a);
    res_0 <- (W32.of_int 0);
    i <- 0;
    while (i < 2) {
      t <- b.[i];
      res_0 <- (res_0 `|` t);
      i <- i + 1;
    }
    return (res_0);
  }
}.

