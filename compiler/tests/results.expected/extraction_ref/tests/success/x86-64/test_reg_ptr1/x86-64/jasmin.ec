require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array4.
require import WArray32.

abbrev glob_t = Array4.of_list witness [W64.of_int 0; W64.of_int 1; W64.of_int 2; W64.of_int 3].


module M = {
  proc foo (x:W64.t) : W64.t = {
    var aux: int;
    
    var r:W64.t;
    var i:int;
    var s:W64.t Array4.t;
    var rt:W64.t Array4.t;
    var st:W64.t Array4.t;
    rt <- witness;
    s <- witness;
    st <- witness;
    i <- 0;
    while (i < 4) {
      s.[i] <- x;
      i <- i + 1;
    }
    rt <- s;
    r <- (W64.of_int 0);
    i <- 0;
    while (i < 4) {
      r <- (r + rt.[0]);
      i <- i + 1;
    }
    st <- rt;
    i <- 0;
    while (i < 4) {
      r <- (r + s.[0]);
      i <- i + 1;
    }
    rt <- st;
    i <- 0;
    while (i < 4) {
      rt.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    i <- 0;
    while (i < 4) {
      r <- (r + rt.[0]);
      i <- i + 1;
    }
    s <- rt;
    i <- 0;
    while (i < 4) {
      r <- (r + s.[0]);
      i <- i + 1;
    }
    return (r);
  }
}.

