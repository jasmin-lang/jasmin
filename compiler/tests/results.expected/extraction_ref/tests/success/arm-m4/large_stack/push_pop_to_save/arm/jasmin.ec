require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array10 Array1024.
require import WArray40 WArray4096.



module M = {
  proc main () : W32.t = {
    var aux: int;
    
    var i:W32.t;
    var n:W32.t;
    var s:W32.t Array1024.t;
    var ps:W32.t Array1024.t;
    var j:int;
    var t:W32.t Array10.t;
    var d:W32.t;
    ps <- witness;
    s <- witness;
    t <- witness;
    i <- (W32.of_int 0);
    n <- (W32.of_int 1024);
    ps <- s;
    
    while ((i \ult n)) {
      ps.[(W32.to_uint i)] <- i;
      i <- (i + (W32.of_int 1));
    }
    j <- 0;
    while (j < 10) {
      t.[j] <- ps.[j];
      j <- j + 1;
    }
    i <- (W32.of_int 10);
    n <- (W32.of_int ((1024 %/ 10) * 10));
    
    while ((i \ult n)) {
      j <- 0;
      while (j < 10) {
        d <- ps.[(W32.to_uint i)];
        t.[j] <- (t.[j] + d);
        i <- (i + (W32.of_int 1));
        j <- j + 1;
      }
    }
    n <- (W32.of_int 1024);
    
    while ((i \ult n)) {
      d <- ps.[(W32.to_uint i)];
      t.[0] <- (t.[0] + d);
      i <- (i + (W32.of_int 1));
    }
    j <- 1;
    while (j < 10) {
      t.[0] <- (t.[0] + t.[j]);
      j <- j + 1;
    }
    i <- t.[0];
    return (i);
  }
}.

