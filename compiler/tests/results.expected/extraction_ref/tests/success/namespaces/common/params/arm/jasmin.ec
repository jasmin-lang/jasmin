require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array1 Array8.
require import WArray4 WArray32.



module M = {
  proc short__sum (t:W32.t Array1.t) : W32.t = {
    var aux: int;
    
    var s:W32.t;
    var c:int;
    
    s <- (W32.of_int 0);
    c <- 0;
    while (c < 1) {
      s <- (s + t.[c]);
      c <- c + 1;
    }
    return (s);
  }
  
  proc long__sum (t:W32.t Array8.t) : W32.t = {
    var aux: int;
    
    var s:W32.t;
    var c:int;
    
    s <- (W32.of_int 0);
    c <- 0;
    while (c < 8) {
      s <- (s + t.[c]);
      c <- c + 1;
    }
    return (s);
  }
  
  proc test (a:W32.t) : W32.t = {
    var aux: int;
    
    var r:W32.t;
    var i:int;
    var x:W32.t Array1.t;
    var y:W32.t Array8.t;
    var t:W32.t;
    x <- witness;
    y <- witness;
    i <- 0;
    while (i < 1) {
      x.[i] <- a;
      i <- i + 1;
    }
    i <- 0;
    while (i < 8) {
      y.[i] <- a;
      i <- i + 1;
    }
    r <- (W32.of_int 0);
    t <@ short__sum (x);
    r <- (r + t);
    t <@ long__sum (y);
    r <- (r + t);
    return (r);
  }
}.

