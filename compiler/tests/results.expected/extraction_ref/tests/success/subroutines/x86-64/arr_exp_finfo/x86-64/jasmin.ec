require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray16.



module M = {
  proc test1 (t:W64.t Array2.t, p:W64.t Array2.t) : W64.t Array2.t * W64.t Array2.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 2) {
      t.[i] <- (t.[i] + (W64.of_int 1));
      p.[i] <- (p.[i] + (W64.of_int 1));
      i <- i + 1;
    }
    return (p, t);
  }
  
  proc test2 (t:W64.t Array2.t, p:W64.t Array2.t) : W64.t Array2.t * W64.t Array2.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 2) {
      t.[i] <- (t.[i] + (W64.of_int 1));
      p.[i] <- (p.[i] + (W64.of_int 1));
      i <- i + 1;
    }
    return (t, p);
  }
  
  proc test3 (p:W64.t Array2.t, t:W64.t Array2.t) : W64.t Array2.t * W64.t Array2.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 2) {
      t.[i] <- (t.[i] + (W64.of_int 1));
      p.[i] <- (p.[i] + (W64.of_int 1));
      i <- i + 1;
    }
    return (p, t);
  }
  
  proc test4 (p:W64.t Array2.t, t:W64.t Array2.t) : W64.t Array2.t * W64.t Array2.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 2) {
      t.[i] <- (t.[i] + (W64.of_int 1));
      p.[i] <- (p.[i] + (W64.of_int 1));
      i <- i + 1;
    }
    return (t, p);
  }
  
  proc main () : W64.t = {
    var aux: int;
    
    var r:W64.t;
    var s:W64.t Array2.t;
    var p:W64.t Array2.t;
    var i:int;
    var t:W64.t Array2.t;
    p <- witness;
    s <- witness;
    t <- witness;
    p <- s;
    i <- 0;
    while (i < 2) {
      t.[i] <- (W64.of_int i);
      p.[i] <- (W64.of_int i);
      i <- i + 1;
    }
    (p, t) <@ test1 (t, p);
    (t, p) <@ test2 (t, p);
    (p, t) <@ test3 (p, t);
    (t, p) <@ test4 (p, t);
    t.[0] <- (t.[0] + t.[1]);
    t.[0] <- (t.[0] + p.[0]);
    t.[0] <- (t.[0] + p.[1]);
    r <- t.[0];
    return (r);
  }
}.

