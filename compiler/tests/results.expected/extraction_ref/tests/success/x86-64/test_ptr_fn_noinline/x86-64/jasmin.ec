require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array3.
require import WArray24.



module M = {
  proc init (p:W64.t Array3.t) : W64.t Array3.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 3) {
      p.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    return (p);
  }
  
  proc set (p:W64.t Array3.t) : W64.t Array3.t * W64.t = {
    
    var r:W64.t;
    
    p.[0] <- (W64.of_int 1);
    r <- p.[1];
    return (p, r);
  }
  
  proc foo5 () : W64.t = {
    
    var r:W64.t;
    var s:W64.t Array3.t;
    s <- witness;
    s <@ init (s);
    (s, r) <@ set (s);
    r <- (r + s.[0]);
    return (r);
  }
}.

