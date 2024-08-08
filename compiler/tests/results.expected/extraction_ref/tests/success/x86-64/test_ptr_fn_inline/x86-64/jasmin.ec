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
      p.[i] <- (W64.of_int i);
      i <- i + 1;
    }
    return (p);
  }
  
  proc foo () : W64.t = {
    var aux: int;
    
    var r:W64.t;
    var s:W64.t Array3.t;
    var i:int;
    s <- witness;
    s <@ init (s);
    r <- (W64.of_int 0);
    i <- 0;
    while (i < 3) {
      r <- (r + s.[i]);
      i <- i + 1;
    }
    return (r);
  }
}.

