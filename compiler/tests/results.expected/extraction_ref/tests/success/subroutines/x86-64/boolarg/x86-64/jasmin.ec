require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array8.
require import WArray64.



module M = {
  proc zero (b:bool) : W64.t = {
    var aux: int;
    
    var sum:W64.t;
    var i:int;
    var t:W64.t Array8.t;
    t <- witness;
    i <- 0;
    while (i < 8) {
      t.[i] <- (W64.of_int 0);
      sum <- (W64.of_int i);
      t.[i] <- (b ? sum : t.[i]);
      i <- i + 1;
    }
    sum <- (W64.of_int 0);
    i <- 0;
    while (i < 8) {
      sum <- (sum + t.[i]);
      i <- i + 1;
    }
    return (sum);
  }
  
  proc main (x:W64.t) : W64.t = {
    
    var result:W64.t;
    var b:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    
    ( _0,  _1,  _2,  _3, b) <- TEST_64 x x;
    result <@ zero (b);
    return (result);
  }
}.

