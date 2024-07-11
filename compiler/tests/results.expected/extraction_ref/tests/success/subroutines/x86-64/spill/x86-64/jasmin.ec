require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array12.
require import WArray96.



module M = {
  proc gosub (a:W64.t) : W64.t = {
    var aux: int;
    
    var k:W64.t;
    var i:int;
    var tab:W64.t Array12.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    tab <- witness;
    ( _0,  _1,  _2,  _3,  _4, k) <- set0_64 ;
    i <- 0;
    while (i < 12) {
      tab.[i] <- a;
      i <- i + 1;
    }
    i <- 0;
    while (i < 12) {
      k <- (k + tab.[i]);
      i <- i + 1;
    }
    return (k);
  }
  
  proc main (x:W64.t) : W64.t = {
    
    var r:W64.t;
    var t:W64.t;
    
    r <- x;
    t <@ gosub (x);
    r <- (r + t);
    return (r);
  }
}.

