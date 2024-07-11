require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray16.



module M = {
  proc inc (x:int) : int = {
    
    var y:int;
    
    y <- (x + 1);
    return (y);
  }
  
  proc snd (a:W64.t, b:W64.t) : W64.t = {
    
    var r:W64.t;
    var t:W64.t Array2.t;
    var k:int;
    t <- witness;
    t.[0] <- a;
    t.[1] <- b;
    k <@ inc (0);
    r <- t.[k];
    return (r);
  }
}.

