require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array3.
require import WArray24.



module M = {
  proc foo (px:W64.t Array3.t) : W64.t = {
    
    var res_x:W64.t;
    var y:W64.t Array3.t;
    y <- witness;
    px <- y;
    y.[0] <- (W64.of_int 666);
    res_x <- px.[0];
    return (res_x);
  }
  
  proc main () : W64.t = {
    
    var res_0:W64.t;
    var x:W64.t Array3.t;
    var  _0:W64.t;
    x <- witness;
    x.[0] <- (W64.of_int 41);
     _0 <@ foo (x);
    res_0 <- x.[0];
    return (res_0);
  }
}.

