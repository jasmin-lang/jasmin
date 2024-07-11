require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array12.
require import WArray96.



module M = {
  proc test_for () : W64.t = {
    var aux: int;
    
    var sum:W64.t;
    var i:int;
    var t:W64.t Array12.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    t <- witness;
    i <- 0;
    while (i < 12) {
      t.[i] <- (W64.of_int i);
      i <- i + 1;
    }
    (_of_, _cf_, _sf_,  _0, _zf_, sum) <- set0_64 ;
    i <- 0;
    while (i < 12) {
      sum <- (sum + t.[i]);
      i <- i + 1;
    }
    return (sum);
  }
}.

