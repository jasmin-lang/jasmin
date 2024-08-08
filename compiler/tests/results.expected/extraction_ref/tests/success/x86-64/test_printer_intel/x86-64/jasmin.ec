require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1 Array10.
require import WArray16 WArray80.



module M = {
  proc foo (plain:W64.t, output:W64.t) : unit = {
    var aux: int;
    
    var i:int;
    var s_k:W64.t Array10.t;
    var x0:W128.t;
    var s_0:W128.t Array1.t;
    var j:W64.t;
    var pi:W8.t;
    s_0 <- witness;
    s_k <- witness;
    i <- 0;
    while (i < 10) {
      s_k.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    x0 <- set0_128 ;
    s_0.[0] <- x0;
    j <- (W64.of_int 0);
    
    while ((j \ult (W64.of_int 80))) {
      pi <- (loadW8 Glob.mem (W64.to_uint (plain + j)));
      pi <- (pi `^` (get8 (WArray80.init64 (fun i_0 => (s_k).[i_0])) (W64.to_uint j)));
      pi <- (pi `^` (get8 (WArray16.init128 (fun i_0 => (s_0).[i_0])) 0));
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (output + j)) (pi);
      j <- (j + (W64.of_int 1));
    }
    return ();
  }
}.

