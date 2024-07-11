require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array1 Array65536.
require import WArray4 WArray262144.



module M = {
  proc main () : W32.t = {
    
    var res_0:W32.t;
    var i:W32.t;
    var n:W32.t;
    var s:W32.t Array65536.t;
    var r:W32.t Array65536.t;
    var r2:W32.t Array1.t;
    r <- witness;
    r2 <- witness;
    s <- witness;
    i <- (W32.of_int 0);
    res_0 <- (W32.of_int 0);
    n <- (W32.of_int 65536);
    
    while ((i \ult n)) {
      s.[(W32.to_uint i)] <- res_0;
    }
    r <- s;
    r2 <- (Array1.init (fun i_0 => r.[(65536 - 1) + i_0]));
    res_0 <- r2.[0];
    return (res_0);
  }
}.

