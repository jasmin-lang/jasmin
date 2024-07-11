require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1 Array2 Array16.
require import WArray16.



module M = {
  proc test () : W64.t = {
    var aux_0: W8.t Array16.t;
    var aux: W8.t Array16.t;
    
    var res_0:W64.t;
    var s:W64.t Array2.t;
    var r1:W64.t Array2.t;
    var r2:W64.t Array2.t;
    r1 <- witness;
    r2 <- witness;
    s <- witness;
    s.[0] <- (W64.of_int 0);
    s.[1] <- (W64.of_int 1);
    r1 <- s;
    r1.[0] <- (W64.of_int 2);
    r2 <- s;
    r2.[1] <- (W64.of_int 3);
    (r1, r2) <- swap_ r1 r2;
    s <- Array2.init (fun i => if 0 <= i < 0 + 1 then (Array1.init (fun i => r2.[0 + i])).[i-0] else s.[i]);
    s <- Array2.init (fun i => if 1 <= i < 1 + 1 then (Array1.init (fun i => r1.[1 + i])).[i-1] else s.[i]);
    res_0 <- (W64.of_int 0);
    res_0 <- (res_0 + s.[1]);
    return (res_0);
  }
}.

