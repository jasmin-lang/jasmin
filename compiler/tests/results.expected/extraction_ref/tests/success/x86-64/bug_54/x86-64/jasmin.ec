require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2 Array3 Array4.
require import WArray3 WArray4.



module M = {
  proc main () : W8.t = {
    
    var res_0:W8.t;
    var b:W8.t Array4.t;
    var a:W8.t Array3.t;
    a <- witness;
    b <- witness;
    b.[1] <- (W8.of_int 42);
    a <- Array3.init (fun i => if 0 <= i < 0 + 2 then (Array2.init (fun i => b.[1 + i])).[i-0] else a.[i]);
    res_0 <- a.[0];
    return (res_0);
  }
}.

