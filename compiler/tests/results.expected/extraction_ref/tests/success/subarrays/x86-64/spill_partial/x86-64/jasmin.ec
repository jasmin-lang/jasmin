require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2 Array4.
require import WArray16 WArray32.



module M = {
  proc f (r:W64.t Array2.t) : W64.t Array2.t = {
    
    
    
    r.[0] <- (W64.of_int 1);
    return (r);
  }
  
  proc test (r:W64.t Array4.t) : W64.t Array4.t * W64.t = {
    
    var res_0:W64.t;
    var r2:W64.t Array2.t;
    r2 <- witness;
    r2 <- (Array2.init (fun i => r.[1 + i]));
    (* Erased call to spill *)
    r2 <@ f (r2);
    (* Erased call to unspill *)
    r <- Array4.init (fun i => if 1 <= i < 1 + 2 then r2.[i-1] else r.[i]);
    res_0 <- r.[1];
    return (r, res_0);
  }
}.

