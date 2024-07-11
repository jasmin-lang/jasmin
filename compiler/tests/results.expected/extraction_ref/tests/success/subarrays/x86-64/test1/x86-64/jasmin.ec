require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1 Array10.
require import WArray8 WArray80.



module M = {
  proc test () : W64.t = {
    
    var r:W64.t;
    var s:W64.t Array10.t;
    var t:W64.t Array1.t;
    s <- witness;
    t <- witness;
    t <- (Array1.init (fun i => s.[0 + i]));
    t <- Array1.init (WArray8.get64 (WArray8.set64_direct (WArray8.init64 (fun i => (t).[i])) 0 ((W64.of_int 0))));
    s <- Array10.init (fun i => if 0 <= i < 0 + 1 then t.[i-0] else s.[i]);
    r <- s.[0];
    return (r);
  }
}.

