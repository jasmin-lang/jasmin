require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1 Array2.
require import WArray8 WArray16.

abbrev g = Array2.of_list witness [W64.of_int 42; W64.of_int 137].


abbrev z = W64.of_int 0.


module M = {
  proc mem2mem (m:W64.t) : W64.t = {
    
    var r:W64.t;
    var s:W64.t Array2.t;
    var p:W64.t Array1.t;
    var q:W64.t Array1.t;
    p <- witness;
    q <- witness;
    s <- witness;
    r <- (W64.of_int 0);
    s.[0] <- (W64.of_int 0);
    p <- (Array1.init (fun i => g.[0 + i]));
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (m + (W64.of_int 0))) ((loadW64 Glob.mem (W64.to_uint (m + (W64.of_int 8)))));
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (m + (W64.of_int 0))) (z);
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (m + (W64.of_int 8))) (g.[0]);
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (m + (W64.of_int 16))) (s.[0]);
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (m + (W64.of_int 24))) (p.[0]);
    s.[0] <- (loadW64 Glob.mem (W64.to_uint (m + (W64.of_int 0))));
    r <- (r + s.[0]);
    s.[0] <- g.[0];
    r <- (r + s.[0]);
    s.[1] <- s.[0];
    r <- (r + s.[1]);
    s.[0] <- p.[0];
    r <- (r + s.[0]);
    q <- (Array1.init (fun i => s.[1 + i]));
    q.[0] <- (loadW64 Glob.mem (W64.to_uint (m + (W64.of_int 0))));
    r <- (r + q.[0]);
    q.[0] <- g.[0];
    r <- (r + q.[0]);
    q.[0] <- s.[0];
    r <- (r + q.[0]);
    q.[0] <- p.[0];
    r <- (r + q.[0]);
    return (r);
  }
}.

