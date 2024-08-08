require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1 Array2.
require import WArray8 WArray16.

abbrev g = Array2.of_list witness [W64.of_int 42; W64.of_int 137].


abbrev z = W64.of_int 0.


module M = {
  var leakages : leakages_t
  
  proc mem2mem (m:W64.t) : W64.t = {
    var aux: W64.t;
    var aux_0: W64.t Array1.t;
    
    var r:W64.t;
    var s:W64.t Array2.t;
    var p:W64.t Array1.t;
    var q:W64.t Array1.t;
    p <- witness;
    q <- witness;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    s.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- (Array1.init (fun i => g.[0 + i]));
    p <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (m + (W64.of_int 8)))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (m + (W64.of_int 8))));
    leakages <- LeakAddr([(W64.to_uint (m + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (m + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- z;
    leakages <- LeakAddr([(W64.to_uint (m + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (m + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([0]) :: leakages;
    aux <- g.[0];
    leakages <- LeakAddr([(W64.to_uint (m + (W64.of_int 8)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (m + (W64.of_int 8))) (aux);
    leakages <- LeakAddr([0]) :: leakages;
    aux <- s.[0];
    leakages <- LeakAddr([(W64.to_uint (m + (W64.of_int 16)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (m + (W64.of_int 16))) (aux);
    leakages <- LeakAddr([0]) :: leakages;
    aux <- p.[0];
    leakages <- LeakAddr([(W64.to_uint (m + (W64.of_int 24)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (m + (W64.of_int 24))) (aux);
    leakages <- LeakAddr([(W64.to_uint (m + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (m + (W64.of_int 0))));
    leakages <- LeakAddr([0]) :: leakages;
    s.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (r + s.[0]);
    r <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- g.[0];
    leakages <- LeakAddr([0]) :: leakages;
    s.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (r + s.[0]);
    r <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- s.[0];
    leakages <- LeakAddr([1]) :: leakages;
    s.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (r + s.[1]);
    r <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- p.[0];
    leakages <- LeakAddr([0]) :: leakages;
    s.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (r + s.[0]);
    r <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux_0 <- (Array1.init (fun i => s.[1 + i]));
    q <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (m + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (m + (W64.of_int 0))));
    leakages <- LeakAddr([0]) :: leakages;
    q.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (r + q.[0]);
    r <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- g.[0];
    leakages <- LeakAddr([0]) :: leakages;
    q.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (r + q.[0]);
    r <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- s.[0];
    leakages <- LeakAddr([0]) :: leakages;
    q.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (r + q.[0]);
    r <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- p.[0];
    leakages <- LeakAddr([0]) :: leakages;
    q.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (r + q.[0]);
    r <- aux;
    return (r);
  }
}.

