require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc memcmp (p:W64.t, q:W64.t, n:W64.t) : W64.t = {
    
    var r:W64.t;
    var i:W64.t;
    var a:W64.t;
    var b:W64.t;
    var z:W64.t;
    
    r <- (W64.of_int 1);
    i <- (W64.of_int 0);
    
    while ((i \ult n)) {
      a <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
      b <- (loadW64 Glob.mem (W64.to_uint (q + (W64.of_int 0))));
      z <- (W64.of_int 0);
      r <- ((a <> b) ? z : r);
      p <- (p + (W64.of_int 8));
      q <- (q + (W64.of_int 8));
      i <- (i + (W64.of_int 1));
    }
    return (r);
  }
}.

