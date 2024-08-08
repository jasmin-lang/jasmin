require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc memcmp (p:W64.t, q:W64.t, n:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    var i:W64.t;
    var a:W64.t;
    var b:W64.t;
    var z:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    i <- aux;
    
    leakages <- LeakCond((i \ult n)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult n)) {
      leakages <- LeakAddr([(W64.to_uint (p + (W64.of_int 0)))]) :: leakages;
      aux <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
      a <- aux;
      leakages <- LeakAddr([(W64.to_uint (q + (W64.of_int 0)))]) :: leakages;
      aux <- (loadW64 Glob.mem (W64.to_uint (q + (W64.of_int 0))));
      b <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 0);
      z <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- ((a <> b) ? z : r);
      r <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (p + (W64.of_int 8));
      p <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (q + (W64.of_int 8));
      q <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult n)) :: LeakAddr([]) :: leakages;
    
    }
    return (r);
  }
}.

