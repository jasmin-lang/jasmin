require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc memcmp (p:W32.t, q:W32.t, n:W32.t) : W32.t = {
    var aux: W32.t;
    
    var res_0:W32.t;
    var i:W32.t;
    var a:W32.t;
    var b:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 1);
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    i <- aux;
    
    leakages <- LeakCond((i \ult n)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult n)) {
      leakages <- LeakAddr([(W32.to_uint (p + (W32.of_int 0)))]) :: leakages;
      aux <- (loadW32 Glob.mem (W32.to_uint (p + (W32.of_int 0))));
      a <- aux;
      leakages <- LeakAddr([(W32.to_uint (q + (W32.of_int 0)))]) :: leakages;
      aux <- (loadW32 Glob.mem (W32.to_uint (q + (W32.of_int 0))));
      b <- aux;
      leakages <- LeakCond((a <> b)) :: LeakAddr([]) :: leakages;
      if ((a <> b)) {
        leakages <- LeakAddr([]) :: leakages;
        aux <- (W32.of_int 0);
        res_0 <- aux;
      } else {
        
      }
      leakages <- LeakAddr([]) :: leakages;
      aux <- (p + (W32.of_int 4));
      p <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (q + (W32.of_int 4));
      q <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (i + (W32.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult n)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- res_0;
    res_0 <- aux;
    return (res_0);
  }
}.

