require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc aux (a:W256.t, b:W256.t, c:W256.t) : W256.t * W256.t * W256.t = {
    var aux_0: W256.t;
    
    var x:W256.t;
    var y:W256.t;
    var z:W256.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (a `^` b);
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (a `^` c);
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (b `^` c);
    z <- aux_0;
    return (x, y, z);
  }
  
  proc f (x:W256.t, y:W256.t) : W256.t = {
    var aux_2: W256.t;
    var aux_1: W256.t;
    var aux_0: W256.t;
    
    var r:W256.t;
    var m:W256.t;
    var n:W256.t;
    var p:W256.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- x;
    m <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    (aux_2, aux_1, aux_0) <@ aux (x, m, y);
    m <- aux_2;
    n <- aux_1;
    p <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (m `^` p);
    r <- aux_2;
    return (r);
  }
  
  proc main (q:W64.t) : unit = {
    var aux_0: W256.t;
    
    var u:W256.t;
    var v:W256.t;
    var w:W256.t;
    
    leakages <- LeakAddr([(W64.to_uint (q + (W64.of_int 0)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (q + (W64.of_int 0))));
    u <- aux_0;
    leakages <- LeakAddr([(W64.to_uint (q + (W64.of_int 32)))]) :: leakages;
    aux_0 <- (loadW256 Glob.mem (W64.to_uint (q + (W64.of_int 32))));
    v <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ f (u, v);
    w <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- w;
    leakages <- LeakAddr([(W64.to_uint (q + (W64.of_int 64)))]) :: leakages;
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (q + (W64.of_int 64))) (aux_0);
    return ();
  }
}.

