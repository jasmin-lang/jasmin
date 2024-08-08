require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray16.



module M = {
  var leakages : leakages_t
  
  proc f (x:W64.t, y:W64.t) : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t;
    
    var t:W64.t;
    var i_0:W64.t Array2.t;
    var r:W64.t Array2.t;
    var q:W64.t;
    i_0 <- witness;
    r <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    leakages <- LeakAddr([0]) :: leakages;
    i_0.[0] <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- y;
    leakages <- LeakAddr([1]) :: leakages;
    i_0.[1] <- aux_0;
    leakages <- LeakAddr([1; 0]) :: leakages;
    (aux_0, aux) <- mulu_64 i_0.[0] i_0.[1];
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux;
    leakages <- LeakAddr([1; 0]) :: leakages;
    aux_0 <- (r.[0] + r.[1]);
    q <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- q;
    t <- aux_0;
    return (t);
  }
  
  proc g (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r * (W64.of_int 38));
    r <- aux;
    return (r);
  }
  
  proc h (x:W64.t) : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t;
    
    var lo:W64.t;
    var y:W64.t;
    var hi:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    y <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- mulu_64 y (W64.of_int 38);
    hi <- aux_0;
    lo <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (lo + hi);
    lo <- aux_0;
    return (lo);
  }
  
  proc i (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var y:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (y * (W64.of_int 18446744073709551615));
    y <- aux;
    return (y);
  }
  
  proc mul32 (x:W32.t, y:W32.t) : W32.t = {
    var aux_0: W32.t;
    var aux: W32.t;
    
    var r:W32.t;
    var a:W32.t;
    var b:W32.t;
    var  _0:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- y;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- mulu_32 a b;
     _0 <- aux_0;
    r <- aux;
    return (r);
  }
}.

