require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray16.



module M = {
  proc f (x:W64.t, y:W64.t) : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t;
    
    var t:W64.t;
    var i_0:W64.t Array2.t;
    var r:W64.t Array2.t;
    var q:W64.t;
    i_0 <- witness;
    r <- witness;
    i_0.[0] <- x;
    i_0.[1] <- y;
    (aux_0, aux) <- mulu_64 i_0.[0] i_0.[1];
    r.[0] <- aux_0;
    r.[1] <- aux;
    q <- (r.[0] + r.[1]);
    t <- q;
    return (t);
  }
  
  proc g (x:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r <- x;
    r <- (r * (W64.of_int 38));
    return (r);
  }
  
  proc h (x:W64.t) : W64.t = {
    
    var lo:W64.t;
    var y:W64.t;
    var hi:W64.t;
    
    y <- x;
    (hi, lo) <- mulu_64 y (W64.of_int 38);
    lo <- (lo + hi);
    return (lo);
  }
  
  proc i (x:W64.t) : W64.t = {
    
    var y:W64.t;
    
    y <- x;
    y <- (y * (W64.of_int 18446744073709551615));
    return (y);
  }
  
  proc mul32 (x:W32.t, y:W32.t) : W32.t = {
    
    var r:W32.t;
    var a:W32.t;
    var b:W32.t;
    var  _0:W32.t;
    
    a <- x;
    b <- y;
    ( _0, r) <- mulu_32 a b;
    return (r);
  }
}.

