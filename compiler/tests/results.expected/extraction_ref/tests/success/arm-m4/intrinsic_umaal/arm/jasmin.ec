require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc umaal (a:W32.t, b:W32.t, c:W32.t, d:W32.t) : W32.t = {
    
    var f:bool;
    
    f <- (d \ult c);
    (a, b) <- UMAAL a b c d;
    (a, b) <- UMAALcc a b c d f a b;
    a <- (a `^` b);
    return (a);
  }
}.

