require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc opsize_test (x:W64.t) : W8.t = {
    
    var r:W8.t;
    var y:W32.t;
    
    y <- (truncateu32 x);
    y <- (y + (truncateu32 x));
    y <- ((y \ult (W32.of_int 0)) ? (truncateu32 x) : y);
    x <- (x `>>` (W8.of_int 32));
    x <- (x `|>>` (W8.of_int 8));
    r <- (truncateu8 x);
    r <- (r `>>` (W8.of_int 1));
    r <- (r `^` (truncateu8 y));
    return (r);
  }
}.

