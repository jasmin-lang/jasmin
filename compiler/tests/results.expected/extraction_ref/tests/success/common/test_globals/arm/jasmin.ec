require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array2.
require import WArray8.

abbrev g = W32.of_int 3.


abbrev f_0 = W32.of_int 10.


abbrev t = Array2.of_list witness [W32.of_int 10; W32.of_int 3].


abbrev e = W32.of_int 5.


abbrev d = W32.of_int 30.


abbrev c = W32.of_int 30.


abbrev b = W32.of_int 3.


abbrev a = W32.of_int 10.


module M = {
  proc f (x:W32.t) : W32.t = {
    
    var r:W32.t;
    
    r <- x;
    r <- (r + (W32.of_int 10));
    r <- (r + (W32.of_int (10 %/ 3)));
    x <- a;
    r <- (r + x);
    x <- b;
    r <- (r + x);
    x <- c;
    r <- (r + x);
    x <- d;
    r <- (r + x);
    x <- e;
    r <- (r + x);
    x <- f_0;
    r <- (r + x);
    x <- g;
    r <- (r + x);
    return (r);
  }
}.

