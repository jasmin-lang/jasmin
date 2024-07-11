require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray32.

abbrev c7 = W128.of_int 7.


abbrev c3 = W128.of_int 3.


module M = {
  proc add (x:W128.t, z:W128.t) : W128.t = {
    
    var y:W128.t;
    var t:W128.t Array2.t;
    t <- witness;
    y <- z;
    t.[0] <- x;
    t.[1] <- y;
    x <- (x `^` t.[0]);
    y <- (y `^` t.[1]);
    x <- (x `^` y);
    return (x);
  }
  
  proc main () : W128.t = {
    
    var x:W128.t;
    var y:W128.t;
    var z:W128.t;
    var s:W128.t;
    
    x <- c3;
    y <- c7;
    z <- set0_128 ;
    s <- z;
    x <@ add (x, y);
    x <- (x `^` s);
    x <@ add (x, y);
    x <- (x `^` s);
    x <@ add (x, y);
    x <- (x `^` s);
    return (x);
  }
}.

