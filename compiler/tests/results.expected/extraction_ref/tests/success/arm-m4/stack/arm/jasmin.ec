require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc leaf () : W32.t = {
    var aux: int;
    
    var f:W32.t;
    var r:W32.t;
    var i:int;
    
    f <- (W32.of_int 0);
    r <- f;
    i <- 0;
    while (i < 4) {
      f <- r;
      f <- (f + (W32.of_int i));
      r <- f;
      i <- i + 1;
    }
    f <- r;
    return (f);
  }
  
  proc main (x:W32.t) : W32.t = {
    
    var s:W32.t;
    var k:W32.t;
    
    s <- x;
    k <@ leaf ();
    x <- s;
    x <- (x + k);
    return (x);
  }
}.

