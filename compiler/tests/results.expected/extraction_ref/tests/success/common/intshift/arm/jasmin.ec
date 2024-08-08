require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc test_int_shift (x:W32.t) : W32.t = {
    var aux: int;
    
    var i:int;
    
    x <- x;
    i <- 0;
    while (i < 4) {
      x <- (x + (W32.of_int (1 `<<` i)));
      i <- i + 1;
    }
    return (x);
  }
}.

