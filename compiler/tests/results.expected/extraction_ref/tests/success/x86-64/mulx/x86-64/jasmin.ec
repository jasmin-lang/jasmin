require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test (x:W64.t, y:W64.t) : W64.t = {
    
    var z1:W64.t;
    var hi:W64.t;
    var lo:W64.t;
    
    x <- x;
    (hi, lo) <- MULX_64 x y;
    z1 <- (hi `<<` (W8.of_int 1));
    z1 <- (z1 + lo);
    return (z1);
  }
  
  proc test_lo_hi (x:W64.t, y:W64.t) : W64.t = {
    
    var z1:W64.t;
    var lo:W64.t;
    var hi:W64.t;
    
    x <- x;
    (lo, hi) <- MULX_lo_hi_64 x y;
    z1 <- (hi `<<` (W8.of_int 1));
    z1 <- (z1 + lo);
    return (z1);
  }
  
  proc test_hi (x:W64.t, y:W64.t) : W64.t = {
    
    var z1:W64.t;
    var hi:W64.t;
    
    x <- x;
    hi <- MULX_hi_64 x y;
    z1 <- (hi `<<` (W8.of_int 1));
    return (z1);
  }
}.

