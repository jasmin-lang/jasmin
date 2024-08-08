require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (x:W64.t, y:W64.t) : W64.t = {
    
    var u:W64.t;
    var r:W64.t;
    
    u <- x;
    r <- (W64.of_int 0);
    if ((x \ult y)) {
      r <- (W64.of_int 1);
    } else {
      
    }
    if ((x \slt y)) {
      r <- (W64.of_int 2);
    } else {
      
    }
    if ((x \ule y)) {
      r <- (W64.of_int 3);
    } else {
      
    }
    if ((x \sle y)) {
      r <- (W64.of_int 4);
    } else {
      
    }
    if ((x = y)) {
      r <- (W64.of_int 5);
    } else {
      
    }
    if ((x <> y)) {
      r <- (W64.of_int 6);
    } else {
      
    }
    if ((y \ult x)) {
      r <- (W64.of_int 7);
    } else {
      
    }
    if ((y \slt x)) {
      r <- (W64.of_int 8);
    } else {
      
    }
    if ((y \ule x)) {
      r <- (W64.of_int 9);
    } else {
      
    }
    if ((y \sle x)) {
      r <- (W64.of_int 10);
    } else {
      
    }
    u <- (u + r);
    return (u);
  }
}.

