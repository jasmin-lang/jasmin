require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc add (arg0:W32.t, arg1:W32.t) : W32.t = {
    
    var x:W32.t;
    
    x <- arg1;
    x <- (arg0 + (x `<<` (W8.of_int 3)));
    return (x);
  }
  
  proc main (arg0:W32.t, arg1:W32.t) : W32.t = {
    var aux: int;
    
    var x:W32.t;
    var z:bool;
    var y:W32.t;
    var n:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W32.t;
    
    ( _0, z,  _1, x) <- MOVS arg0;
    y <- arg1;
    if (z) {
      x <@ add (x, y);
    } else {
      x <@ add (x, y);
    }
    n <- 0;
    while (n < 3) {
      x <@ add (x, y);
      n <- n + 1;
    }
    ( _2, z,  _3,  _4) <- MOVS x;
    while (z) {
      x <@ add (x, y);
      ( _2, z,  _3,  _4) <- MOVS x;
    }
    return (x);
  }
}.

