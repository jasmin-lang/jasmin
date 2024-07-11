require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc case_0 (x:W64.t) : W64.t = {
    
    var a:W64.t;
    var b:W64.t;
    var pf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    
    a <- (W64.of_int 0);
    b <- (W64.of_int 1);
    ( _0,  _1,  _2, pf,  _3) <- TEST_64 x x;
    a <- (pf ? b : a);
    return (a);
  }
  
  proc test_parity () : W64.t = {
    var aux: int;
    
    var result:W64.t;
    var i:int;
    var tmp:W64.t;
    
    result <- (W64.of_int 0);
    i <- 0;
    while (i < 4) {
      tmp <- (W64.of_int i);
      tmp <@ case_0 (tmp);
      result <- (result `<<` (W8.of_int 1));
      result <- (result `|` tmp);
      i <- i + 1;
    }
    return (result);
  }
}.

