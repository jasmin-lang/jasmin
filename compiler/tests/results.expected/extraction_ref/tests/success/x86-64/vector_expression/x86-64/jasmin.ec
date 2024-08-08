require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc toto () : W64.t = {
    
    var r:W64.t;
    var x:W256.t;
    var y:W256.t;
    var v:W128.t;
    var w:W128.t;
    
    x <- (W256.of_int 0);
    y <- (W256.of_int 1);
    x <- (x \vadd64u256 y);
    x <- (x \vadd64u256 y);
    x <- (x \vsub64u256 y);
    x <- (x \vsub64u256 y);
    x <- (x \vmul64u256 y);
    x <- (x \vmul64u256 y);
    x <- (x \vmul8u256 y);
    x <- ((W256.of_int 219) \vmul16u256 (W256.of_int 5));
    x <- (x \vshl64u256 (W8.of_int 32));
    x <- (x \vshr64u256 (W8.of_int 32));
    x <- (x \vshl64u256 (W8.of_int 32));
    x <- (x \vsar64u256 (W8.of_int 32));
    x <- (x \vsar64u256 (W8.of_int 27));
    v <- (W128.of_int 0);
    w <- (W128.of_int 1);
    v <- (v \vadd32u128 w);
    v <- (v \vadd32u128 w);
    v <- (v \vsub32u128 w);
    v <- (v \vsub32u128 w);
    v <- (v \vmul32u128 w);
    v <- (v \vmul32u128 w);
    v <- (v \vmul8u128 w);
    v <- ((W128.of_int 219) \vmul16u128 (W128.of_int 5));
    v <- (v \vshl32u128 (W8.of_int 32));
    v <- (v \vshr32u128 (W8.of_int 32));
    v <- (v \vshl32u128 (W8.of_int 32));
    v <- (v \vsar32u128 (W8.of_int 32));
    r <- (W64.of_int 0);
    return (r);
  }
}.

