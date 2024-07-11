require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_while (x:W64.t) : W64.t = {
    
    var r:W64.t;
    var i:W64.t;
    var zf:bool;
    var _of_:bool;
    var _sf_:bool;
    var  _0:bool;
    
    i <- (W64.of_int 10);
    r <- (W64.of_int 0);
    r <- (r + (W64.of_int 1));
    (_of_, _sf_,  _0, zf, i) <- DEC_64 i;
    while ((! zf)) {
      r <- (r + (W64.of_int 2));
      r <- (r + (W64.of_int 1));
      (_of_, _sf_,  _0, zf, i) <- DEC_64 i;
    }
    r <- (r + x);
    return (r);
  }
  
  proc zero (y:W64.t) : W64.t = {
    
    var x:W64.t;
    var b:bool;
    
    x <- y;
    b <- (x \slt (W64.of_int 0));
    while (b) {
      x <- (x + (W64.of_int 1));
      b <- (x \slt (W64.of_int 0));
    }
    return (x);
  }
}.

