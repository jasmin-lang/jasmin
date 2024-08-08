require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array2.
require import WArray2 WArray4.



module M = {
  proc main () : W32.t = {
    
    var r:W32.t;
    var x:W32.t;
    var stk8:W8.t;
    var stk16:W16.t;
    var arr8:W8.t Array2.t;
    var arr16:W16.t Array2.t;
    var y:W32.t;
    arr16 <- witness;
    arr8 <- witness;
    x <- (W32.of_int 0);
    r <- (W32.of_int 0);
    stk8 <- (truncateu8 x);
    stk16 <- (truncateu16 x);
    arr8.[0] <- (truncateu8 x);
    arr8.[1] <- (truncateu8 x);
    arr16.[0] <- (truncateu16 x);
    arr16.[1] <- (truncateu16 x);
    x <- (zeroextu32 stk8);
    y <- (sigextu32 stk8);
    r <- (r + x);
    r <- (r + y);
    x <- (zeroextu32 stk16);
    y <- (sigextu32 stk16);
    r <- (r + x);
    r <- (r + y);
    x <- (zeroextu32 arr8.[0]);
    y <- (sigextu32 arr8.[1]);
    r <- (r + x);
    r <- (r + y);
    x <- (zeroextu32 arr16.[0]);
    y <- (sigextu32 arr16.[1]);
    r <- (r + x);
    r <- (r + y);
    x <- (zeroextu32 (loadW8 Glob.mem (W32.to_uint (r + (W32.of_int 0)))));
    y <- (sigextu32 (loadW8 Glob.mem (W32.to_uint (r + (W32.of_int 0)))));
    r <- (r + x);
    r <- (r + y);
    x <- (zeroextu32 (loadW16 Glob.mem (W32.to_uint (r + (W32.of_int 0)))));
    y <- (sigextu32 (loadW16 Glob.mem (W32.to_uint (r + (W32.of_int 0)))));
    r <- (r + x);
    r <- (r + y);
    return (r);
  }
}.

