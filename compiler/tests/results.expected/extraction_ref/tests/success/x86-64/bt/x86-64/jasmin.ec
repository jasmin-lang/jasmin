require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_bt (x:W64.t, y:W64.t) : W64.t = {
    
    var r:W64.t;
    var c:bool;
    
    r <- x;
    c <- BT_16 (truncateu16 x) (truncateu16 y);
    r <- (c ? y : r);
    c <- BT_32 (truncateu32 x) (truncateu32 y);
    r <- (c ? y : r);
    c <- BT_64 x y;
    r <- (c ? y : r);
    c <- BT_16 (truncateu16 x) (W16.of_int 5);
    r <- (c ? y : r);
    c <- BT_32 (truncateu32 x) (W32.of_int 15);
    r <- (c ? y : r);
    c <- BT_64 x (W64.of_int 15);
    r <- (c ? y : r);
    return (r);
  }
}.

