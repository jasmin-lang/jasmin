require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test () : W64.t = {
    
    var r:W64.t;
    var x:W64.t;
    var y:W64.t;
    var z:W64.t;
    var cf:bool;
    
    x <- (W64.of_int 0);
    y <- x;
    z <- y;
    x <- (x + (W64.of_int 420));
    x <- (x + (W64.of_int 737894400000));
    y <- (y - (W64.of_int (- 2147483648)));
    y <- (y - (W64.of_int 2147483647));
    (cf, y) <- sbb_64 y (W64.of_int 20015998348237) false;
    (cf, z) <- adc_64 z (W64.of_int 42) cf;
    (cf, z) <- adc_64 z (W64.of_int (- 2147483649)) cf;
    (cf, z) <- sbb_64 z (W64.of_int 0) cf;
    x <- (x * (W64.of_int 12));
    z <- (z * (W64.of_int (- 2147483650)));
    x <- (x `|` (W64.of_int 33));
    y <- (y `|` (W64.of_int 737894400000));
    z <- (z `^` (W64.of_int (- 1)));
    x <- (x `^` (W64.of_int 2147483648));
    y <- (y `&` (W64.of_int (- 2147483648)));
    z <- (z `&` (W64.of_int 737894400000));
    r <- (W64.of_int 0);
    r <- (r `&` x);
    r <- (r `&` y);
    r <- (r `&` z);
    return (r);
  }
}.

