require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc movt () : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var n:bool;
    var z:bool;
    var c:bool;
    var v:bool;
    
    x <- (W32.of_int 0);
    x <- MOVT x (W16.of_int 0);
    x <- MOVT x (W16.of_int 1);
    x <- MOVT x (W16.of_int 65535);
    (n, z, c, v) <- CMP x (W32.of_int 0);
    x <- MOVTcc x (W16.of_int 3) z x;
    x <- MOVTcc x (W16.of_int 3) (! z) x;
    x <- MOVTcc x (W16.of_int 3) c x;
    x <- MOVTcc x (W16.of_int 3) (! c) x;
    x <- MOVTcc x (W16.of_int 3) n x;
    x <- MOVTcc x (W16.of_int 3) (! n) x;
    x <- MOVTcc x (W16.of_int 3) v x;
    x <- MOVTcc x (W16.of_int 3) (! v) x;
    x <- MOVTcc x (W16.of_int 3) (c /\ (! z)) x;
    x <- MOVTcc x (W16.of_int 3) ((! c) \/ z) x;
    x <- MOVTcc x (W16.of_int 3) (n = v) x;
    x <- MOVTcc x (W16.of_int 3) (! (n = v)) x;
    x <- MOVTcc x (W16.of_int 3) ((! z) /\ (n = v)) x;
    x <- MOVTcc x (W16.of_int 3) (z \/ (! (n = v))) x;
    res_0 <- x;
    return (res_0);
  }
}.

