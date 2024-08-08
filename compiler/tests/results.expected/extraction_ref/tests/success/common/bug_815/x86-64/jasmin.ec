require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1 Array4.
require import WArray4.



module M = {
  proc snd (x:W32.t, y:W32.t) : W32.t = {
    var aux_0: W8.t Array4.t;
    var aux: W8.t Array4.t;
    
    var a:W32.t Array1.t;
    var b:W32.t Array1.t;
    a <- witness;
    b <- witness;
    a.[0] <- x;
    b.[0] <- y;
    (a, b) <- swap_ a b;
    x <- a.[0];
    return (x);
  }
}.

