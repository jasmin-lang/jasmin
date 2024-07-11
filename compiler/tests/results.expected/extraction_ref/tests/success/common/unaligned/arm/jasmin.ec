require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array2 Array3.
require import WArray3 WArray8.



module M = {
  proc main (x:W32.t) : W32.t = {
    
    var a:W32.t Array2.t;
    a <- witness;
    a.[0] <- x;
    a.[1] <- x;
    x <- (get32_direct (WArray8.init32 (fun i => (a).[i])) 2);
    return (x);
  }
  
  proc instack (x:W32.t) : W32.t = {
    
    var r:W32.t;
    var s:W8.t Array3.t;
    s <- witness;
    r <- (W32.of_int 0);
    s.[0] <- (truncateu8 r);
    s <- Array3.init (WArray3.get8 (WArray3.set16_direct (WArray3.init8 (fun i => (s).[i])) 1 ((truncateu16 x))));
    r <- (sigextu32 s.[1]);
    return (r);
  }
}.

