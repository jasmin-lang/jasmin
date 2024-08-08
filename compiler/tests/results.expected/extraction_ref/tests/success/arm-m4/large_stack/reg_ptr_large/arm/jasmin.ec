require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array16385.
require import WArray65540.



module M = {
  proc foo () : W32.t = {
    
    var x:W32.t;
    var z:W32.t;
    var i:W32.t;
    var n:W32.t;
    var s1:W32.t Array16385.t;
    var ps1:W32.t Array16385.t;
    var s2:W32.t Array16385.t;
    var ps2:W32.t Array16385.t;
    ps1 <- witness;
    ps2 <- witness;
    s1 <- witness;
    s2 <- witness;
    z <- (W32.of_int 0);
    i <- (W32.of_int 0);
    n <- (W32.of_int 16385);
    ps1 <- s1;
    ps2 <- s2;
    
    while ((i \ult n)) {
      ps1.[(W32.to_uint i)] <- z;
      ps2.[(W32.to_uint i)] <- z;
      i <- (i + (W32.of_int 1));
    }
    x <- ps1.[0];
    n <- ps2.[0];
    x <- (x + n);
    return (x);
  }
  
  proc main () : W32.t = {
    
    var r:W32.t;
    
    r <@ foo ();
    return (r);
  }
}.

