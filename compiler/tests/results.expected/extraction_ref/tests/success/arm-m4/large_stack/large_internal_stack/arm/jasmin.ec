require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array1025.
require import WArray4100.



module M = {
  proc large () : W32.t = {
    
    var s:W32.t;
    var st:W32.t Array1025.t;
    var t:W32.t Array1025.t;
    var i:W32.t;
    var n:W32.t;
    var tmp:W32.t;
    st <- witness;
    t <- witness;
    t <- st;
    i <- (W32.of_int 0);
    n <- (W32.of_int (1025 - 1));
    n <- (n + (W32.of_int 1));
    
    while ((i \ult n)) {
      t.[(W32.to_uint i)] <- i;
      i <- (i + (W32.of_int 1));
    }
    i <- (W32.of_int 0);
    s <- (W32.of_int 0);
    
    while ((i \ult n)) {
      tmp <- t.[(W32.to_uint i)];
      s <- (s + tmp);
      i <- (i + (W32.of_int 1));
    }
    return (s);
  }
  
  proc main () : W32.t = {
    
    var s:W32.t;
    
    s <@ large ();
    return (s);
  }
}.

