require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array4.
require import WArray4.

abbrev t = Array4.of_list witness [W8.of_int 1; W8.of_int 2; W8.of_int 3; W8.of_int 4].


abbrev g = W32.of_int 42.


module M = {
  proc fourtytwo () : W32.t = {
    
    var r:W32.t;
    
    r <- g;
    return (r);
  }
  
  proc two () : W32.t = {
    
    var r:W32.t;
    
    r <- (zeroextu32 t.[1]);
    return (r);
  }
  
  proc mod4p1 (i:W32.t) : W32.t = {
    
    var r:W32.t;
    var p:W8.t Array4.t;
    p <- witness;
    p <- t;
    i <- (i `&` (W32.of_int 3));
    r <- (zeroextu32 p.[(W32.to_uint i)]);
    return (r);
  }
}.

