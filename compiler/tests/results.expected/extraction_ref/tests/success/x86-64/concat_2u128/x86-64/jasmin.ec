require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc concat_2u128 (x:W64.t, y:W64.t, z:W64.t) : unit = {
    
    var a:W128.t;
    var b:W128.t;
    var c:W256.t;
    
    a <- (loadW128 Glob.mem (W64.to_uint (x + (W64.of_int 0))));
    b <- (loadW128 Glob.mem (W64.to_uint (y + (W64.of_int 0))));
    c <- (W256.of_int ((W128.to_uint b) %% 2^128 + 2^128 * (W128.to_uint a)));
    Glob.mem <- storeW256 Glob.mem (W64.to_uint (z + (W64.of_int 0))) (c);
    return ();
  }
}.

