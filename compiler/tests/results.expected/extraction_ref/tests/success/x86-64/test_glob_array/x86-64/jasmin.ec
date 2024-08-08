require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array4 Array9.
require import WArray32 WArray36.

abbrev glob_t = Array4.of_list witness [W64.of_int 0; W64.of_int 1; W64.of_int 2; W64.of_int 3].


abbrev t32 = Array9.of_list witness [W32.of_int 4; W32.of_int 0; W32.of_int 5; W32.of_int 0; W32.of_int 6; W32.of_int 0; W32.of_int 7; W32.of_int 0; W32.of_int 8].


module M = {
  proc sum (x:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r <- x;
    r <- (r + glob_t.[0]);
    r <- (r + glob_t.[1]);
    r <- (r + glob_t.[2]);
    r <- (r + glob_t.[3]);
    return (r);
  }
  
  proc sum1 (x:W64.t) : W64.t = {
    var aux: int;
    
    var r:W64.t;
    var i:int;
    
    r <- x;
    i <- 0;
    while (i < 4) {
      r <- (r + glob_t.[i]);
      i <- i + 1;
    }
    return (r);
  }
  
  proc sum32 (x:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r <- x;
    r <- (r + (get64 (WArray36.init32 (fun i => (t32).[i])) 0));
    r <- (r + (get64 (WArray36.init32 (fun i => (t32).[i])) 1));
    r <- (r + (get64 (WArray36.init32 (fun i => (t32).[i])) 2));
    r <- (r + (get64 (WArray36.init32 (fun i => (t32).[i])) 3));
    return (r);
  }
  
  proc suma (x:W32.t) : W32.t = {
    
    var r:W32.t;
    
    r <- x;
    r <- (r + t32.[0]);
    r <- (r + t32.[1]);
    r <- (r + t32.[2]);
    r <- (r + t32.[3]);
    return (r);
  }
}.

