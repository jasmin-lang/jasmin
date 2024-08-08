require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray16 WArray32.



module M = {
  proc main (x:W64.t) : W128.t = {
    var aux: int;
    
    var r:W128.t;
    var i:int;
    var a:W128.t Array2.t;
    a <- witness;
    i <- 0;
    while (i < 16) {
      a <- Array2.init (WArray32.get128 (WArray32.set16 (WArray32.init128 (fun i_0 => (a).[i_0])) i ((loadW16 Glob.mem (W64.to_uint (x + (W64.of_int (2 * i))))))));
      i <- i + 1;
    }
    r <- set0_128 ;
    i <- 0;
    while (i < 3) {
      r <- (r `^` (get128_direct (WArray32.init128 (fun i_0 => (a).[i_0])) (i * 8)));
      i <- i + 1;
    }
    return (r);
  }
  
  proc sopndest () : W64.t = {
    
    var r:W64.t;
    var x:W128.t;
    var a:W128.t Array2.t;
    a <- witness;
    x <- set0_128 ;
    a <- Array2.init (WArray32.get128 (WArray32.set128_direct (WArray32.init128 (fun i => (a).[i])) 8 (x)));
    r <- (get64_direct (WArray32.init128 (fun i => (a).[i])) 8);
    return (r);
  }
  
  proc add_in_mem (x:W64.t, y:W64.t) : W64.t = {
    
    var s:W64.t Array2.t;
    s <- witness;
    s.[0] <- (W64.of_int 0);
    s.[1] <- (W64.of_int 0);
    s <- Array2.init (WArray16.get64 (WArray16.set64_direct (WArray16.init64 (fun i => (s).[i])) 4 (x)));
    s <- Array2.init (WArray16.get64 (WArray16.set64_direct (WArray16.init64 (fun i => (s).[i])) 4 (((get64_direct (WArray16.init64 (fun i => (s).[i])) 4) + y))));
    x <- s.[0];
    return (x);
  }
}.

