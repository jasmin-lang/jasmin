require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray16 WArray32.



module M = {
  var leakages : leakages_t
  
  proc main (x:W64.t) : W128.t = {
    var aux: int;
    var aux_0: W16.t;
    var aux_1: W128.t;
    
    var r:W128.t;
    var i:int;
    var a:W128.t Array2.t;
    a <- witness;
    leakages <- LeakFor(0,16) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 16) {
      leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int (2 * i))))]) :: leakages;
      aux_0 <- (loadW16 Glob.mem (W64.to_uint (x + (W64.of_int (2 * i)))));
      leakages <- LeakAddr([i]) :: leakages;
      a <- Array2.init (WArray32.get128 (WArray32.set16 (WArray32.init128 (fun i_0 => (a).[i_0])) i (aux_0)));
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- set0_128 ;
    r <- aux_1;
    leakages <- LeakFor(0,3) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 3) {
      leakages <- LeakAddr([(i * 8)]) :: leakages;
      aux_1 <- (r `^` (get128_direct (WArray32.init128 (fun i_0 => (a).[i_0])) (i * 8)));
      r <- aux_1;
      i <- i + 1;
    }
    return (r);
  }
  
  proc sopndest () : W64.t = {
    var aux_0: W64.t;
    var aux: W128.t;
    
    var r:W64.t;
    var x:W128.t;
    var a:W128.t Array2.t;
    a <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- set0_128 ;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([8]) :: leakages;
    a <- Array2.init (WArray32.get128 (WArray32.set128_direct (WArray32.init128 (fun i => (a).[i])) 8 (aux)));
    leakages <- LeakAddr([8]) :: leakages;
    aux_0 <- (get64_direct (WArray32.init128 (fun i => (a).[i])) 8);
    r <- aux_0;
    return (r);
  }
  
  proc add_in_mem (x:W64.t, y:W64.t) : W64.t = {
    var aux: W64.t;
    
    var s:W64.t Array2.t;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    s.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([1]) :: leakages;
    s.[1] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([4]) :: leakages;
    s <- Array2.init (WArray16.get64 (WArray16.set64_direct (WArray16.init64 (fun i => (s).[i])) 4 (aux)));
    leakages <- LeakAddr([4]) :: leakages;
    aux <- ((get64_direct (WArray16.init64 (fun i => (s).[i])) 4) + y);
    leakages <- LeakAddr([4]) :: leakages;
    s <- Array2.init (WArray16.get64 (WArray16.set64_direct (WArray16.init64 (fun i => (s).[i])) 4 (aux)));
    leakages <- LeakAddr([0]) :: leakages;
    aux <- s.[0];
    x <- aux;
    return (x);
  }
}.

