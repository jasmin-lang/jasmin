require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1 Array10.
require import WArray16 WArray80.



module M = {
  var leakages : leakages_t
  
  proc foo (plain:W64.t, output:W64.t) : unit = {
    var aux: int;
    var aux_2: W8.t;
    var aux_0: W64.t;
    var aux_1: W128.t;
    
    var i:int;
    var s_k:W64.t Array10.t;
    var x0:W128.t;
    var s_0:W128.t Array1.t;
    var j:W64.t;
    var pi:W8.t;
    s_0 <- witness;
    s_k <- witness;
    leakages <- LeakFor(0,10) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 10) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([i]) :: leakages;
      s_k.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- set0_128 ;
    x0 <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- x0;
    leakages <- LeakAddr([0]) :: leakages;
    s_0.[0] <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    j <- aux_0;
    
    leakages <- LeakCond((j \ult (W64.of_int 80))) :: LeakAddr([]) :: leakages;
    
    while ((j \ult (W64.of_int 80))) {
      leakages <- LeakAddr([(W64.to_uint (plain + j))]) :: leakages;
      aux_2 <- (loadW8 Glob.mem (W64.to_uint (plain + j)));
      pi <- aux_2;
      leakages <- LeakAddr([(W64.to_uint j)]) :: leakages;
      aux_2 <- (pi `^` (get8 (WArray80.init64 (fun i_0 => (s_k).[i_0])) (W64.to_uint j)));
      pi <- aux_2;
      leakages <- LeakAddr([0]) :: leakages;
      aux_2 <- (pi `^` (get8 (WArray16.init128 (fun i_0 => (s_0).[i_0])) 0));
      pi <- aux_2;
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <- pi;
      leakages <- LeakAddr([(W64.to_uint (output + j))]) :: leakages;
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (output + j)) (aux_2);
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (j + (W64.of_int 1));
      j <- aux_0;
    leakages <- LeakCond((j \ult (W64.of_int 80))) :: LeakAddr([]) :: leakages;
    
    }
    return ();
  }
}.

