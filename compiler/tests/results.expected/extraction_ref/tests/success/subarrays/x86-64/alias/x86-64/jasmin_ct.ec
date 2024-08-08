require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2 Array4.
require import WArray16 WArray32.



module M = {
  var leakages : leakages_t
  
  proc create () : W64.t Array2.t = {
    var aux: W64.t;
    
    var tab:W64.t Array2.t;
    tab <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    tab.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    leakages <- LeakAddr([1]) :: leakages;
    tab.[1] <- aux;
    return (tab);
  }
  
  proc sum (x:W64.t, v:W64.t Array4.t) : W64.t = {
    var aux_0: int;
    var aux: W64.t;
    
    var result:W64.t;
    var i:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    result <- aux;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (result + v.[i]);
      result <- aux;
      i <- i + 1;
    }
    return (result);
  }
  
  proc test (x:W64.t) : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t Array2.t;
    
    var result:W64.t;
    var big:W64.t Array4.t;
    big <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ create ();
    leakages <- LeakAddr([0]) :: leakages;
    big <- Array4.init (fun i => if 0 <= i < 0 + 2 then aux.[i-0] else big.[i]);
    leakages <- LeakAddr([]) :: leakages;
    aux <@ create ();
    leakages <- LeakAddr([2]) :: leakages;
    big <- Array4.init (fun i => if 2 <= i < 2 + 2 then aux.[i-2] else big.[i]);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ sum (x, big);
    result <- aux_0;
    return (result);
  }
}.

