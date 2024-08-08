require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.
require import Array2 Array3.
require import WArray3 WArray8.



module M = {
  var leakages : leakages_t
  
  proc main (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    var a:W32.t Array2.t;
    a <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([1]) :: leakages;
    a.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (get32_direct (WArray8.init32 (fun i => (a).[i])) 2);
    x <- aux;
    return (x);
  }
  
  proc instack (x:W32.t) : W32.t = {
    var aux_0: W8.t;
    var aux_1: W16.t;
    var aux: W32.t;
    
    var r:W32.t;
    var s:W8.t Array3.t;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    leakages <- LeakAddr([0]) :: leakages;
    s.[0] <- (truncateu8 aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([1]) :: leakages;
    s <- Array3.init (WArray3.get8 (WArray3.set16_direct (WArray3.init8 (fun i => (s).[i])) 1 ((truncateu16 aux))));
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (sigextu32 s.[1]);
    r <- aux;
    return (r);
  }
}.

