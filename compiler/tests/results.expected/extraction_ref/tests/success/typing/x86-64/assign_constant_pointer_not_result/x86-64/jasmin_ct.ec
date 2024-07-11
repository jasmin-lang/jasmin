require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array3.
require import WArray24.



module M = {
  var leakages : leakages_t
  
  proc foo (px:W64.t Array3.t) : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t Array3.t;
    
    var res_x:W64.t;
    var y:W64.t Array3.t;
    y <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- y;
    px <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 666);
    leakages <- LeakAddr([0]) :: leakages;
    y.[0] <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- px.[0];
    res_x <- aux_0;
    return (res_x);
  }
  
  proc main () : W64.t = {
    var aux: W64.t;
    
    var res_0:W64.t;
    var x:W64.t Array3.t;
    var  _0:W64.t;
    x <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 41);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ foo (x);
     _0 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- x.[0];
    res_0 <- aux;
    return (res_0);
  }
}.

