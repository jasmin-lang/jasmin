require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.
require import Array1 Array4.
require import WArray4.



module M = {
  var leakages : leakages_t
  
  proc snd (x:W32.t, y:W32.t) : W32.t = {
    var aux: W32.t;
    var aux_1: W8.t Array4.t;
    var aux_0: W8.t Array4.t;
    var aux_3: W32.t Array1.t;
    var aux_2: W32.t Array1.t;
    
    var a:W32.t Array1.t;
    var b:W32.t Array1.t;
    a <- witness;
    b <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- y;
    leakages <- LeakAddr([0]) :: leakages;
    b.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2) <- swap_ a b;
    a <- aux_3;
    b <- aux_2;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    x <- aux;
    return (x);
  }
}.

