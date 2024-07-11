require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc rev (x:W32.t) : W32.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: W32.t;
    
    var y:W32.t;
    var nf:bool;
    var zf:bool;
    var vf:bool;
    var cf:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- REV x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- REV16 y;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- REVSH x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0) <- CMP x y;
    nf <- aux_3;
    zf <- aux_2;
    vf <- aux_1;
    cf <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- REVcc x cf y;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- REV16cc y cf x;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- REVSHcc x cf y;
    y <- aux;
    return (y);
  }
}.

