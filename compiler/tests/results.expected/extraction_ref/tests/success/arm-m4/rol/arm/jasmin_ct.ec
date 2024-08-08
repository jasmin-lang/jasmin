require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc rol (arg0:W32.t) : W32.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: W32.t;
    
    var res_0:W32.t;
    var x:W32.t;
    var nf:bool;
    var zf:bool;
    var cf:bool;
    var vf:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (arg0 `|<<|` (W8.of_int 0));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux <- (arg0 `|<<|` (W8.of_int 1));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `|<<|` (W8.of_int 1));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([(W32.to_uint (x + (W32.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W32.to_uint (x + (W32.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0) <- CMP x (W32.of_int 0);
    nf <- aux_3;
    zf <- aux_2;
    cf <- aux_1;
    vf <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (zf ? (x `|<<|` (W8.of_int 2)) : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((! (! zf)) ? (x `|<<|` (W8.of_int 2)) : x);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    res_0 <- aux;
    return (res_0);
  }
}.

