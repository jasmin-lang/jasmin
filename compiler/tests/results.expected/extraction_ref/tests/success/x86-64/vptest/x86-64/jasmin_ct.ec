require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_ptest (rp:W64.t) : unit = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux: W64.t;
    var aux_6: W128.t;
    var aux_0: W256.t;
    
    var r:W64.t;
    var f:W64.t;
    var g:W256.t;
    var zf:bool;
    var h:W128.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    f <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- set0_256 ;
    g <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1) <- VPTEST_256 g g;
     _0 <- aux_5;
     _1 <- aux_4;
     _2 <- aux_3;
     _3 <- aux_2;
    zf <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((! zf) ? f : r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    leakages <- LeakAddr([(W64.to_uint (rp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (rp + (W64.of_int 0))) (aux);
    leakages <- LeakAddr([]) :: leakages;
    aux_6 <- set0_128 ;
    h <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1) <- VPTEST_128 h h;
     _4 <- aux_5;
     _5 <- aux_4;
     _6 <- aux_3;
     _7 <- aux_2;
    zf <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((! zf) ? f : r);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    leakages <- LeakAddr([(W64.to_uint (rp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (rp + (W64.of_int 0))) (aux);
    return ();
  }
}.

