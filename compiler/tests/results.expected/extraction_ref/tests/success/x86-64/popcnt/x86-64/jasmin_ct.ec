require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_popcnt16 (rp:W64.t) : unit = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_4: W16.t;
    
    var zf:bool;
    var t:W16.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    
    leakages <- LeakAddr([(W64.to_uint (rp + (W64.of_int 0)))]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- POPCNT_16 (loadW16 Glob.mem (W64.to_uint (rp + (W64.of_int 0))));
     _0 <- aux_3;
     _1 <- aux_2;
     _2 <- aux_1;
     _3 <- aux_0;
    zf <- aux;
    t <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- POPCNT_16 t;
     _4 <- aux_3;
     _5 <- aux_2;
     _6 <- aux_1;
     _7 <- aux_0;
    zf <- aux;
    t <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- t;
    leakages <- LeakAddr([(W64.to_uint (rp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW16 Glob.mem (W64.to_uint (rp + (W64.of_int 0))) (aux_4);
    return ();
  }
  
  proc test_popcnt32 (rp:W64.t) : unit = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_4: W32.t;
    
    var zf:bool;
    var t:W32.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    
    leakages <- LeakAddr([(W64.to_uint (rp + (W64.of_int 0)))]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- POPCNT_32 (loadW32 Glob.mem (W64.to_uint (rp + (W64.of_int 0))));
     _0 <- aux_3;
     _1 <- aux_2;
     _2 <- aux_1;
     _3 <- aux_0;
    zf <- aux;
    t <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- POPCNT_32 t;
     _4 <- aux_3;
     _5 <- aux_2;
     _6 <- aux_1;
     _7 <- aux_0;
    zf <- aux;
    t <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- t;
    leakages <- LeakAddr([(W64.to_uint (rp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (rp + (W64.of_int 0))) (aux_4);
    return ();
  }
  
  proc test_popcnt64 (rp:W64.t) : unit = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_4: W64.t;
    
    var zf:bool;
    var t:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    
    leakages <- LeakAddr([(W64.to_uint (rp + (W64.of_int 0)))]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- POPCNT_64 (loadW64 Glob.mem (W64.to_uint (rp + (W64.of_int 0))));
     _0 <- aux_3;
     _1 <- aux_2;
     _2 <- aux_1;
     _3 <- aux_0;
    zf <- aux;
    t <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- POPCNT_64 t;
     _4 <- aux_3;
     _5 <- aux_2;
     _6 <- aux_1;
     _7 <- aux_0;
    zf <- aux;
    t <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- t;
    leakages <- LeakAddr([(W64.to_uint (rp + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (rp + (W64.of_int 0))) (aux_4);
    return ();
  }
}.

