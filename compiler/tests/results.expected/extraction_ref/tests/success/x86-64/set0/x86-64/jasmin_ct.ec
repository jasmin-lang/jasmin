require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc foo (x:W64.t) : W64.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_4: W8.t;
    var aux_6: W16.t;
    var aux_7: W32.t;
    var aux_5: W64.t;
    var aux_8: W128.t;
    var aux_9: W256.t;
    
    var r:W64.t;
    var x8:W8.t;
    var x16:W16.t;
    var tmp:W64.t;
    var x32:W32.t;
    var x64:W64.t;
    var x128:W128.t;
    var x256:W256.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    var  _12:bool;
    var  _13:bool;
    var  _14:bool;
    var  _15:bool;
    var  _16:bool;
    var  _17:bool;
    var  _18:bool;
    var  _19:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- set0_8 ;
     _0 <- aux_3;
     _1 <- aux_2;
     _2 <- aux_1;
     _3 <- aux_0;
     _4 <- aux;
    x8 <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (sigextu64 x8);
    r <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_6) <- set0_16 ;
     _5 <- aux_3;
     _6 <- aux_2;
     _7 <- aux_1;
     _8 <- aux_0;
     _9 <- aux;
    x16 <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (sigextu64 x16);
    tmp <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (r + tmp);
    r <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_7) <- set0_32 ;
     _10 <- aux_3;
     _11 <- aux_2;
     _12 <- aux_1;
     _13 <- aux_0;
     _14 <- aux;
    x32 <- aux_7;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (sigextu64 x32);
    tmp <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (r + tmp);
    r <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_5) <- set0_64 ;
     _15 <- aux_3;
     _16 <- aux_2;
     _17 <- aux_1;
     _18 <- aux_0;
     _19 <- aux;
    x64 <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- x64;
    tmp <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (r + tmp);
    r <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_8 <- set0_128 ;
    x128 <- aux_8;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- VPEXTR_64 x128 (W8.of_int 0);
    tmp <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (r + tmp);
    r <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_9 <- set0_256 ;
    x256 <- aux_9;
    leakages <- LeakAddr([]) :: leakages;
    aux_8 <- VEXTRACTI128 x256 (W8.of_int 0);
    x128 <- aux_8;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- VPEXTR_64 x128 (W8.of_int 0);
    tmp <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (r + tmp);
    r <- aux_5;
    return (r);
  }
}.

