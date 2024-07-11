require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc main () : unit = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_4: W8.t;
    var aux_5: W16.t;
    var aux_6: W32.t;
    var aux_7: W64.t;
    var aux_8: W128.t;
    var aux_9: W256.t;
    
    var p8:W8.t;
    var p16:W16.t;
    var p32:W32.t;
    var p64:W64.t;
    var p128:W128.t;
    var p256:W256.t;
    var msf0:W64.t;
    var f:bool;
    var msf1:W64.t;
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
    var  _20:bool;
    var  _21:bool;
    var  _22:bool;
    var  _23:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- set0_8 ;
     _0 <- aux_3;
     _1 <- aux_2;
     _2 <- aux_1;
     _3 <- aux_0;
     _4 <- aux;
    p8 <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_5) <- set0_16 ;
     _5 <- aux_3;
     _6 <- aux_2;
     _7 <- aux_1;
     _8 <- aux_0;
     _9 <- aux;
    p16 <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_6) <- set0_32 ;
     _10 <- aux_3;
     _11 <- aux_2;
     _12 <- aux_1;
     _13 <- aux_0;
     _14 <- aux;
    p32 <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_7) <- set0_64 ;
     _15 <- aux_3;
     _16 <- aux_2;
     _17 <- aux_1;
     _18 <- aux_0;
     _19 <- aux;
    p64 <- aux_7;
    leakages <- LeakAddr([]) :: leakages;
    aux_8 <- set0_128 ;
    p128 <- aux_8;
    leakages <- LeakAddr([]) :: leakages;
    aux_9 <- set0_256 ;
    p256 <- aux_9;
    leakages <- LeakAddr([]) :: leakages;
    aux_7 <- init_msf ;
    msf0 <- aux_7;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux) <- CMP_64 p64 p64;
    f <- aux_3;
     _20 <- aux_2;
     _21 <- aux_1;
     _22 <- aux_0;
     _23 <- aux;
    leakages <- LeakCond(f) :: LeakAddr([]) :: leakages;
    if (f) {
      leakages <- LeakAddr([]) :: leakages;
      aux_7 <- update_msf f msf0;
      msf0 <- aux_7;
    } else {
      
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_7 <- mov_msf msf0;
    msf1 <- aux_7;
    leakages <- LeakAddr([]) :: leakages;
    aux_4 <- protect_8 p8 msf1;
    p8 <- aux_4;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- protect_16 p16 msf1;
    p16 <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_6 <- protect_32 p32 msf1;
    p32 <- aux_6;
    leakages <- LeakAddr([]) :: leakages;
    aux_7 <- protect_64 p64 msf1;
    p64 <- aux_7;
    leakages <- LeakAddr([]) :: leakages;
    aux_8 <- protect_128 p128 msf1;
    p128 <- aux_8;
    leakages <- LeakAddr([]) :: leakages;
    aux_9 <- protect_256 p256 msf1;
    p256 <- aux_9;
    return ();
  }
}.

