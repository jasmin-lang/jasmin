require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc main () : unit = {
    
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
    
    ( _0,  _1,  _2,  _3,  _4, p8) <- set0_8 ;
    ( _5,  _6,  _7,  _8,  _9, p16) <- set0_16 ;
    ( _10,  _11,  _12,  _13,  _14, p32) <- set0_32 ;
    ( _15,  _16,  _17,  _18,  _19, p64) <- set0_64 ;
    p128 <- set0_128 ;
    p256 <- set0_256 ;
    msf0 <- init_msf ;
    (f,  _20,  _21,  _22,  _23) <- CMP_64 p64 p64;
    if (f) {
      msf0 <- update_msf f msf0;
    } else {
      
    }
    msf1 <- mov_msf msf0;
    p8 <- protect_8 p8 msf1;
    p16 <- protect_16 p16 msf1;
    p32 <- protect_32 p32 msf1;
    p64 <- protect_64 p64 msf1;
    p128 <- protect_128 p128 msf1;
    p256 <- protect_256 p256 msf1;
    return ();
  }
}.

