require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc foo (x:W64.t) : W64.t = {
    
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
    
    ( _0,  _1,  _2,  _3,  _4, x8) <- set0_8 ;
    r <- (sigextu64 x8);
    ( _5,  _6,  _7,  _8,  _9, x16) <- set0_16 ;
    tmp <- (sigextu64 x16);
    r <- (r + tmp);
    ( _10,  _11,  _12,  _13,  _14, x32) <- set0_32 ;
    tmp <- (sigextu64 x32);
    r <- (r + tmp);
    ( _15,  _16,  _17,  _18,  _19, x64) <- set0_64 ;
    tmp <- x64;
    r <- (r + tmp);
    x128 <- set0_128 ;
    tmp <- VPEXTR_64 x128 (W8.of_int 0);
    r <- (r + tmp);
    x256 <- set0_256 ;
    x128 <- VEXTRACTI128 x256 (W8.of_int 0);
    tmp <- VPEXTR_64 x128 (W8.of_int 0);
    r <- (r + tmp);
    return (r);
  }
}.

