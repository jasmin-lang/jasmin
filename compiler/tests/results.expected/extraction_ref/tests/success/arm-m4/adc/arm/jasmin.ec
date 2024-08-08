require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.





module M = {
  proc adc (arg0:W32.t, arg1:W32.t) : W32.t = {
    
    var res_0:W32.t;
    var x:W32.t;
    var c:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    
    x <- arg1;
    ( _0, x) <- adc_32 arg0 x false;
    (c, x) <- adc_32 arg0 x false;
    ( _1, x) <- adc_32 x (W32.of_int 12) false;
    (c, x) <- adc_32 x (W32.of_int 98) false;
    (c, x) <- adc_32 arg0 x c;
    ( _2, x) <- adc_32 arg0 x c;
    (c, x) <- adc_32 arg0 x false;
    ( _3, x) <- adc_32 arg0 x false;
    ( _4, x) <- adc_32 x arg0 false;
    (c, x) <- adc_32 x arg0 false;
    ( _5, x) <- adc_32 x (W32.of_int 12) false;
    (c, x) <- adc_32 x (W32.of_int 98) false;
    (c, x) <- adc_32 x arg0 c;
    ( _6, x) <- adc_32 x arg0 c;
    (c, x) <- adc_32 x arg0 false;
    ( _7, x) <- adc_32 x arg0 false;
    res_0 <- x;
    return (res_0);
  }
}.

