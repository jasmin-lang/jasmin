require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc add1 (arg:W64.t) : W64.t = {
    
    var z:W64.t;
    var cf:bool;
    var _of_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var zf:bool;
    var cF:bool;
    var zF:bool;
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
    
    z <- arg;
    ( _0, z) <- adc_64 z z false;
    (cf, z) <- adc_64 z z false;
    ( _1, z) <- adc_64 z z cf;
    ( _2, z) <- adc_64 z z false;
    ( _3, z) <- adc_64 z z false;
    (cf, z) <- adc_64 z z false;
    (cf, z) <- adc_64 z z false;
    (cf, z) <- adc_64 z z cf;
    (cf, z) <- adc_64 z z false;
    ( _4, cf,  _5,  _6,  _7, z) <- ADC_64 z z cf;
    (_of_, cf, _sf_,  _8, _zf_, z) <- ADC_64 z z cf;
    (_of_, cf, _sf_,  _9, _zf_, z) <- ADC_64 z z cf;
    (_of_, cf, _sf_,  _10, zf, z) <- ADC_64 z z cf;
    (_of_, cF, _sf_,  _11, zF, z) <- ADC_64 z z cf;
    ( _12,  _13,  _14,  _15,  _16, z) <- ADC_64 z z cF;
    return (z);
  }
}.

