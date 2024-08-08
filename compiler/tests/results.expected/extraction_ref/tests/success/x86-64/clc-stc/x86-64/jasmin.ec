require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_stc () : W64.t = {
    
    var r:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var cf:bool;
    var  _0:bool;
    var  _1:bool;
    
    (_of_, _cf_, _sf_,  _0, _zf_, r) <- set0_64 ;
    cf <- STC ;
    ( _1, r) <- adc_64 r r cf;
    return (r);
  }
  
  proc test_clc () : W64.t = {
    
    var r:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var cf:bool;
    var  _0:bool;
    var  _1:bool;
    
    (_of_, _cf_, _sf_,  _0, _zf_, r) <- set0_64 ;
    cf <- CLC ;
    ( _1, r) <- adc_64 r r cf;
    return (r);
  }
}.

