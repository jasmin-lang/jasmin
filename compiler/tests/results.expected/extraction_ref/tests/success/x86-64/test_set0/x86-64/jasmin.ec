require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (x:W64.t) : unit = {
    
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
    
    ( _0,  _1,  _2,  _3,  _4, x) <- set0_64 ;
    ( _5,  _6,  _7,  _8,  _9, x) <- set0_64 ;
    ( _10,  _11,  _12,  _13,  _14, x) <- set0_64 ;
    ( _15,  _16,  _17,  _18,  _19, x) <- set0_64 ;
    ( _20, x) <- adc_64 x x false;
    return ();
  }
  
  proc g8 () : W8.t = {
    
    var r:W8.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    
    (_of_, _cf_, _sf_,  _0, _zf_, r) <- set0_8 ;
    return (r);
  }
  
  proc g16 () : W16.t = {
    
    var r:W16.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    
    (_of_, _cf_, _sf_,  _0, _zf_, r) <- set0_16 ;
    return (r);
  }
  
  proc g32 () : W32.t = {
    
    var r:W32.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    
    (_of_, _cf_, _sf_,  _0, _zf_, r) <- set0_32 ;
    return (r);
  }
  
  proc g64 () : W64.t = {
    
    var r:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    
    (_of_, _cf_, _sf_,  _0, _zf_, r) <- set0_64 ;
    return (r);
  }
}.

