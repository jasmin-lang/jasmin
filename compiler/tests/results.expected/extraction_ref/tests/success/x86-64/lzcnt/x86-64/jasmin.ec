require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc lzcnt (x:W64.t) : W64.t = {
    
    var r:W64.t;
    var _of_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var _cf_:bool;
    var  _0:bool;
    var  _1:bool;
    
    r <- x;
    (_of_, _sf_,  _0, _zf_, r) <- DEC_64 r;
    (_of_, _cf_, _sf_,  _1, _zf_, r) <- LZCNT_64 x;
    return (r);
  }
  
  proc foo () : W64.t = {
    
    var r:W64.t;
    var a:W64.t;
    
    a <- (W64.of_int (1 `<<` 62));
    r <@ lzcnt (a);
    return (r);
  }
}.

