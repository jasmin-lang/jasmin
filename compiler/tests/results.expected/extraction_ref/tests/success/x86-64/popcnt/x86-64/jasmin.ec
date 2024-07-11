require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_popcnt16 (rp:W64.t) : unit = {
    
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
    
    ( _0,  _1,  _2,  _3, zf, t) <- POPCNT_16 (loadW16 Glob.mem (W64.to_uint (rp + (W64.of_int 0))));
    ( _4,  _5,  _6,  _7, zf, t) <- POPCNT_16 t;
    Glob.mem <- storeW16 Glob.mem (W64.to_uint (rp + (W64.of_int 0))) (t);
    return ();
  }
  
  proc test_popcnt32 (rp:W64.t) : unit = {
    
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
    
    ( _0,  _1,  _2,  _3, zf, t) <- POPCNT_32 (loadW32 Glob.mem (W64.to_uint (rp + (W64.of_int 0))));
    ( _4,  _5,  _6,  _7, zf, t) <- POPCNT_32 t;
    Glob.mem <- storeW32 Glob.mem (W64.to_uint (rp + (W64.of_int 0))) (t);
    return ();
  }
  
  proc test_popcnt64 (rp:W64.t) : unit = {
    
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
    
    ( _0,  _1,  _2,  _3, zf, t) <- POPCNT_64 (loadW64 Glob.mem (W64.to_uint (rp + (W64.of_int 0))));
    ( _4,  _5,  _6,  _7, zf, t) <- POPCNT_64 t;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (rp + (W64.of_int 0))) (t);
    return ();
  }
}.

