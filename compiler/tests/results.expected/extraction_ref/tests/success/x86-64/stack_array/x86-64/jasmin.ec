require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array10.
require import WArray80.



module M = {
  proc fill (in_0:W64.t, out:W64.t, len:W64.t) : W64.t = {
    
    var i:W64.t;
    var max:W64.t;
    var aux:W64.t;
    var t:W64.t Array10.t;
    t <- witness;
    max <- (W64.of_int 10);
    max <- ((len \ult max) ? len : max);
    i <- (W64.of_int 0);
    
    while ((i \ult max)) {
      aux <- (loadW64 Glob.mem (W64.to_uint (in_0 + ((W64.of_int 8) * i))));
      t.[(W64.to_uint i)] <- aux;
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int 0);
    
    while ((i \ult max)) {
      aux <- t.[(W64.to_uint i)];
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (in_0 + ((W64.of_int 8) * i))) (aux);
      i <- (i + (W64.of_int 1));
    }
    return (i);
  }
}.

