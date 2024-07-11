require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array5.
require import WArray20.



module M = {
  proc array_init () : W32.t Array5.t = {
    var aux: int;
    
    var a:W32.t Array5.t;
    var i:int;
    var t:W32.t;
    a <- witness;
    i <- 0;
    while (i < 5) {
      t <- (W32.of_int i);
      a.[i] <- t;
      i <- i + 1;
    }
    return (a);
  }
  
  proc test_u16 () : W32.t = {
    
    var r:W32.t;
    var a:W32.t Array5.t;
    var pa:W32.t Array5.t;
    var i:W32.t;
    var t:W32.t;
    a <- witness;
    pa <- witness;
    a <@ array_init ();
    pa <- a;
    i <- (W32.of_int 0);
    t <- (W32.of_int 3);
    pa.[(W32.to_uint i)] <- t;
    r <- (zeroextu32 (get16 (WArray20.init32 (fun i_0 => (pa).[i_0])) (W32.to_uint i)));
    return (r);
  }
  
  proc test_u32 () : W32.t = {
    
    var r:W32.t;
    var a:W32.t Array5.t;
    var pa:W32.t Array5.t;
    var i:W32.t;
    var t:W32.t;
    a <- witness;
    pa <- witness;
    a <@ array_init ();
    pa <- a;
    r <- (W32.of_int 0);
    i <- (W32.of_int 0);
    
    while ((i \ult (W32.of_int 5))) {
      t <- pa.[(W32.to_uint i)];
      r <- (r + t);
      i <- (i + (W32.of_int 1));
    }
    return (r);
  }
}.

