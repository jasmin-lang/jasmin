require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array5.
require import WArray20.



module M = {
  proc array_init () : W32.t Array5.t = {
    var aux: int;
    
    var a:W32.t Array5.t;
    var i:int;
    a <- witness;
    i <- 0;
    while (i < 5) {
      a.[i] <- (W32.of_int i);
      i <- i + 1;
    }
    return (a);
  }
  
  proc test_u16 () : W16.t = {
    
    var r:W16.t;
    var a:W32.t Array5.t;
    var i:W64.t;
    a <- witness;
    a <@ array_init ();
    i <- (W64.of_int 0);
    a.[(W64.to_uint i)] <- (W32.of_int 3);
    r <- (get16 (WArray20.init32 (fun i_0 => (a).[i_0])) (W64.to_uint i));
    return (r);
  }
  
  proc test_u32 () : W32.t = {
    
    var r:W32.t;
    var a:W32.t Array5.t;
    var i:W64.t;
    var t:W32.t;
    a <- witness;
    a <@ array_init ();
    r <- (W32.of_int 0);
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int 5))) {
      t <- a.[(W64.to_uint i)];
      r <- (r + t);
      i <- (i + (W64.of_int 1));
    }
    return (r);
  }
}.

