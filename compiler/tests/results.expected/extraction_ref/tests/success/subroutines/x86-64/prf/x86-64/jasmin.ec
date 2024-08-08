require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1 Array2.
require import WArray1 WArray2.



module M = {
  proc id (x:W8.t Array1.t) : W8.t Array1.t = {
    
    var v:W8.t;
    
    v <- x.[0];
    v <- (v + (W8.of_int 1));
    x.[0] <- v;
    return (x);
  }
  
  proc copy (y:W8.t Array2.t) : W8.t Array2.t = {
    var aux: W8.t Array1.t;
    
    
    
    aux <@ id ((Array1.init (fun i => y.[(0 * 1) + i])));
    y <- Array2.init (fun i => if (0 * 1) <= i < (0 * 1) + 1 then aux.[i-(0 * 1)] else y.[i]);
    aux <@ id ((Array1.init (fun i => y.[(1 * 1) + i])));
    y <- Array2.init (fun i => if (1 * 1) <= i < (1 * 1) + 1 then aux.[i-(1 * 1)] else y.[i]);
    return (y);
  }
  
  proc test (p:W64.t) : unit = {
    var aux: int;
    
    var z:W8.t;
    var i:int;
    var tab:W8.t Array2.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    tab <- witness;
    ( _0,  _1,  _2,  _3,  _4, z) <- set0_8 ;
    i <- 0;
    while (i < 2) {
      tab.[i] <- z;
      i <- i + 1;
    }
    tab <@ copy (tab);
    i <- 0;
    while (i < 2) {
      z <- tab.[0];
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (p + (W64.of_int i))) (z);
      i <- i + 1;
    }
    return ();
  }
}.

