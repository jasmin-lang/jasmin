require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2 Array4.
require import WArray16 WArray32.



module M = {
  proc create () : W64.t Array2.t = {
    
    var tab:W64.t Array2.t;
    tab <- witness;
    tab.[0] <- (W64.of_int 0);
    tab.[1] <- (W64.of_int 1);
    return (tab);
  }
  
  proc sum (x:W64.t, v:W64.t Array4.t) : W64.t = {
    var aux: int;
    
    var result:W64.t;
    var i:int;
    
    result <- x;
    i <- 0;
    while (i < 4) {
      result <- (result + v.[i]);
      i <- i + 1;
    }
    return (result);
  }
  
  proc test (x:W64.t) : W64.t = {
    var aux: W64.t Array2.t;
    
    var result:W64.t;
    var big:W64.t Array4.t;
    big <- witness;
    aux <@ create ();
    big <- Array4.init (fun i => if 0 <= i < 0 + 2 then aux.[i-0] else big.[i]);
    aux <@ create ();
    big <- Array4.init (fun i => if 2 <= i < 2 + 2 then aux.[i-2] else big.[i]);
    result <@ sum (x, big);
    return (result);
  }
}.

