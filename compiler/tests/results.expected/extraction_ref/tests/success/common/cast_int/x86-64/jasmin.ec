require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test () : int = {
    
    var j:int;
    var i:int;
    
    i <- 0;
    j <- (1 `<<` i);
    return (j);
  }
  
  proc main () : W32.t = {
    
    var n:W32.t;
    var k:int;
    
    k <@ test ();
    n <- (W32.of_int k);
    return (n);
  }
}.

