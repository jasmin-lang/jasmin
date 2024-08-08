require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test1 () : int = {
    var aux: int;
    
    var j:int;
    var i:int;
    
    j <- 0;
    i <- 0;
    while (i < 4) {
      j <- (j + i);
      i <- i + 1;
    }
    return (j);
  }
  
  proc test2 () : W64.t = {
    var aux: int;
    
    var j:W64.t;
    var i:int;
    
    j <- (W64.of_int 0);
    i <- 0;
    while (i < 4) {
      j <- (j + (W64.of_int i));
      i <- i + 1;
    }
    return (j);
  }
  
  proc test3 () : W64.t = {
    
    var j:W64.t;
    var tmp:int;
    var i:W64.t;
    
    tmp <@ test1 ();
    j <- (W64.of_int tmp);
    i <@ test2 ();
    
    while ((j \ule (W64.of_int 12))) {
      j <- (j + i);
    }
    return (j);
  }
}.

