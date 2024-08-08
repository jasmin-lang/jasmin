require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1 Array8.
require import WArray8 WArray64.



module M = {
  proc test0 (x:W64.t) : W64.t = {
    var aux: int;
    
    var result:W64.t;
    var i:int;
    var tab:W64.t Array8.t;
    tab <- witness;
    i <- 0;
    while (i < 8) {
      tab.[i] <- x;
      i <- i + 1;
    }
    result <- (W64.of_int 0);
    i <- 0;
    while (i < 8) {
      result <- (result + tab.[i]);
      i <- i + 1;
    }
    return (result);
  }
  
  proc test1 (x:W64.t) : W64.t = {
    var aux: int;
    
    var result:W64.t;
    var t:W64.t;
    var i:int;
    var tab:W64.t Array8.t;
    tab <- witness;
    t <- x;
    i <- 0;
    while (i < 8) {
      tab.[i] <- x;
      i <- i + 1;
    }
    result <- t;
    i <- 0;
    while (i < 8) {
      result <- (result + tab.[i]);
      i <- i + 1;
    }
    return (result);
  }
  
  proc test2 (x:W64.t) : W64.t = {
    
    var result:W64.t;
    var t:W64.t Array1.t;
    t <- witness;
    t.[0] <- x;
    result <- t.[0];
    return (result);
  }
  
  proc copy (x:W64.t) : W64.t = {
    
    var t:W64.t Array1.t;
    t <- witness;
    t.[0] <- x;
    x <- t.[0];
    return (x);
  }
  
  proc test3 (x:W64.t) : W64.t = {
    
    var result:W64.t;
    
    result <@ copy (x);
    return (result);
  }
  
  proc test4 (x:W64.t) : W64.t = {
    
    var result:W64.t;
    
    result <@ copy (x);
    return (result);
  }
  
  proc test5 (x:W64.t) : W64.t = {
    
    var result:W64.t;
    
    result <@ copy (x);
    return (result);
  }
  
  proc test6 (x:W64.t) : W64.t = {
    
    var result:W64.t;
    
    result <@ copy (x);
    return (result);
  }
}.

