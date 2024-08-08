require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array1 Array4 Array5 Array13.
require import WArray4 WArray16 WArray20 WArray52.



module M = {
  proc onregister0 (x:W32.t) : W32.t = {
    var aux: int;
    
    var result:W32.t;
    var t:W32.t;
    var i:int;
    var tab:W32.t Array1.t;
    tab <- witness;
    t <- x;
    i <- 0;
    while (i < 1) {
      tab.[i] <- x;
      i <- i + 1;
    }
    result <- t;
    i <- 0;
    while (i < 1) {
      result <- (result + tab.[i]);
      i <- i + 1;
    }
    return (result);
  }
  
  proc onregister1 (x:W32.t) : W32.t = {
    var aux: int;
    
    var result:W32.t;
    var t:W32.t;
    var i:int;
    var tab:W32.t Array4.t;
    tab <- witness;
    t <- x;
    aux <- (((14 - 8) - 1) - 1);
    i <- 0;
    while (i < aux) {
      tab.[i] <- x;
      i <- i + 1;
    }
    result <- t;
    aux <- (((14 - 8) - 1) - 1);
    i <- 0;
    while (i < aux) {
      result <- (result + tab.[i]);
      i <- i + 1;
    }
    return (result);
  }
  
  proc onstack0 (x:W32.t) : W32.t = {
    var aux: int;
    
    var result:W32.t;
    var t:W32.t;
    var i:int;
    var tab:W32.t Array5.t;
    tab <- witness;
    t <- x;
    aux <- ((14 - 8) - 1);
    i <- 0;
    while (i < aux) {
      tab.[i] <- x;
      i <- i + 1;
    }
    result <- t;
    aux <- ((14 - 8) - 1);
    i <- 0;
    while (i < aux) {
      result <- (result + tab.[i]);
      i <- i + 1;
    }
    return (result);
  }
  
  proc onstack1 (x:W32.t) : W32.t = {
    var aux: int;
    
    var result:W32.t;
    var t:W32.t;
    var i:int;
    var tab:W32.t Array13.t;
    tab <- witness;
    t <- x;
    aux <- (14 - 1);
    i <- 0;
    while (i < aux) {
      tab.[i] <- x;
      i <- i + 1;
    }
    result <- t;
    aux <- (14 - 1);
    i <- 0;
    while (i < aux) {
      result <- (result + tab.[i]);
      i <- i + 1;
    }
    return (result);
  }
}.

