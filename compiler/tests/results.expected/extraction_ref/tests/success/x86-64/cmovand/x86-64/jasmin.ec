require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc condition2 (i:W64.t, n:W64.t) : bool = {
    
    var result:bool;
    var t:bool;
    var a:W8.t;
    var b:W8.t;
    var c:W8.t;
    
    t <- ((W64.of_int 0) \slt i);
    a <- SETcc t;
    t <- (i \slt n);
    b <- SETcc t;
    c <- (b `&` a);
    result <- (c = (W8.of_int 1));
    return (result);
  }
  
  proc move_0 (i:W64.t, n:W64.t, x:W64.t, y:W64.t) : W64.t = {
    
    var c:bool;
    
    c <@ condition2 (i, n);
    x <- (c ? y : x);
    return (x);
  }
  
  proc test (x:W64.t, y:W64.t) : W64.t = {
    
    var r:W64.t;
    var a:W64.t;
    var b:W64.t;
    
    a <- (W64.of_int 10);
    b <- (W64.of_int 20);
    r <- x;
    r <@ move_0 (a, b, r, y);
    return (r);
  }
}.

