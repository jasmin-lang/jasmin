require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc condition2 (i:W64.t, n:W64.t) : bool = {
    var aux: bool;
    var aux_0: W8.t;
    
    var result:bool;
    var t:bool;
    var a:W8.t;
    var b:W8.t;
    var c:W8.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((W64.of_int 0) \slt i);
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- SETcc t;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (i \slt n);
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- SETcc t;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (b `&` a);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c = (W8.of_int 1));
    result <- aux;
    return (result);
  }
  
  proc move_0 (i:W64.t, n:W64.t, x:W64.t, y:W64.t) : W64.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var c:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ condition2 (i, n);
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (c ? y : x);
    x <- aux_0;
    return (x);
  }
  
  proc test (x:W64.t, y:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    var a:W64.t;
    var b:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 10);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 20);
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ move_0 (a, b, r, y);
    r <- aux;
    return (r);
  }
}.

