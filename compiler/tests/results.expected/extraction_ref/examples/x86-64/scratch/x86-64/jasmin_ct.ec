require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (a:W64.t, b:W64.t) : W64.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var r:W64.t;
    var c:bool;
    var x:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <- adc_64 a b false;
    c <- aux;
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    r <- aux_0;
    return (r);
  }
  
  proc g (x:W64.t, y:W64.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var r:W64.t;
    var b:bool;
    var c:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 42);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_64 r x false;
    b <- aux_0;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_64 r y b;
    c <- aux_0;
    r <- aux;
    return (r);
  }
  
  proc h (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + (W64.of_int 1));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + x);
    r <- aux;
    return (r);
  }
  
  proc i (x:W64.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var r:W64.t;
    var c:bool;
    var z:W64.t;
    var  _0:bool;
    var  _1:W64.t;
    var  _2:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_64 x x false;
     _0 <- aux_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_64 x x false;
    c <- aux_0;
     _1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_64 r z c;
     _2 <- aux_0;
    r <- aux;
    return (r);
  }
  
  proc j (x:W64.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var r:W64.t;
    var y:W64.t;
    var b:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `<<` (W8.of_int 2));
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (y `>>` (W8.of_int 1));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `|>>` (W8.of_int 1));
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- adc_64 y (W64.of_int 1) false;
    b <- aux_0;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- y;
    r <- aux;
    return (r);
  }
  
  proc k (x:W64.t) : W64.t = {
    var aux: W64.t;
    
    var e:W64.t;
    var a:W64.t;
    var b:W64.t;
    var c:W64.t;
    var d:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 2);
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 3);
    d <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    e <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (e + b);
    e <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (e + c);
    e <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (e + d);
    e <- aux;
    return (e);
  }
}.

