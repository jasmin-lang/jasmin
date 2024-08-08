require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (a:W64.t, b:W64.t) : W64.t = {
    
    var r:W64.t;
    var c:bool;
    var x:W64.t;
    
    (c, x) <- adc_64 a b false;
    r <- x;
    return (r);
  }
  
  proc g (x:W64.t, y:W64.t) : W64.t = {
    
    var r:W64.t;
    var b:bool;
    var c:bool;
    
    r <- (W64.of_int 42);
    (b, r) <- adc_64 r x false;
    (c, r) <- adc_64 r y b;
    return (r);
  }
  
  proc h (x:W64.t) : W64.t = {
    
    var r:W64.t;
    
    r <- x;
    r <- (r + (W64.of_int 1));
    r <- (r + x);
    return (r);
  }
  
  proc i (x:W64.t) : W64.t = {
    
    var r:W64.t;
    var c:bool;
    var z:W64.t;
    var  _0:bool;
    var  _1:W64.t;
    var  _2:bool;
    
    r <- x;
    ( _0, x) <- adc_64 x x false;
    (c,  _1) <- adc_64 x x false;
    z <- (W64.of_int 0);
    ( _2, r) <- adc_64 r z c;
    return (r);
  }
  
  proc j (x:W64.t) : W64.t = {
    
    var r:W64.t;
    var y:W64.t;
    var b:bool;
    
    y <- (x `<<` (W8.of_int 2));
    x <- (y `>>` (W8.of_int 1));
    y <- (x `|>>` (W8.of_int 1));
    (b, y) <- adc_64 y (W64.of_int 1) false;
    r <- y;
    return (r);
  }
  
  proc k (x:W64.t) : W64.t = {
    
    var e:W64.t;
    var a:W64.t;
    var b:W64.t;
    var c:W64.t;
    var d:W64.t;
    
    a <- (W64.of_int 0);
    b <- (W64.of_int 1);
    c <- (W64.of_int 2);
    d <- (W64.of_int 3);
    e <- a;
    e <- (e + b);
    e <- (e + c);
    e <- (e + d);
    return (e);
  }
}.

