require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc f (x:W64.t) : W64.t = {
    
    var c:W64.t;
    var a:W64.t;
    var d:W8.t;
    var of_0:bool;
    var cf:bool;
    var b:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    
    a <- x;
    d <- (W8.of_int 4);
    a <- (a `|<<|` (d `&` (W8.of_int 63)));
    a <- (a `|<<|` (W8.of_int 2));
    ( _0,  _1, a) <- ROL_64 a d;
    (of_0, cf, b) <- ROL_64 a (W8.of_int 2);
    (cf, b) <- adc_64 b x cf;
    c <- (b `|>>|` (d `&` (W8.of_int 63)));
    c <- (b `|>>|` (W8.of_int 3));
    ( _2,  _3, c) <- ROR_64 b d;
    ( _4,  _5, c) <- ROR_64 c (W8.of_int 3);
    return (c);
  }
}.

