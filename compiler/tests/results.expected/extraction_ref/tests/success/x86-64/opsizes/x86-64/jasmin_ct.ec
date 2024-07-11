require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc parsing_test (s:W64.t, v:W64.t) : W64.t = {
    var aux: W64.t;
    
    var x:W64.t;
    var u:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- s;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- v;
    u <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + s);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + (W64.of_int 64));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + s);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `>>` (truncateu8 (u `&` (W64.of_int 63))));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `|>>` (W8.of_int 24));
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `|>>` (truncateu8 (u `&` (W64.of_int 63))));
    x <- aux;
    return (x);
  }
  
  proc reg32_test (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    var y:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (y + x);
    y <- aux;
    return (y);
  }
  
  proc dead_code (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    var z:W32.t;
    var y:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- y;
    z <- aux;
    return (z);
  }
  
  proc move_0 (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    var y:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    y <- aux;
    return (y);
  }
  
  proc test_inline (a:W32.t) : W32.t = {
    var aux: W32.t;
    
    var b:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ move_0 (a);
    b <- aux;
    return (b);
  }
  
  proc primop_test (x:W64.t) : W8.t = {
    var aux_6: bool;
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_7: W8.t;
    var aux_1: W16.t;
    var aux_0: W32.t;
    var aux: W64.t;
    
    var a:W8.t;
    var d:W64.t;
    var c:W32.t;
    var b:W16.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    d <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- MOV_32 (truncateu32 d);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- MOV_16 (truncateu16 c);
    b <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    (aux_6, aux_5, aux_4, aux_3, aux_2, aux_7) <- ADD_8 (truncateu8 b) (truncateu8 b);
     _0 <- aux_6;
     _1 <- aux_5;
     _2 <- aux_4;
     _3 <- aux_3;
     _4 <- aux_2;
    a <- aux_7;
    return (a);
  }
  
  proc pluseq (x:W64.t) : W8.t = {
    var aux_1: W8.t;
    var aux_0: W16.t;
    var aux: W32.t;
    
    var a:W8.t;
    var c:W32.t;
    var b:W16.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (c * (truncateu32 x));
    c <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W16.of_int 0);
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (W8.of_int 0);
    a <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (b - (truncateu16 c));
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (a + (truncateu8 b));
    a <- aux_1;
    return (a);
  }
  
  proc test_shift (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    var y:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (y `<<` (W8.of_int 1));
    y <- aux;
    return (y);
  }
  
  proc test_immediate () : W32.t = {
    var aux: W32.t;
    var aux_0: W256.t;
    
    var r:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- ((W256.of_int 42) `&` (W256.of_int 10));
    r <- (truncateu32 aux_0);
    return (r);
  }
}.

