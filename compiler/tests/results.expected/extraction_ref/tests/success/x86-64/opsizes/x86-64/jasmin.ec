require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc parsing_test (s:W64.t, v:W64.t) : W64.t = {
    
    var x:W64.t;
    var u:W64.t;
    
    x <- s;
    u <- v;
    x <- (x + s);
    x <- (x + (W64.of_int 64));
    x <- (x + s);
    x <- (x `>>` (truncateu8 (u `&` (W64.of_int 63))));
    x <- (x `|>>` (W8.of_int 24));
    x <- (x `|>>` (truncateu8 (u `&` (W64.of_int 63))));
    return (x);
  }
  
  proc reg32_test (x:W32.t) : W32.t = {
    
    var y:W32.t;
    
    y <- x;
    y <- (y + x);
    return (y);
  }
  
  proc dead_code (x:W32.t) : W32.t = {
    
    var z:W32.t;
    var y:W32.t;
    
    y <- x;
    z <- y;
    return (z);
  }
  
  proc move_0 (x:W32.t) : W32.t = {
    
    var y:W32.t;
    
    y <- x;
    return (y);
  }
  
  proc test_inline (a:W32.t) : W32.t = {
    
    var b:W32.t;
    
    b <@ move_0 (a);
    return (b);
  }
  
  proc primop_test (x:W64.t) : W8.t = {
    
    var a:W8.t;
    var d:W64.t;
    var c:W32.t;
    var b:W16.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    
    d <- x;
    c <- MOV_32 (truncateu32 d);
    b <- MOV_16 (truncateu16 c);
    ( _0,  _1,  _2,  _3,  _4, a) <- ADD_8 (truncateu8 b) (truncateu8 b);
    return (a);
  }
  
  proc pluseq (x:W64.t) : W8.t = {
    
    var a:W8.t;
    var c:W32.t;
    var b:W16.t;
    
    c <- (W32.of_int 0);
    c <- (c * (truncateu32 x));
    b <- (W16.of_int 0);
    a <- (W8.of_int 0);
    b <- (b - (truncateu16 c));
    a <- (a + (truncateu8 b));
    return (a);
  }
  
  proc test_shift (x:W32.t) : W32.t = {
    
    var y:W32.t;
    
    y <- x;
    y <- (y `<<` (W8.of_int 1));
    return (y);
  }
  
  proc test_immediate () : W32.t = {
    
    var r:W32.t;
    
    r <- (truncateu32 ((W256.of_int 42) `&` (W256.of_int 10)));
    return (r);
  }
}.

