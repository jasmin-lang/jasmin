require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc test_div (x:W64.t) : W8.t = {
    
    var s:W8.t;
    var r:W8.t;
    var a:W64.t;
    var b:W64.t;
    var c:W64.t;
    var d:W64.t;
    var e:W32.t;
    var f:W32.t;
    var g:W16.t;
    var h:W16.t;
    
    r <- (W8.of_int 0);
    a <- (W64.of_int 1);
    x <- ((x \ule (W64.of_int 0)) ? a : x);
    x <- (((W64.of_int 32768) \ule x) ? a : x);
    a <- x;
    b <- x;
    c <- (a \udiv b);
    d <- (c \sdiv b);
    r <- (r + (truncateu8 d));
    e <- ((truncateu32 d) \udiv (truncateu32 b));
    f <- (e \sdiv (truncateu32 b));
    r <- (r + (truncateu8 f));
    g <- ((truncateu16 f) \udiv (truncateu16 b));
    h <- (g \sdiv (truncateu16 b));
    r <- (r + (truncateu8 h));
    s <- r;
    return (s);
  }
  
  proc test_mod (x:W64.t) : W8.t = {
    
    var s:W8.t;
    var r:W8.t;
    var a:W64.t;
    var b:W64.t;
    var c:W64.t;
    var d:W32.t;
    var e:W16.t;
    
    r <- (W8.of_int 0);
    a <- (W64.of_int 1);
    x <- ((x \ule (W64.of_int 0)) ? a : x);
    x <- (((W64.of_int 32768) \ule x) ? a : x);
    a <- x;
    b <- x;
    c <- (a \umod b);
    r <- (r + (truncateu8 c));
    a <- x;
    b <- x;
    c <- (a \smod b);
    r <- (r + (truncateu8 c));
    a <- x;
    b <- x;
    d <- ((truncateu32 a) \umod (truncateu32 b));
    r <- (r + (truncateu8 d));
    a <- x;
    b <- x;
    d <- ((truncateu32 a) \smod (truncateu32 b));
    r <- (r + (truncateu8 d));
    a <- x;
    b <- x;
    e <- ((truncateu16 a) \umod (truncateu16 b));
    r <- (r + (truncateu8 e));
    a <- x;
    b <- x;
    e <- ((truncateu16 a) \smod (truncateu16 b));
    r <- (r + (truncateu8 e));
    s <- r;
    return (s);
  }
  
  proc test_compound (x:W64.t, y:W64.t) : W64.t = {
    
    var c:W64.t;
    var a:W64.t;
    var b:W64.t;
    
    a <- (W64.of_int 1);
    y <- ((y \ule (W64.of_int 0)) ? a : y);
    a <- x;
    b <- y;
    a <- (a \udiv b);
    a <- (a \umod b);
    c <- a;
    return (c);
  }
}.

