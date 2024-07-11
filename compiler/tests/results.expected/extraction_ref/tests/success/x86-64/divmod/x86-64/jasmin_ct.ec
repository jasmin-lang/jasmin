require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc test_div (x:W64.t) : W8.t = {
    var aux: W8.t;
    var aux_2: W16.t;
    var aux_1: W32.t;
    var aux_0: W64.t;
    
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
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W8.of_int 0);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 1);
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- ((x \ule (W64.of_int 0)) ? a : x);
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (((W64.of_int 32768) \ule x) ? a : x);
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (a \udiv b);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (c \sdiv b);
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + (truncateu8 d));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- ((truncateu32 d) \udiv (truncateu32 b));
    e <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (e \sdiv (truncateu32 b));
    f <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + (truncateu8 f));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- ((truncateu16 f) \udiv (truncateu16 b));
    g <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (g \sdiv (truncateu16 b));
    h <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + (truncateu8 h));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    s <- aux;
    return (s);
  }
  
  proc test_mod (x:W64.t) : W8.t = {
    var aux: W8.t;
    var aux_2: W16.t;
    var aux_1: W32.t;
    var aux_0: W64.t;
    
    var s:W8.t;
    var r:W8.t;
    var a:W64.t;
    var b:W64.t;
    var c:W64.t;
    var d:W32.t;
    var e:W16.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W8.of_int 0);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 1);
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- ((x \ule (W64.of_int 0)) ? a : x);
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (((W64.of_int 32768) \ule x) ? a : x);
    x <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (a \umod b);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + (truncateu8 c));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (a \smod b);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + (truncateu8 c));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- ((truncateu32 a) \umod (truncateu32 b));
    d <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + (truncateu8 d));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- ((truncateu32 a) \smod (truncateu32 b));
    d <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + (truncateu8 d));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- ((truncateu16 a) \umod (truncateu16 b));
    e <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + (truncateu8 e));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- x;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- ((truncateu16 a) \smod (truncateu16 b));
    e <- aux_2;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + (truncateu8 e));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    s <- aux;
    return (s);
  }
  
  proc test_compound (x:W64.t, y:W64.t) : W64.t = {
    var aux: W64.t;
    
    var c:W64.t;
    var a:W64.t;
    var b:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((y \ule (W64.of_int 0)) ? a : y);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- y;
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (a \udiv b);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (a \umod b);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    c <- aux;
    return (c);
  }
}.

