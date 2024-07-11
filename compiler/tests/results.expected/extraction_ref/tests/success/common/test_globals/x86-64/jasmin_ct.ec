require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray8.

abbrev g = W32.of_int 3.


abbrev f_0 = W32.of_int 10.


abbrev t = Array2.of_list witness [W32.of_int 10; W32.of_int 3].


abbrev e = W32.of_int 5.


abbrev d = W32.of_int 30.


abbrev c = W32.of_int 30.


abbrev b = W32.of_int 3.


abbrev a = W32.of_int 10.


module M = {
  var leakages : leakages_t
  
  proc f (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    var r:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + (W32.of_int 10));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + (W32.of_int (10 %/ 3)));
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + x);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + x);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- c;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + x);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- d;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + x);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- e;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + x);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- f_0;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + x);
    r <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- g;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (r + x);
    r <- aux;
    return (r);
  }
}.

