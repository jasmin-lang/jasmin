require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray32.

abbrev c7 = W128.of_int 7.


abbrev c3 = W128.of_int 3.


module M = {
  var leakages : leakages_t
  
  proc add (x:W128.t, z:W128.t) : W128.t = {
    var aux: W128.t;
    
    var y:W128.t;
    var t:W128.t Array2.t;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- z;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- y;
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (x `^` t.[0]);
    x <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (y `^` t.[1]);
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `^` y);
    x <- aux;
    return (x);
  }
  
  proc main () : W128.t = {
    var aux: W128.t;
    
    var x:W128.t;
    var y:W128.t;
    var z:W128.t;
    var s:W128.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- c3;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- c7;
    y <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- set0_128 ;
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- z;
    s <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ add (x, y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `^` s);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ add (x, y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `^` s);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ add (x, y);
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x `^` s);
    x <- aux;
    return (x);
  }
}.

