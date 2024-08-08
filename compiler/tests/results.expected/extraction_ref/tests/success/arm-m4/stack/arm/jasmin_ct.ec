require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc leaf () : W32.t = {
    var aux_0: int;
    var aux: W32.t;
    
    var f:W32.t;
    var r:W32.t;
    var i:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    f <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- f;
    r <- aux;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- r;
      f <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (f + (W32.of_int i));
      f <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- f;
      r <- aux;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- r;
    f <- aux;
    return (f);
  }
  
  proc main (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    var s:W32.t;
    var k:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    s <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ leaf ();
    k <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- s;
    x <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + k);
    x <- aux;
    return (x);
  }
}.

