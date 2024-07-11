require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (a:W32.t, b:W32.t, c:W32.t) : W32.t = {
    var aux: bool;
    var aux_0: W32.t;
    
    var d:W32.t;
    var cond:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (a = (W32.of_int 0));
    cond <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- ((a * b) + c);
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (d + (b * c));
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (cond ? ((b * c) + d) : a);
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (cond ? (a + (b * c)) : a);
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- MLA c d a;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- MLAcc d a b cond c;
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (c - (d * a));
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (b - (c * d));
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (cond ? (d - (a * b)) : c);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (cond ? (c - (a * b)) : c);
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- MLS a b c;
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- MLScc d a b cond c;
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- c;
    d <- aux_0;
    return (d);
  }
}.

