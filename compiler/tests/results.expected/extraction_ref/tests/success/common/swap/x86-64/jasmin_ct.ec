require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2 Array8.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc main (x:W32.t, y:W32.t) : W32.t = {
    var aux_5: W32.t;
    var aux_4: W32.t;
    var aux_2: W8.t Array8.t;
    var aux_1: W8.t Array8.t;
    var aux_3: W32.t Array2.t;
    var aux_0: W32.t Array2.t;
    
    var t1:W32.t Array2.t;
    var pt1:W32.t Array2.t;
    var t2:W32.t Array2.t;
    var pt2:W32.t Array2.t;
    var aux:W32.t;
    pt1 <- witness;
    pt2 <- witness;
    t1 <- witness;
    t2 <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- t1;
    pt1 <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- t2;
    pt2 <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_0) <- swap_ pt1 pt2;
    pt1 <- aux_3;
    pt2 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (W32.of_int 0);
    aux <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    pt1.[0] <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (W32.of_int 1);
    aux <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    pt1.[1] <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (W32.of_int 0);
    aux <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    pt2.[0] <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (W32.of_int 1);
    aux <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    pt2.[1] <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_0) <- swap_ pt1 pt2;
    pt1 <- aux_3;
    pt2 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_4) <- swap_ x y;
    x <- aux_5;
    y <- aux_4;
    leakages <- LeakAddr([0]) :: leakages;
    aux_5 <- pt1.[0];
    aux <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (x + aux);
    x <- aux_5;
    leakages <- LeakAddr([1]) :: leakages;
    aux_5 <- pt1.[1];
    aux <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (x + aux);
    x <- aux_5;
    leakages <- LeakAddr([0]) :: leakages;
    aux_5 <- pt2.[0];
    aux <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (x + aux);
    x <- aux_5;
    leakages <- LeakAddr([1]) :: leakages;
    aux_5 <- pt2.[1];
    aux <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (x + aux);
    x <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- pt1;
    t1 <- aux_3;
    leakages <- LeakAddr([]) :: leakages;
    aux_3 <- pt2;
    t2 <- aux_3;
    leakages <- LeakAddr([0]) :: leakages;
    aux_5 <- t1.[0];
    aux <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (x + aux);
    x <- aux_5;
    leakages <- LeakAddr([1]) :: leakages;
    aux_5 <- t1.[1];
    aux <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (x + aux);
    x <- aux_5;
    leakages <- LeakAddr([0]) :: leakages;
    aux_5 <- t2.[0];
    aux <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (x + aux);
    x <- aux_5;
    leakages <- LeakAddr([1]) :: leakages;
    aux_5 <- t2.[1];
    aux <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- (x + aux);
    x <- aux_5;
    leakages <- LeakAddr([]) :: leakages;
    aux_5 <- x;
    x <- aux_5;
    return (x);
  }
}.

