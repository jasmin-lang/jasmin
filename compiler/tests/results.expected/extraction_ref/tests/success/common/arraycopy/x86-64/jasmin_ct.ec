require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array4 Array16.
require import WArray16.

abbrev g = Array4.of_list witness [W32.of_int 1; W32.of_int 2; W32.of_int 3; W32.of_int 4].


module M = {
  var leakages : leakages_t
  
  proc all_kinds () : W32.t = {
    var aux_2: int;
    var aux_1: W32.t;
    var aux: W8.t Array16.t;
    var aux_0: W32.t Array4.t;
    
    var x:W32.t;
    var a:W32.t Array4.t;
    var b:W32.t Array4.t;
    var c:W32.t Array4.t;
    var d:W32.t Array4.t;
    var i:int;
    var p:W32.t Array4.t;
    var q:W32.t Array4.t;
    a <- witness;
    b <- witness;
    c <- witness;
    d <- witness;
    p <- witness;
    q <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- copy_32 g;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- copy_32 a;
    b <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- copy_32 b;
    c <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- copy_32 c;
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- copy_32 d;
    a <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- (W32.of_int 0);
    x <- aux_1;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_1 <- (x + a.[i]);
      x <- aux_1;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- c;
    p <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- p;
    q <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- copy_32 a;
    p <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- copy_32 p;
    q <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- copy_32 q;
    d <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- copy_32 d;
    p <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- copy_32 a;
    a <- aux_0;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_1 <- (x + a.[i]);
      x <- aux_1;
      i <- i + 1;
    }
    return (x);
  }
}.

