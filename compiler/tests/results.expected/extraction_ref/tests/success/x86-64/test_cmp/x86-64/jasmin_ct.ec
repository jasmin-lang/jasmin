require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc f (x:W64.t, y:W64.t) : W64.t = {
    var aux: W64.t;
    
    var u:W64.t;
    var r:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    u <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    r <- aux;
    leakages <- LeakCond((x \ult y)) :: LeakAddr([]) :: leakages;
    if ((x \ult y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 1);
      r <- aux;
    } else {
      
    }
    leakages <- LeakCond((x \slt y)) :: LeakAddr([]) :: leakages;
    if ((x \slt y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 2);
      r <- aux;
    } else {
      
    }
    leakages <- LeakCond((x \ule y)) :: LeakAddr([]) :: leakages;
    if ((x \ule y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 3);
      r <- aux;
    } else {
      
    }
    leakages <- LeakCond((x \sle y)) :: LeakAddr([]) :: leakages;
    if ((x \sle y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 4);
      r <- aux;
    } else {
      
    }
    leakages <- LeakCond((x = y)) :: LeakAddr([]) :: leakages;
    if ((x = y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 5);
      r <- aux;
    } else {
      
    }
    leakages <- LeakCond((x <> y)) :: LeakAddr([]) :: leakages;
    if ((x <> y)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 6);
      r <- aux;
    } else {
      
    }
    leakages <- LeakCond((y \ult x)) :: LeakAddr([]) :: leakages;
    if ((y \ult x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 7);
      r <- aux;
    } else {
      
    }
    leakages <- LeakCond((y \slt x)) :: LeakAddr([]) :: leakages;
    if ((y \slt x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 8);
      r <- aux;
    } else {
      
    }
    leakages <- LeakCond((y \ule x)) :: LeakAddr([]) :: leakages;
    if ((y \ule x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 9);
      r <- aux;
    } else {
      
    }
    leakages <- LeakCond((y \sle x)) :: LeakAddr([]) :: leakages;
    if ((y \sle x)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W64.of_int 10);
      r <- aux;
    } else {
      
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- (u + r);
    u <- aux;
    return (u);
  }
}.

