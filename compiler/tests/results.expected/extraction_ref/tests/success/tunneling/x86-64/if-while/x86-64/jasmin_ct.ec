require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc nested_ifs (x:W64.t, y:W64.t, z:W64.t) : W64.t = {
    var aux: W64.t;
    
    var r:W64.t;
    var i:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    i <- aux;
    leakages <- LeakCond((x \ult y)) :: LeakAddr([]) :: leakages;
    if ((x \ult y)) {
      leakages <- LeakCond((y \ult z)) :: LeakAddr([]) :: leakages;
      if ((y \ult z)) {
        leakages <- LeakAddr([]) :: leakages;
        aux <- (W64.of_int 0);
        r <- aux;
      } else {
        leakages <- LeakCond((x \ult z)) :: LeakAddr([]) :: leakages;
        if ((x \ult z)) {
          leakages <- LeakAddr([]) :: leakages;
          aux <- (W64.of_int 1);
          r <- aux;
        } else {
          leakages <- LeakAddr([]) :: leakages;
          aux <- (W64.of_int 2);
          r <- aux;
        }
      }
    } else {
      leakages <- LeakCond((x \ult z)) :: LeakAddr([]) :: leakages;
      if ((x \ult z)) {
        leakages <- LeakAddr([]) :: leakages;
        aux <- (W64.of_int 3);
        r <- aux;
      } else {
        leakages <- LeakCond((y \ult z)) :: LeakAddr([]) :: leakages;
        if ((y \ult z)) {
          leakages <- LeakAddr([]) :: leakages;
          aux <- (W64.of_int 4);
          r <- aux;
        } else {
          leakages <- LeakAddr([]) :: leakages;
          aux <- (W64.of_int 5);
          r <- aux;
        }
      }
    }
    
    leakages <- LeakCond((i \ult (W64.of_int 0))) :: LeakAddr([]) :: leakages;
    
    while ((i \ult (W64.of_int 0))) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult (W64.of_int 0))) :: LeakAddr([]) :: leakages;
    
    }
    return (r);
  }
}.

