require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc __fp_rdcn_low (a:W64.t Array1.t) : W64.t * W64.t Array1.t = {
    var aux_0: W64.t;
    
    var result:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- a.[0];
    result <- aux_0;
    return (result, a);
  }
  
  proc fp_exp_low () : W64.t = {
    var aux_0: W64.t;
    var aux_1: W64.t Array1.t;
    
    var c:W64.t;
    var k:W64.t;
    var cnr:W64.t Array1.t;
    cnr <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    k <- aux_0;
    
    leakages <- LeakCond((k \ult (W64.of_int 64))) :: LeakAddr([]) :: leakages;
    
    while ((k \ult (W64.of_int 64))) {
      leakages <- LeakAddr([]) :: leakages;
      (aux_0, aux_1) <@ __fp_rdcn_low (cnr);
      c <- aux_0;
      cnr <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (k + (W64.of_int 1));
      k <- aux_0;
    leakages <- LeakCond((k \ult (W64.of_int 64))) :: LeakAddr([]) :: leakages;
    
    }
    return (c);
  }
  
  proc aux () : W64.t = {
    var aux_0: W64.t;
    var aux_1: W64.t Array1.t;
    
    var k:W64.t;
    var cnr:W64.t Array1.t;
    cnr <- witness;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux_1) <@ __fp_rdcn_low (cnr);
    k <- aux_0;
    cnr <- aux_1;
    return (k);
  }
  
  proc fp_exp_low1 () : W64.t = {
    var aux_0: W64.t;
    
    var c:W64.t;
    var k:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W64.of_int 0);
    k <- aux_0;
    
    leakages <- LeakCond((k \ult (W64.of_int 64))) :: LeakAddr([]) :: leakages;
    
    while ((k \ult (W64.of_int 64))) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ aux ();
      c <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (k + (W64.of_int 1));
      k <- aux_0;
    leakages <- LeakCond((k \ult (W64.of_int 64))) :: LeakAddr([]) :: leakages;
    
    }
    return (c);
  }
}.

