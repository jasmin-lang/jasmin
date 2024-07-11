require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray8.



module M = {
  var leakages : leakages_t
  
  proc reduce () : W64.t Array1.t = {
    var aux: W64.t;
    
    var xa:W64.t Array1.t;
    xa <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    xa.[0] <- aux;
    return (xa);
  }
  
  proc iterated_square (xa:W64.t Array1.t, n:W64.t) : W64.t Array1.t = {
    var aux_0: bool;
    var aux_1: W64.t;
    var aux: W64.t Array1.t;
    
    var cf:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ reduce ();
    xa <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux_1) <- sbb_64 n (W64.of_int 1) false;
    cf <- aux_0;
    n <- aux_1;
    leakages <- LeakCond((! cf)) :: LeakAddr([]) :: leakages;
    
    while ((! cf)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <@ reduce ();
      xa <- aux;
      leakages <- LeakAddr([]) :: leakages;
      (aux_0, aux_1) <- sbb_64 n (W64.of_int 1) false;
      cf <- aux_0;
      n <- aux_1;
    leakages <- LeakCond((! cf)) :: LeakAddr([]) :: leakages;
    
    }
    return (xa);
  }
  
  proc iterated_square_export (xap:W64.t, n:W64.t) : unit = {
    var aux: W64.t;
    var aux_0: W64.t Array1.t;
    
    var xa:W64.t Array1.t;
    var ns:W64.t;
    xa <- witness;
    leakages <- LeakAddr([(W64.to_uint (xap + (W64.of_int 0)))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (xap + (W64.of_int 0))));
    leakages <- LeakAddr([0]) :: leakages;
    xa.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- n;
    ns <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ iterated_square (xa, ns);
    xa <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- xa.[0];
    leakages <- LeakAddr([(W64.to_uint (xap + (W64.of_int 0)))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (xap + (W64.of_int 0))) (aux);
    return ();
  }
}.

