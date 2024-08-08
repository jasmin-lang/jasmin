require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.



module M = {
  var leakages : leakages_t
  
  proc add (x:W64.t, y:W64.t) : W64.t = {
    var aux: W64.t;
    
    var z:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + y);
    z <- aux;
    return (z);
  }
  
  proc addc (x:W64.t, y:W64.t) : bool * W64.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var c:bool;
    var z:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <- adc_64 x y false;
    c <- aux;
    z <- aux_0;
    return (c, z);
  }
  
  proc main () : W64.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var z:W64.t;
    var c:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    (aux, aux_0) <@ addc ((W64.of_int 0), (W64.of_int 0));
    c <- aux;
    z <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ add ((W64.of_int 0), z);
    z <- aux_0;
    return (z);
  }
}.

