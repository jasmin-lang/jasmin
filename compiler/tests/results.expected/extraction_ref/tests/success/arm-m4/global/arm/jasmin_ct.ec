require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.
require import Array4.
require import WArray4.

abbrev t = Array4.of_list witness [W8.of_int 1; W8.of_int 2; W8.of_int 3; W8.of_int 4].


abbrev g = W32.of_int 42.


module M = {
  var leakages : leakages_t
  
  proc fourtytwo () : W32.t = {
    var aux: W32.t;
    
    var r:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- g;
    r <- aux;
    return (r);
  }
  
  proc two () : W32.t = {
    var aux: W32.t;
    
    var r:W32.t;
    
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (zeroextu32 t.[1]);
    r <- aux;
    return (r);
  }
  
  proc mod4p1 (i:W32.t) : W32.t = {
    var aux_0: W32.t;
    var aux: W8.t Array4.t;
    
    var r:W32.t;
    var p:W8.t Array4.t;
    p <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- t;
    p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (i `&` (W32.of_int 3));
    i <- aux_0;
    leakages <- LeakAddr([(W32.to_uint i)]) :: leakages;
    aux_0 <- (zeroextu32 p.[(W32.to_uint i)]);
    r <- aux_0;
    return (r);
  }
}.

