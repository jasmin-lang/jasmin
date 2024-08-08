require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.
require import Array1025.
require import WArray4100.



module M = {
  var leakages : leakages_t
  
  proc foo () : W32.t = {
    var aux: W32.t;
    var aux_0: W32.t Array1025.t;
    
    var x:W32.t;
    var z:W32.t;
    var i:W32.t;
    var n:W32.t;
    var s1:W32.t Array1025.t;
    var ps1:W32.t Array1025.t;
    var s2:W32.t Array1025.t;
    var ps2:W32.t Array1025.t;
    ps1 <- witness;
    ps2 <- witness;
    s1 <- witness;
    s2 <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    i <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 1025);
    n <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s1;
    ps1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s2;
    ps2 <- aux_0;
    
    leakages <- LeakCond((i \ult n)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult n)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- z;
      leakages <- LeakAddr([(W32.to_uint i)]) :: leakages;
      ps1.[(W32.to_uint i)] <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- z;
      leakages <- LeakAddr([(W32.to_uint i)]) :: leakages;
      ps2.[(W32.to_uint i)] <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (i + (W32.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult n)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([0]) :: leakages;
    aux <- ps1.[0];
    x <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- ps2.[0];
    n <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (x + n);
    x <- aux;
    return (x);
  }
  
  proc main () : W32.t = {
    var aux: W32.t;
    
    var r:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ foo ();
    r <- aux;
    return (r);
  }
}.

