require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.
require import Array1025.
require import WArray4100.



module M = {
  var leakages : leakages_t
  
  proc large () : W32.t = {
    var aux_0: W32.t;
    var aux: W32.t Array1025.t;
    
    var s:W32.t;
    var st:W32.t Array1025.t;
    var t:W32.t Array1025.t;
    var i:W32.t;
    var n:W32.t;
    var tmp:W32.t;
    st <- witness;
    t <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- st;
    t <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 0);
    i <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int (1025 - 1));
    n <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (n + (W32.of_int 1));
    n <- aux_0;
    
    leakages <- LeakCond((i \ult n)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult n)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- i;
      leakages <- LeakAddr([(W32.to_uint i)]) :: leakages;
      t.[(W32.to_uint i)] <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (i + (W32.of_int 1));
      i <- aux_0;
    leakages <- LeakCond((i \ult n)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 0);
    i <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 0);
    s <- aux_0;
    
    leakages <- LeakCond((i \ult n)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult n)) {
      leakages <- LeakAddr([(W32.to_uint i)]) :: leakages;
      aux_0 <- t.[(W32.to_uint i)];
      tmp <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (s + tmp);
      s <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (i + (W32.of_int 1));
      i <- aux_0;
    leakages <- LeakCond((i \ult n)) :: LeakAddr([]) :: leakages;
    
    }
    return (s);
  }
  
  proc main () : W32.t = {
    var aux: W32.t;
    
    var s:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ large ();
    s <- aux;
    return (s);
  }
}.

