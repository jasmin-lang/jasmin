require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2.
require import WArray16.



module M = {
  var leakages : leakages_t
  
  proc init () : W64.t Array2.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var r:W64.t Array2.t;
    var i:int;
    r <- witness;
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int i);
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
  
  proc add (a:W64.t Array2.t, b:W64.t Array2.t) : W64.t Array2.t = {
    var aux: W64.t;
    
    var i:W64.t;
    var t:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    i <- aux;
    
    leakages <- LeakCond((i \ult (W64.of_int 2))) :: LeakAddr([]) :: leakages;
    
    while ((i \ult (W64.of_int 2))) {
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux <- a.[(W64.to_uint i)];
      t <- aux;
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux <- (t + b.[(W64.to_uint i)]);
      t <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- t;
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      a.[(W64.to_uint i)] <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult (W64.of_int 2))) :: LeakAddr([]) :: leakages;
    
    }
    return (a);
  }
  
  proc store (p:W64.t, x:W64.t Array2.t) : unit = {
    var aux: W64.t;
    
    var i:W64.t;
    var t:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    i <- aux;
    
    leakages <- LeakCond((i \ult (W64.of_int 2))) :: LeakAddr([]) :: leakages;
    
    while ((i \ult (W64.of_int 2))) {
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux <- x.[(W64.to_uint i)];
      t <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- t;
      leakages <- LeakAddr([(W64.to_uint (p + ((W64.of_int 8) * i)))]) :: leakages;
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + ((W64.of_int 8) * i))) (aux);
      leakages <- LeakAddr([]) :: leakages;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult (W64.of_int 2))) :: LeakAddr([]) :: leakages;
    
    }
    return ();
  }
  
  proc test1 (p:W64.t) : unit = {
    var aux: W64.t Array2.t;
    
    var a:W64.t Array2.t;
    var ap:W64.t Array2.t;
    var b:W64.t Array2.t;
    var bp:W64.t Array2.t;
    a <- witness;
    ap <- witness;
    b <- witness;
    bp <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ init ();
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    ap <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ init ();
    b <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    bp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ add (ap, bp);
    ap <- aux;
    leakages <- LeakAddr([]) :: leakages;
    store (p, ap);
    leakages <- LeakAddr([]) :: leakages;
    store (p, bp);
    return ();
  }
}.

