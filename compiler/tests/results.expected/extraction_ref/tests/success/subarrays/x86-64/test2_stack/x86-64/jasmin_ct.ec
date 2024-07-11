require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2 Array6.
require import WArray16 WArray48.



module M = {
  var leakages : leakages_t
  
  proc init (t:W64.t Array2.t) : W64.t Array2.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      i <- i + 1;
    }
    return (t);
  }
  
  proc test2 () : W64.t Array6.t = {
    var aux_0: W64.t Array2.t;
    
    var s:W64.t Array6.t;
    var s0:W64.t Array2.t;
    var s1:W64.t Array2.t;
    var s2:W64.t Array2.t;
    var aux:W64.t Array2.t;
    aux <- witness;
    s <- witness;
    s0 <- witness;
    s1 <- witness;
    s2 <- witness;
    leakages <- LeakAddr([(0 * 2)]) :: leakages;
    aux_0 <- (Array2.init (fun i => s.[(0 * 2) + i]));
    s0 <- aux_0;
    leakages <- LeakAddr([(1 * 2)]) :: leakages;
    aux_0 <- (Array2.init (fun i => s.[(1 * 2) + i]));
    s1 <- aux_0;
    leakages <- LeakAddr([(2 * 2)]) :: leakages;
    aux_0 <- (Array2.init (fun i => s.[(2 * 2) + i]));
    s2 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s0;
    aux <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ init (aux);
    aux <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- aux;
    s0 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s1;
    aux <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ init (aux);
    aux <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- aux;
    s1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s2;
    aux <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ init (aux);
    aux <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- aux;
    s2 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s0;
    leakages <- LeakAddr([(0 * 2)]) :: leakages;
    s <- Array6.init (fun i => if (0 * 2) <= i < (0 * 2) + 2 then aux_0.[i-(0 * 2)] else s.[i]);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s1;
    leakages <- LeakAddr([(1 * 2)]) :: leakages;
    s <- Array6.init (fun i => if (1 * 2) <= i < (1 * 2) + 2 then aux_0.[i-(1 * 2)] else s.[i]);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s2;
    leakages <- LeakAddr([(2 * 2)]) :: leakages;
    s <- Array6.init (fun i => if (2 * 2) <= i < (2 * 2) + 2 then aux_0.[i-(2 * 2)] else s.[i]);
    return (s);
  }
  
  proc test () : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t Array6.t;
    
    var r:W64.t;
    var s:W64.t Array6.t;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ test2 ();
    s <- aux;
    leakages <- LeakAddr([((3 * 2) - 1)]) :: leakages;
    aux_0 <- s.[((3 * 2) - 1)];
    r <- aux_0;
    return (r);
  }
  
  proc test2_ () : W64.t Array6.t = {
    var aux: int;
    var aux_0: W64.t Array2.t;
    
    var s:W64.t Array6.t;
    var i:int;
    s <- witness;
    leakages <- LeakFor(0,3) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 3) {
      leakages <- LeakAddr([(i * 2)]) :: leakages;
      aux_0 <@ init ((Array2.init (fun i_0 => s.[(i * 2) + i_0])));
      leakages <- LeakAddr([(i * 2)]) :: leakages;
      s <- Array6.init (fun i_0 => if (i * 2) <= i_0 < (i * 2) + 2 then aux_0.[i_0-(i * 2)] else s.[i_0]);
      i <- i + 1;
    }
    return (s);
  }
  
  proc test_ () : W64.t = {
    var aux_0: W64.t;
    var aux: W64.t Array6.t;
    
    var r:W64.t;
    var s:W64.t Array6.t;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ test2_ ();
    s <- aux;
    leakages <- LeakAddr([((3 * 2) - 1)]) :: leakages;
    aux_0 <- s.[((3 * 2) - 1)];
    r <- aux_0;
    return (r);
  }
}.

