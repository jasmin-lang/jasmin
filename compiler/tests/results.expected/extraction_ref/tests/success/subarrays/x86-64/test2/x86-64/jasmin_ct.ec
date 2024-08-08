require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array4 Array20.
require import WArray32 WArray160.



module M = {
  var leakages : leakages_t
  
  proc init (t:W64.t Array4.t) : W64.t Array4.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      i <- i + 1;
    }
    return (t);
  }
  
  proc test1 (s:W64.t Array20.t) : W64.t Array20.t = {
    var aux: int;
    var aux_0: W64.t Array4.t;
    
    var i:int;
    
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 5) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <@ init ((Array4.init (fun i_0 => s.[i + i_0])));
      leakages <- LeakAddr([i]) :: leakages;
      s <- Array20.init (fun i_0 => if i <= i_0 < i + 4 then aux_0.[i_0-i] else s.[i_0]);
      i <- i + 1;
    }
    return (s);
  }
  
  proc test2 (s:W64.t Array20.t) : W64.t Array20.t = {
    var aux_0: W64.t Array4.t;
    
    var s0:W64.t Array4.t;
    var s1:W64.t Array4.t;
    var s2:W64.t Array4.t;
    var s3:W64.t Array4.t;
    var s4:W64.t Array4.t;
    var aux:W64.t Array4.t;
    aux <- witness;
    s0 <- witness;
    s1 <- witness;
    s2 <- witness;
    s3 <- witness;
    s4 <- witness;
    leakages <- LeakAddr([(0 * 4)]) :: leakages;
    aux_0 <- (Array4.init (fun i => s.[(0 * 4) + i]));
    s0 <- aux_0;
    leakages <- LeakAddr([(1 * 4)]) :: leakages;
    aux_0 <- (Array4.init (fun i => s.[(1 * 4) + i]));
    s1 <- aux_0;
    leakages <- LeakAddr([(2 * 4)]) :: leakages;
    aux_0 <- (Array4.init (fun i => s.[(2 * 4) + i]));
    s2 <- aux_0;
    leakages <- LeakAddr([(3 * 4)]) :: leakages;
    aux_0 <- (Array4.init (fun i => s.[(3 * 4) + i]));
    s3 <- aux_0;
    leakages <- LeakAddr([(4 * 4)]) :: leakages;
    aux_0 <- (Array4.init (fun i => s.[(4 * 4) + i]));
    s4 <- aux_0;
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
    aux_0 <- s3;
    aux <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ init (aux);
    aux <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- aux;
    s3 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s4;
    aux <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ init (aux);
    aux <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- aux;
    s4 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s0;
    leakages <- LeakAddr([(0 * 4)]) :: leakages;
    s <- Array20.init (fun i => if (0 * 4) <= i < (0 * 4) + 4 then aux_0.[i-(0 * 4)] else s.[i]);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s1;
    leakages <- LeakAddr([(1 * 4)]) :: leakages;
    s <- Array20.init (fun i => if (1 * 4) <= i < (1 * 4) + 4 then aux_0.[i-(1 * 4)] else s.[i]);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s2;
    leakages <- LeakAddr([(2 * 4)]) :: leakages;
    s <- Array20.init (fun i => if (2 * 4) <= i < (2 * 4) + 4 then aux_0.[i-(2 * 4)] else s.[i]);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s3;
    leakages <- LeakAddr([(3 * 4)]) :: leakages;
    s <- Array20.init (fun i => if (3 * 4) <= i < (3 * 4) + 4 then aux_0.[i-(3 * 4)] else s.[i]);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s4;
    leakages <- LeakAddr([(4 * 4)]) :: leakages;
    s <- Array20.init (fun i => if (4 * 4) <= i < (4 * 4) + 4 then aux_0.[i-(4 * 4)] else s.[i]);
    return (s);
  }
  
  proc test3 (s:W64.t Array20.t) : W64.t Array20.t = {
    var aux_1: W64.t;
    var aux_0: W64.t Array4.t;
    
    var s0:W64.t Array4.t;
    var s1:W64.t Array4.t;
    var aux:W64.t Array4.t;
    var s2:W64.t Array4.t;
    var s3:W64.t Array4.t;
    var s4:W64.t Array4.t;
    aux <- witness;
    s0 <- witness;
    s1 <- witness;
    s2 <- witness;
    s3 <- witness;
    s4 <- witness;
    leakages <- LeakAddr([(0 * 4)]) :: leakages;
    aux_0 <- (Array4.init (fun i => s.[(0 * 4) + i]));
    s0 <- aux_0;
    leakages <- LeakAddr([(1 * 4)]) :: leakages;
    aux_0 <- (Array4.init (fun i => s.[(1 * 4) + i]));
    s1 <- aux_0;
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
    aux_1 <- (W64.of_int 10);
    leakages <- LeakAddr([(2 * 4)]) :: leakages;
    s.[(2 * 4)] <- aux_1;
    leakages <- LeakAddr([(2 * 4)]) :: leakages;
    aux_0 <- (Array4.init (fun i => s.[(2 * 4) + i]));
    s2 <- aux_0;
    leakages <- LeakAddr([(3 * 4)]) :: leakages;
    aux_0 <- (Array4.init (fun i => s.[(3 * 4) + i]));
    s3 <- aux_0;
    leakages <- LeakAddr([(4 * 4)]) :: leakages;
    aux_0 <- (Array4.init (fun i => s.[(4 * 4) + i]));
    s4 <- aux_0;
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
    aux_0 <- s3;
    aux <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ init (aux);
    aux <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- aux;
    s3 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s4;
    aux <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ init (aux);
    aux <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- aux;
    s4 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s0;
    leakages <- LeakAddr([(0 * 4)]) :: leakages;
    s <- Array20.init (fun i => if (0 * 4) <= i < (0 * 4) + 4 then aux_0.[i-(0 * 4)] else s.[i]);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s1;
    leakages <- LeakAddr([(1 * 4)]) :: leakages;
    s <- Array20.init (fun i => if (1 * 4) <= i < (1 * 4) + 4 then aux_0.[i-(1 * 4)] else s.[i]);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s2;
    leakages <- LeakAddr([(2 * 4)]) :: leakages;
    s <- Array20.init (fun i => if (2 * 4) <= i < (2 * 4) + 4 then aux_0.[i-(2 * 4)] else s.[i]);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s3;
    leakages <- LeakAddr([(3 * 4)]) :: leakages;
    s <- Array20.init (fun i => if (3 * 4) <= i < (3 * 4) + 4 then aux_0.[i-(3 * 4)] else s.[i]);
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s4;
    leakages <- LeakAddr([(4 * 4)]) :: leakages;
    s <- Array20.init (fun i => if (4 * 4) <= i < (4 * 4) + 4 then aux_0.[i-(4 * 4)] else s.[i]);
    return (s);
  }
  
  proc test () : W64.t = {
    var aux: int;
    var aux_1: W64.t;
    var aux_0: W64.t Array4.t;
    
    var r:W64.t;
    var i:int;
    var s:W64.t Array20.t;
    s <- witness;
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 5) {
      leakages <- LeakAddr([(i * 4)]) :: leakages;
      aux_0 <@ init ((Array4.init (fun i_0 => s.[(i * 4) + i_0])));
      leakages <- LeakAddr([(i * 4)]) :: leakages;
      s <- Array20.init (fun i_0 => if (i * 4) <= i_0 < (i * 4) + 4 then aux_0.[i_0-(i * 4)] else s.[i_0]);
      i <- i + 1;
    }
    leakages <- LeakAddr([((5 * 4) - 1)]) :: leakages;
    aux_1 <- s.[((5 * 4) - 1)];
    r <- aux_1;
    return (r);
  }
}.

