require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2 Array6.
require import WArray16 WArray48.



module M = {
  proc init (t:W64.t Array2.t) : W64.t Array2.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 2) {
      t.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    return (t);
  }
  
  proc test2 () : W64.t Array6.t = {
    
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
    s0 <- (Array2.init (fun i => s.[(0 * 2) + i]));
    s1 <- (Array2.init (fun i => s.[(1 * 2) + i]));
    s2 <- (Array2.init (fun i => s.[(2 * 2) + i]));
    aux <- s0;
    aux <@ init (aux);
    s0 <- aux;
    aux <- s1;
    aux <@ init (aux);
    s1 <- aux;
    aux <- s2;
    aux <@ init (aux);
    s2 <- aux;
    s <- Array6.init (fun i => if (0 * 2) <= i < (0 * 2) + 2 then s0.[i-(0 * 2)] else s.[i]);
    s <- Array6.init (fun i => if (1 * 2) <= i < (1 * 2) + 2 then s1.[i-(1 * 2)] else s.[i]);
    s <- Array6.init (fun i => if (2 * 2) <= i < (2 * 2) + 2 then s2.[i-(2 * 2)] else s.[i]);
    return (s);
  }
  
  proc test () : W64.t = {
    
    var r:W64.t;
    var s:W64.t Array6.t;
    s <- witness;
    s <@ test2 ();
    r <- s.[((3 * 2) - 1)];
    return (r);
  }
  
  proc test2_ () : W64.t Array6.t = {
    var aux: int;
    var aux_0: W64.t Array2.t;
    
    var s:W64.t Array6.t;
    var i:int;
    s <- witness;
    i <- 0;
    while (i < 3) {
      aux_0 <@ init ((Array2.init (fun i_0 => s.[(i * 2) + i_0])));
      s <- Array6.init (fun i_0 => if (i * 2) <= i_0 < (i * 2) + 2 then aux_0.[i_0-(i * 2)] else s.[i_0]);
      i <- i + 1;
    }
    return (s);
  }
  
  proc test_ () : W64.t = {
    
    var r:W64.t;
    var s:W64.t Array6.t;
    s <- witness;
    s <@ test2_ ();
    r <- s.[((3 * 2) - 1)];
    return (r);
  }
}.

