require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array4 Array20.
require import WArray32 WArray160.



module M = {
  proc init (t:W64.t Array4.t) : W64.t Array4.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 4) {
      t.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    return (t);
  }
  
  proc test1 (s:W64.t Array20.t) : W64.t Array20.t = {
    var aux: int;
    var aux_0: W64.t Array4.t;
    
    var i:int;
    
    i <- 0;
    while (i < 5) {
      aux_0 <@ init ((Array4.init (fun i_0 => s.[i + i_0])));
      s <- Array20.init (fun i_0 => if i <= i_0 < i + 4 then aux_0.[i_0-i] else s.[i_0]);
      i <- i + 1;
    }
    return (s);
  }
  
  proc test2 (s:W64.t Array20.t) : W64.t Array20.t = {
    
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
    s0 <- (Array4.init (fun i => s.[(0 * 4) + i]));
    s1 <- (Array4.init (fun i => s.[(1 * 4) + i]));
    s2 <- (Array4.init (fun i => s.[(2 * 4) + i]));
    s3 <- (Array4.init (fun i => s.[(3 * 4) + i]));
    s4 <- (Array4.init (fun i => s.[(4 * 4) + i]));
    aux <- s0;
    aux <@ init (aux);
    s0 <- aux;
    aux <- s1;
    aux <@ init (aux);
    s1 <- aux;
    aux <- s2;
    aux <@ init (aux);
    s2 <- aux;
    aux <- s3;
    aux <@ init (aux);
    s3 <- aux;
    aux <- s4;
    aux <@ init (aux);
    s4 <- aux;
    s <- Array20.init (fun i => if (0 * 4) <= i < (0 * 4) + 4 then s0.[i-(0 * 4)] else s.[i]);
    s <- Array20.init (fun i => if (1 * 4) <= i < (1 * 4) + 4 then s1.[i-(1 * 4)] else s.[i]);
    s <- Array20.init (fun i => if (2 * 4) <= i < (2 * 4) + 4 then s2.[i-(2 * 4)] else s.[i]);
    s <- Array20.init (fun i => if (3 * 4) <= i < (3 * 4) + 4 then s3.[i-(3 * 4)] else s.[i]);
    s <- Array20.init (fun i => if (4 * 4) <= i < (4 * 4) + 4 then s4.[i-(4 * 4)] else s.[i]);
    return (s);
  }
  
  proc test3 (s:W64.t Array20.t) : W64.t Array20.t = {
    
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
    s0 <- (Array4.init (fun i => s.[(0 * 4) + i]));
    s1 <- (Array4.init (fun i => s.[(1 * 4) + i]));
    aux <- s0;
    aux <@ init (aux);
    s0 <- aux;
    aux <- s1;
    aux <@ init (aux);
    s1 <- aux;
    s.[(2 * 4)] <- (W64.of_int 10);
    s2 <- (Array4.init (fun i => s.[(2 * 4) + i]));
    s3 <- (Array4.init (fun i => s.[(3 * 4) + i]));
    s4 <- (Array4.init (fun i => s.[(4 * 4) + i]));
    aux <- s2;
    aux <@ init (aux);
    s2 <- aux;
    aux <- s3;
    aux <@ init (aux);
    s3 <- aux;
    aux <- s4;
    aux <@ init (aux);
    s4 <- aux;
    s <- Array20.init (fun i => if (0 * 4) <= i < (0 * 4) + 4 then s0.[i-(0 * 4)] else s.[i]);
    s <- Array20.init (fun i => if (1 * 4) <= i < (1 * 4) + 4 then s1.[i-(1 * 4)] else s.[i]);
    s <- Array20.init (fun i => if (2 * 4) <= i < (2 * 4) + 4 then s2.[i-(2 * 4)] else s.[i]);
    s <- Array20.init (fun i => if (3 * 4) <= i < (3 * 4) + 4 then s3.[i-(3 * 4)] else s.[i]);
    s <- Array20.init (fun i => if (4 * 4) <= i < (4 * 4) + 4 then s4.[i-(4 * 4)] else s.[i]);
    return (s);
  }
  
  proc test () : W64.t = {
    var aux: int;
    var aux_0: W64.t Array4.t;
    
    var r:W64.t;
    var i:int;
    var s:W64.t Array20.t;
    s <- witness;
    i <- 0;
    while (i < 5) {
      aux_0 <@ init ((Array4.init (fun i_0 => s.[(i * 4) + i_0])));
      s <- Array20.init (fun i_0 => if (i * 4) <= i_0 < (i * 4) + 4 then aux_0.[i_0-(i * 4)] else s.[i_0]);
      i <- i + 1;
    }
    r <- s.[((5 * 4) - 1)];
    return (r);
  }
}.

