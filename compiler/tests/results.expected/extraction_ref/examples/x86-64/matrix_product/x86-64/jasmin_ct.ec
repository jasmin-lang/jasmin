require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array10 Array100.
require import WArray80 WArray800.



module M = {
  var leakages : leakages_t
  
  proc dot_product (v1:W64.t Array10.t, v2:W64.t Array10.t) : W64.t = {
    var aux_0: int;
    var aux: W64.t;
    
    var res_0:W64.t;
    var i:int;
    var tmp:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    res_0 <- aux;
    leakages <- LeakFor(0,10) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 10) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- v1.[i];
      tmp <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (tmp * v2.[i]);
      tmp <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (res_0 + tmp);
      res_0 <- aux;
      i <- i + 1;
    }
    return (res_0);
  }
  
  proc product_matrix_vector (m:W64.t Array100.t, v:W64.t Array10.t, res_0:W64.t Array10.t) : 
  W64.t Array10.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var tmp:W64.t;
    
    leakages <- LeakFor(0,10) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 10) {
      leakages <- LeakAddr([(i * 10)]) :: leakages;
      aux_0 <@ dot_product ((Array10.init (fun i_0 => m.[(i * 10) + i_0])), v);
      tmp <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- tmp;
      leakages <- LeakAddr([i]) :: leakages;
      res_0.[i] <- aux_0;
      i <- i + 1;
    }
    return (res_0);
  }
  
  proc transpose (m:W64.t Array100.t, res_0:W64.t Array100.t) : W64.t Array100.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    var j:int;
    var tmp:W64.t;
    
    leakages <- LeakFor(0,10) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 10) {
      leakages <- LeakFor(0,10) :: LeakAddr([]) :: leakages;
      j <- 0;
      while (j < 10) {
        leakages <- LeakAddr([(j + (i * 10))]) :: leakages;
        aux_0 <- m.[(j + (i * 10))];
        tmp <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- tmp;
        leakages <- LeakAddr([(i + (j * 10))]) :: leakages;
        res_0.[(i + (j * 10))] <- aux_0;
        j <- j + 1;
      }
      i <- i + 1;
    }
    return (res_0);
  }
  
  proc product_matrix_matrix (m1:W64.t Array100.t, m2:W64.t Array100.t, res_0:W64.t Array100.t) : 
  W64.t Array100.t = {
    var aux_0: int;
    var aux_1: W64.t Array10.t;
    var aux: W64.t Array100.t;
    
    var pres:W64.t Array100.t;
    var m2t:W64.t Array100.t;
    var i:int;
    var rest:W64.t Array100.t;
    m2t <- witness;
    pres <- witness;
    rest <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- res_0;
    pres <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ transpose (m2, m2t);
    m2t <- aux;
    leakages <- LeakFor(0,10) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 10) {
      leakages <- LeakAddr([(i * 10); (i * 10)]) :: leakages;
      aux_1 <@ product_matrix_vector (m1, (Array10.init (fun i_0 => m2t.[(i * 10) + i_0])), (Array10.init (fun i_0 => rest.[(i * 10) + i_0])));
      leakages <- LeakAddr([(i * 10)]) :: leakages;
      rest <- Array100.init (fun i_0 => if (i * 10) <= i_0 < (i * 10) + 10 then aux_1.[i_0-(i * 10)] else rest.[i_0]);
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux <- pres;
    res_0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ transpose (rest, res_0);
    res_0 <- aux;
    return (res_0);
  }
  
  proc productMM (x:W64.t, y:W64.t, z:W64.t) : unit = {
    var aux: int;
    var aux_0: W64.t;
    var aux_1: W64.t Array100.t;
    
    var i:int;
    var tmp:W64.t;
    var mx:W64.t Array100.t;
    var my:W64.t Array100.t;
    var mz:W64.t Array100.t;
    mx <- witness;
    my <- witness;
    mz <- witness;
    leakages <- LeakFor(0,(10 * 10)) :: LeakAddr([]) :: leakages;
    aux <- (10 * 10);
    i <- 0;
    while (i < aux) {
      leakages <- LeakAddr([(W64.to_uint (x + (W64.of_int (8 * i))))]) :: leakages;
      aux_0 <- (loadW64 Glob.mem (W64.to_uint (x + (W64.of_int (8 * i)))));
      tmp <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- tmp;
      leakages <- LeakAddr([i]) :: leakages;
      mx.[i] <- aux_0;
      leakages <- LeakAddr([(W64.to_uint (y + (W64.of_int (8 * i))))]) :: leakages;
      aux_0 <- (loadW64 Glob.mem (W64.to_uint (y + (W64.of_int (8 * i)))));
      tmp <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- tmp;
      leakages <- LeakAddr([i]) :: leakages;
      my.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <@ product_matrix_matrix (mx, my, mz);
    mz <- aux_1;
    leakages <- LeakFor(0,(10 * 10)) :: LeakAddr([]) :: leakages;
    aux <- (10 * 10);
    i <- 0;
    while (i < aux) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- mz.[i];
      tmp <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- tmp;
      leakages <- LeakAddr([(W64.to_uint (z + (W64.of_int (8 * i))))]) :: leakages;
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (z + (W64.of_int (8 * i)))) (aux_0);
      i <- i + 1;
    }
    return ();
  }
}.

