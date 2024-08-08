require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array10 Array100.
require import WArray80 WArray800.



module M = {
  proc dot_product (v1:W64.t Array10.t, v2:W64.t Array10.t) : W64.t = {
    var aux: int;
    
    var res_0:W64.t;
    var i:int;
    var tmp:W64.t;
    
    res_0 <- (W64.of_int 0);
    i <- 0;
    while (i < 10) {
      tmp <- v1.[i];
      tmp <- (tmp * v2.[i]);
      res_0 <- (res_0 + tmp);
      i <- i + 1;
    }
    return (res_0);
  }
  
  proc product_matrix_vector (m:W64.t Array100.t, v:W64.t Array10.t, res_0:W64.t Array10.t) : 
  W64.t Array10.t = {
    var aux: int;
    
    var i:int;
    var tmp:W64.t;
    
    i <- 0;
    while (i < 10) {
      tmp <@ dot_product ((Array10.init (fun i_0 => m.[(i * 10) + i_0])), v);
      res_0.[i] <- tmp;
      i <- i + 1;
    }
    return (res_0);
  }
  
  proc transpose (m:W64.t Array100.t, res_0:W64.t Array100.t) : W64.t Array100.t = {
    var aux: int;
    
    var i:int;
    var j:int;
    var tmp:W64.t;
    
    i <- 0;
    while (i < 10) {
      j <- 0;
      while (j < 10) {
        tmp <- m.[(j + (i * 10))];
        res_0.[(i + (j * 10))] <- tmp;
        j <- j + 1;
      }
      i <- i + 1;
    }
    return (res_0);
  }
  
  proc product_matrix_matrix (m1:W64.t Array100.t, m2:W64.t Array100.t, res_0:W64.t Array100.t) : 
  W64.t Array100.t = {
    var aux: int;
    var aux_0: W64.t Array10.t;
    
    var pres:W64.t Array100.t;
    var m2t:W64.t Array100.t;
    var i:int;
    var rest:W64.t Array100.t;
    m2t <- witness;
    pres <- witness;
    rest <- witness;
    pres <- res_0;
    m2t <@ transpose (m2, m2t);
    i <- 0;
    while (i < 10) {
      aux_0 <@ product_matrix_vector (m1, (Array10.init (fun i_0 => m2t.[(i * 10) + i_0])), (Array10.init (fun i_0 => rest.[(i * 10) + i_0])));
      rest <- Array100.init (fun i_0 => if (i * 10) <= i_0 < (i * 10) + 10 then aux_0.[i_0-(i * 10)] else rest.[i_0]);
      i <- i + 1;
    }
    res_0 <- pres;
    res_0 <@ transpose (rest, res_0);
    return (res_0);
  }
  
  proc productMM (x:W64.t, y:W64.t, z:W64.t) : unit = {
    var aux: int;
    
    var i:int;
    var tmp:W64.t;
    var mx:W64.t Array100.t;
    var my:W64.t Array100.t;
    var mz:W64.t Array100.t;
    mx <- witness;
    my <- witness;
    mz <- witness;
    aux <- (10 * 10);
    i <- 0;
    while (i < aux) {
      tmp <- (loadW64 Glob.mem (W64.to_uint (x + (W64.of_int (8 * i)))));
      mx.[i] <- tmp;
      tmp <- (loadW64 Glob.mem (W64.to_uint (y + (W64.of_int (8 * i)))));
      my.[i] <- tmp;
      i <- i + 1;
    }
    mz <@ product_matrix_matrix (mx, my, mz);
    aux <- (10 * 10);
    i <- 0;
    while (i < aux) {
      tmp <- mz.[i];
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (z + (W64.of_int (8 * i)))) (tmp);
      i <- i + 1;
    }
    return ();
  }
}.

