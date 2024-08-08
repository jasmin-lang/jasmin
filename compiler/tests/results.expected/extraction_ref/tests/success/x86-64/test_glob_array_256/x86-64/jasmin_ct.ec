require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array4.
require import WArray128.

abbrev glob_t = Array4.of_list witness [W256.of_int 0; W256.of_int 1; W256.of_int 2; W256.of_int 3].


module M = {
  var leakages : leakages_t
  
  proc sum (x:W64.t) : W64.t = {
    var aux_2: W64.t;
    var aux_1: W256.t;
    var aux_0: W256.t Array4.t;
    
    var r:W64.t;
    var gt1:W256.t Array4.t;
    var aux:W256.t;
    var i:W64.t;
    gt1 <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- glob_t;
    gt1 <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_1 <- glob_t.[0];
    aux <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (W64.of_int 32);
    i <- aux_2;
    
    leakages <- LeakCond((i \ule (W64.of_int (3 * 32)))) :: LeakAddr(
    []) :: leakages;
    
    while ((i \ule (W64.of_int (3 * 32)))) {
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux_1 <- (aux `^` (get256_direct (WArray128.init256 (fun i_0 => (gt1).[i_0])) (W64.to_uint i)));
      aux <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <- (i + (W64.of_int 32));
      i <- aux_2;
    leakages <- LeakCond((i \ule (W64.of_int (3 * 32)))) :: LeakAddr(
    []) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (W64.of_int 4);
    i <- aux_2;
    
    leakages <- LeakCond((i \ule (W64.of_int (3 * 4)))) :: LeakAddr([]) :: leakages;
    
    while ((i \ule (W64.of_int (3 * 4)))) {
      leakages <- LeakAddr([(W64.to_uint ((W64.of_int 8) * i))]) :: leakages;
      aux_1 <- (aux `^` (get256_direct (WArray128.init256 (fun i_0 => (gt1).[i_0])) (W64.to_uint ((W64.of_int 8) * i))));
      aux <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <- (i + (W64.of_int 4));
      i <- aux_2;
    leakages <- LeakCond((i \ule (W64.of_int (3 * 4)))) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- VPEXTR_64 (truncateu128 aux) (W8.of_int 0);
    r <- aux_2;
    return (r);
  }
  
  proc sum1 (x:W64.t) : W64.t = {
    var aux_2: W64.t;
    var aux_1: W128.t;
    var aux_0: W256.t Array4.t;
    
    var r:W64.t;
    var gt1:W256.t Array4.t;
    var aux:W128.t;
    var i:W64.t;
    gt1 <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- glob_t;
    gt1 <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_1 <- (get128 (WArray128.init256 (fun i_0 => (glob_t).[i_0])) 0);
    aux <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (W64.of_int 16);
    i <- aux_2;
    
    leakages <- LeakCond((i \ule (W64.of_int (7 * 16)))) :: LeakAddr(
    []) :: leakages;
    
    while ((i \ule (W64.of_int (7 * 16)))) {
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      aux_1 <- (aux `^` (get128_direct (WArray128.init256 (fun i_0 => (gt1).[i_0])) (W64.to_uint i)));
      aux <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <- (i + (W64.of_int 16));
      i <- aux_2;
    leakages <- LeakCond((i \ule (W64.of_int (7 * 16)))) :: LeakAddr(
    []) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- (W64.of_int 8);
    i <- aux_2;
    
    leakages <- LeakCond((i \ule (W64.of_int (3 * 4)))) :: LeakAddr([]) :: leakages;
    
    while ((i \ule (W64.of_int (3 * 4)))) {
      leakages <- LeakAddr([(W64.to_uint ((W64.of_int 8) * i))]) :: leakages;
      aux_1 <- (aux `^` (get128_direct (WArray128.init256 (fun i_0 => (gt1).[i_0])) (W64.to_uint ((W64.of_int 8) * i))));
      aux <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_2 <- (i + (W64.of_int 4));
      i <- aux_2;
    leakages <- LeakCond((i \ule (W64.of_int (3 * 4)))) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- VPEXTR_64 aux (W8.of_int 0);
    r <- aux_2;
    return (r);
  }
}.

