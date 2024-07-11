require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array4.
require import WArray128.

abbrev glob_t = Array4.of_list witness [W256.of_int 0; W256.of_int 1; W256.of_int 2; W256.of_int 3].


module M = {
  proc sum (x:W64.t) : W64.t = {
    
    var r:W64.t;
    var gt1:W256.t Array4.t;
    var aux:W256.t;
    var i:W64.t;
    gt1 <- witness;
    gt1 <- glob_t;
    aux <- glob_t.[0];
    i <- (W64.of_int 32);
    
    while ((i \ule (W64.of_int (3 * 32)))) {
      aux <- (aux `^` (get256_direct (WArray128.init256 (fun i_0 => (gt1).[i_0])) (W64.to_uint i)));
      i <- (i + (W64.of_int 32));
    }
    i <- (W64.of_int 4);
    
    while ((i \ule (W64.of_int (3 * 4)))) {
      aux <- (aux `^` (get256_direct (WArray128.init256 (fun i_0 => (gt1).[i_0])) (W64.to_uint ((W64.of_int 8) * i))));
      i <- (i + (W64.of_int 4));
    }
    r <- VPEXTR_64 (truncateu128 aux) (W8.of_int 0);
    return (r);
  }
  
  proc sum1 (x:W64.t) : W64.t = {
    
    var r:W64.t;
    var gt1:W256.t Array4.t;
    var aux:W128.t;
    var i:W64.t;
    gt1 <- witness;
    gt1 <- glob_t;
    aux <- (get128 (WArray128.init256 (fun i_0 => (glob_t).[i_0])) 0);
    i <- (W64.of_int 16);
    
    while ((i \ule (W64.of_int (7 * 16)))) {
      aux <- (aux `^` (get128_direct (WArray128.init256 (fun i_0 => (gt1).[i_0])) (W64.to_uint i)));
      i <- (i + (W64.of_int 16));
    }
    i <- (W64.of_int 8);
    
    while ((i \ule (W64.of_int (3 * 4)))) {
      aux <- (aux `^` (get128_direct (WArray128.init256 (fun i_0 => (gt1).[i_0])) (W64.to_uint ((W64.of_int 8) * i))));
      i <- (i + (W64.of_int 4));
    }
    r <- VPEXTR_64 aux (W8.of_int 0);
    return (r);
  }
}.

