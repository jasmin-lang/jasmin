require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array4.
require import WArray4.



module type Syscall_t = {
  proc randombytes_4(_:W8.t Array4.t) : W8.t Array4.t
}.

module Syscall : Syscall_t = {
  proc randombytes_4(a:W8.t Array4.t) : W8.t Array4.t = {
    a <$ dmap WArray4.darray (fun a => Array4.init (fun i => WArray4.get8 a i));
    return a;
  }
}.

module M(SC:Syscall_t) = {
  proc random32 () : W32.t = {
    var aux: int;
    
    var r:W32.t;
    var s:W8.t Array4.t;
    var p:W8.t Array4.t;
    var i:int;
    var x:W32.t;
    p <- witness;
    s <- witness;
    p <- s;
    s <@ SC.randombytes_4 (p);
    r <- (zeroextu32 s.[0]);
    i <- 1;
    while (i < 4) {
      x <- (zeroextu32 s.[i]);
      r <- (r `|` (x `<<` (W8.of_int (8 * i))));
      i <- i + 1;
    }
    return (r);
  }
}.

