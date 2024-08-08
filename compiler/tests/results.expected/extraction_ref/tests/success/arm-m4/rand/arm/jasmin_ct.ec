require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.
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
  var leakages : leakages_t
  
  proc random32 () : W32.t = {
    var aux_1: int;
    var aux_0: W32.t;
    var aux: W8.t Array4.t;
    
    var r:W32.t;
    var s:W8.t Array4.t;
    var p:W8.t Array4.t;
    var i:int;
    var x:W32.t;
    p <- witness;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- s;
    p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ SC.randombytes_4 (p);
    s <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- (zeroextu32 s.[0]);
    r <- aux_0;
    leakages <- LeakFor(1,4) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 4) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- (zeroextu32 s.[i]);
      x <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (r `|` (x `<<` (W8.of_int (8 * i))));
      r <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
}.

