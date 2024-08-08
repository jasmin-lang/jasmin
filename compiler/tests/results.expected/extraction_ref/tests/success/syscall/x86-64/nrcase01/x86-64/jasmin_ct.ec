require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array8.
require import WArray8.



module type Syscall_t = {
  proc randombytes_8(_:W8.t Array8.t) : W8.t Array8.t
}.

module Syscall : Syscall_t = {
  proc randombytes_8(a:W8.t Array8.t) : W8.t Array8.t = {
    a <$ dmap WArray8.darray (fun a => Array8.init (fun i => WArray8.get8 a i));
    return a;
  }
}.

module M(SC:Syscall_t) = {
  var leakages : leakages_t
  
  proc test2 (skp:W64.t) : unit = {
    var aux_1: int;
    var aux: W64.t;
    var aux_0: W8.t Array8.t;
    
    var rb:W8.t Array8.t;
    var i:int;
    var t64:W64.t;
    rb <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- skp;
    skp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ SC.randombytes_8 (rb);
    rb <- aux_0;
    leakages <- LeakFor(0,((8 * 1) %/ 8)) :: LeakAddr([]) :: leakages;
    aux_1 <- ((8 * 1) %/ 8);
    i <- 0;
    while (i < aux_1) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- (get64 (WArray8.init8 (fun i_0 => (rb).[i_0])) i);
      t64 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- t64;
      leakages <- LeakAddr([(W64.to_uint (skp + (W64.of_int 0)))]) :: leakages;
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (skp + (W64.of_int 0))) (aux);
      leakages <- LeakAddr([]) :: leakages;
      aux <- (skp + (W64.of_int 8));
      skp <- aux;
      i <- i + 1;
    }
    return ();
  }
}.

