require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


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
  proc test2 (skp:W64.t) : unit = {
    var aux: int;
    
    var rb:W8.t Array8.t;
    var i:int;
    var t64:W64.t;
    rb <- witness;
    skp <- skp;
    rb <@ SC.randombytes_8 (rb);
    aux <- ((8 * 1) %/ 8);
    i <- 0;
    while (i < aux) {
      t64 <- (get64 (WArray8.init8 (fun i_0 => (rb).[i_0])) i);
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (skp + (W64.of_int 0))) (t64);
      skp <- (skp + (W64.of_int 8));
      i <- i + 1;
    }
    return ();
  }
}.

