require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1.
require import WArray1.



module type Syscall_t = {
  proc randombytes_1(_:W8.t Array1.t) : W8.t Array1.t
}.

module Syscall : Syscall_t = {
  proc randombytes_1(a:W8.t Array1.t) : W8.t Array1.t = {
    a <$ dmap WArray1.darray (fun a => Array1.init (fun i => WArray1.get8 a i));
    return a;
  }
}.

module M(SC:Syscall_t) = {
  var leakages : leakages_t
  
  proc randombyte () : W8.t = {
    var aux_0: W8.t;
    var aux: W8.t Array1.t;
    
    var r:W8.t;
    var buf:W8.t Array1.t;
    buf <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ SC.randombytes_1 (buf);
    buf <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- buf.[0];
    r <- aux_0;
    return (r);
  }
}.

