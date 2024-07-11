require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


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
  proc randombyte () : W8.t = {
    
    var r:W8.t;
    var buf:W8.t Array1.t;
    buf <- witness;
    buf <@ SC.randombytes_1 (buf);
    r <- buf.[0];
    return (r);
  }
}.

