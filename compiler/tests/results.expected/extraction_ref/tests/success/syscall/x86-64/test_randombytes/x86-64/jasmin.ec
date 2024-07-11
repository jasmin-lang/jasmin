require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1 Array2 Array8 Array12.
require import WArray8 WArray12 WArray16.



module type Syscall_t = {
  proc randombytes_8(_:W8.t Array8.t) : W8.t Array8.t
  proc randombytes_12(_:W8.t Array12.t) : W8.t Array12.t
}.

module Syscall : Syscall_t = {
  proc randombytes_8(a:W8.t Array8.t) : W8.t Array8.t = {
    a <$ dmap WArray8.darray (fun a => Array8.init (fun i => WArray8.get8 a i));
    return a;
  }
  
  proc randombytes_12(a:W8.t Array12.t) : W8.t Array12.t = {
    a <$ dmap WArray12.darray (fun a => Array12.init (fun i => WArray12.get8 a i));
    return a;
  }
}.

module M(SC:Syscall_t) = {
  proc foo1 () : W64.t = {
    var aux: W8.t Array8.t;
    
    var res_0:W64.t;
    var r:W64.t Array1.t;
    var p:W64.t Array1.t;
    p <- witness;
    r <- witness;
    p <- r;
    aux <@ SC.randombytes_8 ((Array8.init (fun i => get8 (WArray8.init64 (fun i => (p).[i])) i)));
    p <- (Array1.init (fun i => get64 (WArray8.init8 (fun i => (aux).[i])) i));
    r <- p;
    res_0 <- r.[0];
    return (res_0);
  }
  
  proc foo2 () : W64.t = {
    
    var res_0:W64.t;
    var r:W8.t Array8.t;
    var p:W8.t Array8.t;
    p <- witness;
    r <- witness;
    p <- r;
    p <@ SC.randombytes_8 (p);
    res_0 <- (get64 (WArray8.init8 (fun i => (p).[i])) 0);
    return (res_0);
  }
  
  proc foo3 () : W8.t = {
    
    var res_0:W8.t;
    var r:W8.t Array12.t;
    r <- witness;
    r <@ SC.randombytes_12 (r);
    res_0 <- r.[0];
    return (res_0);
  }
  
  proc foo4 () : W64.t = {
    var aux: W8.t Array8.t;
    
    var res_0:W64.t;
    var r:W64.t Array2.t;
    r <- witness;
    aux <@ SC.randombytes_8 ((Array8.init (fun i => get8 (WArray8.init64 (fun i => ((Array1.init (fun i => r.[0 + i]))).[i])) i)));
    r <- Array2.init (fun i => if 0 <= i < 0 + 1 then (Array1.init (fun i => get64 (WArray8.init8 (fun i => (aux).[i])) i)).[i-0] else r.[i]);
    res_0 <- r.[0];
    return (res_0);
  }
}.

