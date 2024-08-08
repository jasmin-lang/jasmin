require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc main (a64:W64.t, b64:W64.t) : W8.t = {
    var aux_6: W8.t;
    var aux_5: W8.t;
    var aux_4: W16.t;
    var aux_3: W16.t;
    var aux_2: W32.t;
    var aux_1: W32.t;
    var aux_0: W64.t;
    var aux: W64.t;
    
    var b8:W8.t;
    var sa64:W64.t;
    var a32:W32.t;
    var b32:W32.t;
    var a16:W16.t;
    var b16:W16.t;
    var a8:W8.t;
    var sa32:W32.t;
    var sa16:W16.t;
    var sa8:W8.t;
    var t:W64.t Array1.t;
    var  _0:W32.t;
    var  _1:W16.t;
    var  _2:W8.t;
    t <- witness;
    sa64 <- a64;
    (a64, b64) <- XCHG_64 a64 b64;
    a32 <- (truncateu32 a64);
    b32 <- (truncateu32 b64);
    (a32, b32) <- XCHG_32 a32 b32;
    a16 <- (truncateu16 a32);
    b16 <- (truncateu16 b32);
    (a16, b16) <- XCHG_16 a16 b16;
    a8 <- (truncateu8 a16);
    b8 <- (truncateu8 b16);
    (a8, b8) <- XCHG_8 a8 b8;
    a64 <- sa64;
    (a64, sa64) <- XCHG_64 a64 sa64;
    (sa64, a64) <- XCHG_64 sa64 a64;
    a32 <- (truncateu32 a64);
    sa32 <- a32;
    (a32, sa32) <- XCHG_32 a32 sa32;
    (sa32,  _0) <- XCHG_32 sa32 a32;
    a32 <- sa32;
    sa16 <- (truncateu16 a32);
    (a16, sa16) <- XCHG_16 (truncateu16 a32) sa16;
    (sa16,  _1) <- XCHG_16 sa16 a16;
    a16 <- sa16;
    sa8 <- (truncateu8 a16);
    (a8, sa8) <- XCHG_8 (truncateu8 a16) sa8;
    (sa8,  _2) <- XCHG_8 sa8 a8;
    b8 <- (b8 `^` sa8);
    a64 <- sa64;
    t.[0] <- a64;
    (aux_0, aux) <- XCHG_64 a64 t.[0];
    a64 <- aux_0;
    t.[0] <- aux;
    (aux_0, aux) <- XCHG_64 t.[0] a64;
    t.[0] <- aux_0;
    a64 <- aux;
    a32 <- (truncateu32 a64);
    (aux_2, aux_1) <- XCHG_32 a32 (get32 (WArray8.init64 (fun i => (t).[i])) 0);
    a32 <- aux_2;
    t <- Array1.init (WArray8.get64 (WArray8.set32 (WArray8.init64 (fun i => (t).[i])) 0 (aux_1)));
    (aux_2, aux_1) <- XCHG_32 (get32 (WArray8.init64 (fun i => (t).[i])) 0) a32;
    t <- Array1.init (WArray8.get64 (WArray8.set32 (WArray8.init64 (fun i => (t).[i])) 0 (aux_2)));
    a32 <- aux_1;
    a16 <- (truncateu16 a32);
    (aux_4, aux_3) <- XCHG_16 a16 (get16 (WArray8.init64 (fun i => (t).[i])) 0);
    a16 <- aux_4;
    t <- Array1.init (WArray8.get64 (WArray8.set16 (WArray8.init64 (fun i => (t).[i])) 0 (aux_3)));
    (aux_4, aux_3) <- XCHG_16 (get16 (WArray8.init64 (fun i => (t).[i])) 0) a16;
    t <- Array1.init (WArray8.get64 (WArray8.set16 (WArray8.init64 (fun i => (t).[i])) 0 (aux_4)));
    a16 <- aux_3;
    a8 <- (truncateu8 a16);
    (aux_6, aux_5) <- XCHG_8 a8 (get8 (WArray8.init64 (fun i => (t).[i])) 0);
    a8 <- aux_6;
    t <- Array1.init (WArray8.get64 (WArray8.set8 (WArray8.init64 (fun i => (t).[i])) 0 (aux_5)));
    (aux_6, aux_5) <- XCHG_8 (get8 (WArray8.init64 (fun i => (t).[i])) 0) a8;
    t <- Array1.init (WArray8.get64 (WArray8.set8 (WArray8.init64 (fun i => (t).[i])) 0 (aux_6)));
    a8 <- aux_5;
    b8 <- (b8 `^` a8);
    return (b8);
  }
}.

