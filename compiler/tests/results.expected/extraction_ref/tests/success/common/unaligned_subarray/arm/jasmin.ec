require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.


require import Array1 Array2 Array4.
require import WArray4 WArray8.



module M = {
  proc main () : W32.t = {
    
    var r:W32.t;
    var z:W32.t;
    var s:W32.t Array2.t;
    var p:W32.t Array1.t;
    p <- witness;
    s <- witness;
    z <- (W32.of_int 0);
    s.[0] <- z;
    s.[1] <- z;
    p <- (Array1.init (fun i => get32 (WArray4.init8 (fun i => ((Array4.init (fun i => (get8 (WArray8.init32 (fun i => (s).[i])) (1 + i))))).[i])) i));
    r <- p.[0];
    return (r);
  }
  
  proc load (a:W32.t Array1.t) : W32.t = {
    
    var v:W32.t;
    
    v <- a.[0];
    return (v);
  }
  
  proc deref_unaligned () : W32.t = {
    var aux: int;
    
    var r:W32.t;
    var z:W32.t;
    var i:int;
    var s:W32.t Array2.t;
    s <- witness;
    z <- (W32.of_int 0);
    i <- 0;
    while (i < 8) {
      s <- Array2.init (WArray8.get32 (WArray8.set8 (WArray8.init32 (fun i_0 => (s).[i_0])) i ((truncateu8 z))));
      i <- i + 1;
    }
    r <@ load ((Array1.init (fun i_0 => (get32_direct (WArray8.init32 (fun i_0 => (s).[i_0])) (1 + i_0)))));
    return (r);
  }
  
  proc deref_aligned () : W32.t = {
    var aux: int;
    
    var r:W32.t;
    var z:W32.t;
    var i:int;
    var s:W32.t Array1.t;
    s <- witness;
    z <- (W32.of_int 0);
    i <- 0;
    while (i < 4) {
      s <- Array1.init (WArray4.get32 (WArray4.set8 (WArray4.init32 (fun i_0 => (s).[i_0])) i ((truncateu8 z))));
      i <- i + 1;
    }
    r <@ load ((Array1.init (fun i_0 => (get32_direct (WArray4.init32 (fun i_0 => (s).[i_0])) (0 + i_0)))));
    return (r);
  }
}.

