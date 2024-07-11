require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1 Array2 Array4.
require import WArray4 WArray8.



module M = {
  var leakages : leakages_t
  
  proc main () : W32.t = {
    var aux: W32.t;
    var aux_1: W8.t Array4.t;
    var aux_0: W32.t Array1.t;
    
    var r:W32.t;
    var z:W32.t;
    var s:W32.t Array2.t;
    var p:W32.t Array1.t;
    p <- witness;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    z <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- z;
    leakages <- LeakAddr([0]) :: leakages;
    s.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- z;
    leakages <- LeakAddr([1]) :: leakages;
    s.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux_1 <- (Array4.init (fun i => (get8 (WArray8.init32 (fun i => (s).[i])) (1 + i))));
    p <- (Array1.init (fun i => get32 (WArray4.init8 (fun i => (aux_1).[i])) i));
    leakages <- LeakAddr([0]) :: leakages;
    aux <- p.[0];
    r <- aux;
    return (r);
  }
  
  proc load (a:W32.t Array1.t) : W32.t = {
    var aux: W32.t;
    
    var v:W32.t;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    v <- aux;
    return (v);
  }
  
  proc deref_unaligned () : W32.t = {
    var aux_0: int;
    var aux_1: W8.t;
    var aux: W32.t;
    
    var r:W32.t;
    var z:W32.t;
    var i:int;
    var s:W32.t Array2.t;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    z <- aux;
    leakages <- LeakFor(0,8) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 8) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- z;
      leakages <- LeakAddr([i]) :: leakages;
      s <- Array2.init (WArray8.get32 (WArray8.set8 (WArray8.init32 (fun i_0 => (s).[i_0])) i ((truncateu8 aux))));
      i <- i + 1;
    }
    leakages <- LeakAddr([1]) :: leakages;
    aux <@ load ((Array1.init (fun i_0 => (get32_direct (WArray8.init32 (fun i_0 => (s).[i_0])) (1 + i_0)))));
    r <- aux;
    return (r);
  }
  
  proc deref_aligned () : W32.t = {
    var aux_0: int;
    var aux_1: W8.t;
    var aux: W32.t;
    
    var r:W32.t;
    var z:W32.t;
    var i:int;
    var s:W32.t Array1.t;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    z <- aux;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- z;
      leakages <- LeakAddr([i]) :: leakages;
      s <- Array1.init (WArray4.get32 (WArray4.set8 (WArray4.init32 (fun i_0 => (s).[i_0])) i ((truncateu8 aux))));
      i <- i + 1;
    }
    leakages <- LeakAddr([0]) :: leakages;
    aux <@ load ((Array1.init (fun i_0 => (get32_direct (WArray4.init32 (fun i_0 => (s).[i_0])) (0 + i_0)))));
    r <- aux;
    return (r);
  }
}.

