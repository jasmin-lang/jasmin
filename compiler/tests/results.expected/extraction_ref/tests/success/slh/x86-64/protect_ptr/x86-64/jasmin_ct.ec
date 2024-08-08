require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array2 Array8 Array16.
require import WArray8 WArray16.



module M = {
  var leakages : leakages_t
  
  proc foo () : W64.t * W64.t = {
    var aux: W64.t;
    var aux_1: W8.t Array16.t;
    var aux_0: W64.t Array2.t;
    
    var x:W64.t;
    var y:W64.t;
    var s:W64.t Array2.t;
    var msf:W64.t;
    var p:W64.t Array2.t;
    p <- witness;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    s.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    leakages <- LeakAddr([1]) :: leakages;
    s.[1] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- init_msf ;
    msf <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- s;
    p <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- protect_ptr (Array16.init (fun i => get8 (WArray16.init64 (fun i => (p).[i])) i)) msf;
    p <- (Array2.init (fun i => get64 (WArray16.init8 (fun i => (aux_1).[i])) i));
    leakages <- LeakAddr([0]) :: leakages;
    aux <- p.[0];
    x <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- p.[1];
    y <- aux;
    return (x, y);
  }
  
  proc foo2 () : W64.t = {
    var aux: W32.t;
    var aux_0: W64.t;
    var aux_2: W8.t Array8.t;
    var aux_1: W32.t Array2.t;
    
    var x:W64.t;
    var s:W32.t Array2.t;
    var msf:W64.t;
    var p:W32.t Array2.t;
    p <- witness;
    s <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    s.[0] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 1);
    leakages <- LeakAddr([1]) :: leakages;
    s.[1] <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- init_msf ;
    msf <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- s;
    p <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_2 <- protect_ptr (Array8.init (fun i => get8 (WArray8.init32 (fun i => (p).[i])) i)) msf;
    p <- (Array2.init (fun i => get32 (WArray8.init8 (fun i => (aux_2).[i])) i));
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- (get64 (WArray8.init32 (fun i => (p).[i])) 0);
    x <- aux_0;
    return (x);
  }
}.

