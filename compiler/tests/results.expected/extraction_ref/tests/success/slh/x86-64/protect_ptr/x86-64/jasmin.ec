require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2 Array8 Array16.
require import WArray8 WArray16.



module M = {
  proc foo () : W64.t * W64.t = {
    
    var x:W64.t;
    var y:W64.t;
    var s:W64.t Array2.t;
    var msf:W64.t;
    var p:W64.t Array2.t;
    p <- witness;
    s <- witness;
    s.[0] <- (W64.of_int 0);
    s.[1] <- (W64.of_int 1);
    msf <- init_msf ;
    p <- s;
    p <- (Array2.init (fun i => get64 (WArray16.init8 (fun i => (protect_ptr (Array16.init (fun i => get8 (WArray16.init64 (fun i => (p).[i])) i)) msf).[i])) i));
    x <- p.[0];
    y <- p.[1];
    return (x, y);
  }
  
  proc foo2 () : W64.t = {
    
    var x:W64.t;
    var s:W32.t Array2.t;
    var msf:W64.t;
    var p:W32.t Array2.t;
    p <- witness;
    s <- witness;
    s.[0] <- (W32.of_int 0);
    s.[1] <- (W32.of_int 1);
    msf <- init_msf ;
    p <- s;
    p <- (Array2.init (fun i => get32 (WArray8.init8 (fun i => (protect_ptr (Array8.init (fun i => get8 (WArray8.init32 (fun i => (p).[i])) i)) msf).[i])) i));
    x <- (get64 (WArray8.init32 (fun i => (p).[i])) 0);
    return (x);
  }
}.

