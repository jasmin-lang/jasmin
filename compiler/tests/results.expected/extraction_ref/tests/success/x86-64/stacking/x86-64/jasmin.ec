require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1 Array3.
require import WArray1 WArray48.



module M = {
  proc test (x:W64.t) : W8.t = {
    
    var b:W8.t;
    var a:W8.t Array1.t;
    var r:W128.t;
    var s:W128.t;
    a <- witness;
    a.[0] <- (truncateu8 x);
    r <- (loadW128 Glob.mem (W64.to_uint (x + (W64.of_int 0))));
    s <- r;
    r <- s;
    Glob.mem <- storeW128 Glob.mem (W64.to_uint (x + (W64.of_int 0))) (r);
    b <- a.[0];
    return (b);
  }
  
  proc test1 (x:W64.t) : unit = {
    var aux: int;
    
    var lll:W128.t;
    var a:W128.t Array3.t;
    var ll:W64.t;
    var l:W32.t;
    var i:int;
    var b:W8.t;
    a <- witness;
    lll <- (loadW128 Glob.mem (W64.to_uint (x + (W64.of_int 0))));
    a.[0] <- lll;
    lll <- (loadW128 Glob.mem (W64.to_uint (x + (W64.of_int 16))));
    a.[1] <- lll;
    ll <- (loadW64 Glob.mem (W64.to_uint (x + (W64.of_int 32))));
    a <- Array3.init (WArray48.get128 (WArray48.set64 (WArray48.init128 (fun i_0 => (a).[i_0])) 4 (ll)));
    l <- (loadW32 Glob.mem (W64.to_uint (x + (W64.of_int 40))));
    a <- Array3.init (WArray48.get128 (WArray48.set32 (WArray48.init128 (fun i_0 => (a).[i_0])) 10 (l)));
    l <- (loadW32 Glob.mem (W64.to_uint (x + (W64.of_int 44))));
    a <- Array3.init (WArray48.get128 (WArray48.set32 (WArray48.init128 (fun i_0 => (a).[i_0])) 11 (l)));
    i <- 0;
    while (i < 48) {
      b <- (get8 (WArray48.init128 (fun i_0 => (a).[i_0])) i);
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (x + (W64.of_int i))) (b);
      i <- i + 1;
    }
    return ();
  }
}.

