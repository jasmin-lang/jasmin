require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2.
require import WArray16.



module M = {
  proc init () : W64.t Array2.t = {
    var aux: int;
    
    var r:W64.t Array2.t;
    var i:int;
    r <- witness;
    i <- 0;
    while (i < 2) {
      r.[i] <- (W64.of_int i);
      i <- i + 1;
    }
    return (r);
  }
  
  proc add (a:W64.t Array2.t, b:W64.t Array2.t) : W64.t Array2.t = {
    
    var i:W64.t;
    var t:W64.t;
    
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int 2))) {
      t <- a.[(W64.to_uint i)];
      t <- (t + b.[(W64.to_uint i)]);
      a.[(W64.to_uint i)] <- t;
      i <- (i + (W64.of_int 1));
    }
    return (a);
  }
  
  proc store (p:W64.t, x:W64.t Array2.t) : unit = {
    
    var i:W64.t;
    var t:W64.t;
    
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int 2))) {
      t <- x.[(W64.to_uint i)];
      Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + ((W64.of_int 8) * i))) (t);
      i <- (i + (W64.of_int 1));
    }
    return ();
  }
  
  proc test1 (p:W64.t) : unit = {
    
    var a:W64.t Array2.t;
    var ap:W64.t Array2.t;
    var b:W64.t Array2.t;
    var bp:W64.t Array2.t;
    a <- witness;
    ap <- witness;
    b <- witness;
    bp <- witness;
    a <@ init ();
    ap <- a;
    b <@ init ();
    bp <- b;
    ap <@ add (ap, bp);
    store (p, ap);
    store (p, bp);
    return ();
  }
}.

