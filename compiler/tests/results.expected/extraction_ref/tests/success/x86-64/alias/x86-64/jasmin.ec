require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1 Array5 Array10.
require import WArray8 WArray40 WArray80.



module M = {
  proc test (x:W64.t) : W64.t = {
    
    var result:W64.t;
    var bigA:W64.t Array10.t;
    var leftA:W64.t Array5.t;
    var rightA:W64.t Array5.t;
    var bigB:W64.t Array10.t;
    bigA <- witness;
    bigB <- witness;
    leftA <- witness;
    rightA <- witness;
    bigA.[0] <- x;
    leftA <- (Array5.init (fun i => bigA.[0 + i]));
    rightA <- (Array5.init (fun i => bigA.[5 + i]));
    if (((W64.of_int 0) \ult x)) {
      bigB.[0] <- x;
    } else {
      bigB <- Array10.init (fun i => if 0 <= i < 0 + 5 then leftA.[i-0] else bigB.[i]);
    }
    result <- bigB.[0];
    return (result);
  }
  
  proc toto (p:W64.t Array1.t, x:W64.t) : W64.t Array1.t = {
    
    var a:W64.t Array1.t;
    a <- witness;
    a <- p;
    p <- a;
    p.[0] <- x;
    return (p);
  }
}.

