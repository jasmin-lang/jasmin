require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc __fp_rdcn_low (a:W64.t Array1.t) : W64.t * W64.t Array1.t = {
    
    var result:W64.t;
    
    a.[0] <- (W64.of_int 0);
    result <- a.[0];
    return (result, a);
  }
  
  proc fp_exp_low () : W64.t = {
    
    var c:W64.t;
    var k:W64.t;
    var cnr:W64.t Array1.t;
    cnr <- witness;
    k <- (W64.of_int 0);
    
    while ((k \ult (W64.of_int 64))) {
      (c, cnr) <@ __fp_rdcn_low (cnr);
      k <- (k + (W64.of_int 1));
    }
    return (c);
  }
  
  proc aux () : W64.t = {
    
    var k:W64.t;
    var cnr:W64.t Array1.t;
    cnr <- witness;
    (k, cnr) <@ __fp_rdcn_low (cnr);
    return (k);
  }
  
  proc fp_exp_low1 () : W64.t = {
    
    var c:W64.t;
    var k:W64.t;
    
    k <- (W64.of_int 0);
    
    while ((k \ult (W64.of_int 64))) {
      c <@ aux ();
      k <- (k + (W64.of_int 1));
    }
    return (c);
  }
}.

