require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array1.
require import WArray8.



module M = {
  proc f (x:W64.t Array1.t) : W64.t Array1.t = {
    
    
    
    
    return (x);
  }
  
  proc g () : unit = {
    
    var b:W64.t Array1.t;
    var a:W64.t Array1.t;
    a <- witness;
    b <- witness;
    a <- copy_64 b;
    return ();
  }
}.

