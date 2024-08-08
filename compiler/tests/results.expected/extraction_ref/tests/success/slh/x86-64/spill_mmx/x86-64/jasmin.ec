require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.





module M = {
  proc main (x:W64.t) : W64.t = {
    
    var ms:W64.t;
    var _ms:W64.t;
    
    ms <- init_msf ;
    _ms <- mov_msf ms;
    ms <- mov_msf _ms;
    x <- protect_64 x ms;
    x <- x;
    return (x);
  }
}.

