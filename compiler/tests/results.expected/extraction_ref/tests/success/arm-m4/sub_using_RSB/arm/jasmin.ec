require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.



abbrev mINUS_Q = W32.of_int (-8380417).


module M = {
  proc __montgomery_reduce_8380417 (a:W32.t) : W32.t = {
    
    
    
    a <- ((a `<<` (W8.of_int 3)) - a);
    a <- ((W32.of_int 2) - a);
    return (a);
  }
}.

