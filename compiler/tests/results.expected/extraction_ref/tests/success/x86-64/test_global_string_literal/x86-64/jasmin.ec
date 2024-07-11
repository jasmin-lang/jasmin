require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array10.
require import WArray10.

abbrev test = Array10.of_list witness [W8.of_int 84; W8.of_int 101; W8.of_int 115; W8.of_int 116; W8.of_int 115; W8.of_int 116; W8.of_int 114; W8.of_int 105; W8.of_int 110; W8.of_int 103].


module M = {
  proc main () : W8.t = {
    
    var res_0:W8.t;
    var tmp:W8.t;
    
    res_0 <- (W8.of_int 84);
    tmp <- test.[0];
    res_0 <- (res_0 `^` tmp);
    return (res_0);
  }
}.

