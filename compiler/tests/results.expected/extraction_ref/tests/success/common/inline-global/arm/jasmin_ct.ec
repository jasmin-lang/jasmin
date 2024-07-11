require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_m4.
import SLH32.

from Jasmin require import JLeakage.
require import Array10.
require import WArray10.

abbrev rcon = Array10.of_list witness [W8.of_int 1; W8.of_int 2; W8.of_int 4; W8.of_int 8; W8.of_int 16; W8.of_int 32; W8.of_int 64; W8.of_int (-128); W8.of_int 27; W8.of_int 54].


module M = {
  var leakages : leakages_t
  
  proc rCON (i:int) : int = {
    var aux: int;
    
    var c:int;
    
    leakages <- LeakAddr([(i - 1)]) :: leakages;
    aux <- (W8.to_uint rcon.[(i - 1)]);
    c <- aux;
    return (c);
  }
  
  proc test (x:W32.t) : W32.t = {
    var aux_0: int;
    var aux: W32.t;
    
    var r:W32.t;
    var j:int;
    var v:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    r <- aux;
    leakages <- LeakFor(1,11) :: LeakAddr([]) :: leakages;
    j <- 1;
    while (j < 11) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ rCON (j);
      v <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (r + (W32.of_int v));
      r <- aux;
      leakages <- LeakAddr([(j %% 10)]) :: leakages;
      aux_0 <@ rCON ((W8.to_uint ((rcon.[(j %% 10)] \umod (W8.of_int 10)) + (W8.of_int 1))));
      v <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (r + (W32.of_int v));
      r <- aux;
      j <- j + 1;
    }
    return (r);
  }
}.

