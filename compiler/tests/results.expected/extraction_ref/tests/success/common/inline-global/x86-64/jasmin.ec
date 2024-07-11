require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array10.
require import WArray10.

abbrev rcon = Array10.of_list witness [W8.of_int 1; W8.of_int 2; W8.of_int 4; W8.of_int 8; W8.of_int 16; W8.of_int 32; W8.of_int 64; W8.of_int (-128); W8.of_int 27; W8.of_int 54].


module M = {
  proc rCON (i:int) : int = {
    
    var c:int;
    
    c <- (W8.to_uint rcon.[(i - 1)]);
    return (c);
  }
  
  proc test (x:W32.t) : W32.t = {
    var aux: int;
    
    var r:W32.t;
    var j:int;
    var v:int;
    
    r <- x;
    j <- 1;
    while (j < 11) {
      v <@ rCON (j);
      r <- (r + (W32.of_int v));
      v <@ rCON ((W8.to_uint ((rcon.[(j %% 10)] \umod (W8.of_int 10)) + (W8.of_int 1))));
      r <- (r + (W32.of_int v));
      j <- j + 1;
    }
    return (r);
  }
}.

