require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

from Jasmin require import JLeakage.
require import Array1 Array9 Array14 Array25.
require import WArray1 WArray9 WArray14 WArray25.

abbrev nested = Array25.of_list witness [W8.of_int (-30); W8.of_int (-128); W8.of_int (-100); W8.of_int 34; W8.of_int 73; W8.of_int 115; W8.of_int 32; W8.of_int 39; W8.of_int 116; W8.of_int 104; W8.of_int 105; W8.of_int 115; W8.of_int 39; W8.of_int 32; W8.of_int 113; W8.of_int 117; W8.of_int 111; W8.of_int 116; W8.of_int 101; W8.of_int 100; W8.of_int 63; W8.of_int 34; W8.of_int (-30); W8.of_int (-128); W8.of_int (-99)].


abbrev escaped = Array1.of_list witness [W8.of_int 92].


abbrev hw = Array9.of_list witness [W8.of_int (-23); W8.of_int (-93); W8.of_int (-97); W8.of_int (-23); W8.of_int (-93); W8.of_int (-67); W8.of_int (-26); W8.of_int (-100); W8.of_int (-86)].


abbrev nl = Array1.of_list witness [W8.of_int 10].


abbrev x = Array14.of_list witness [W8.of_int 34; W8.of_int 59; W8.of_int 10; W8.of_int 117; W8.of_int 56; W8.of_int 91; W8.of_int 50; W8.of_int 93; W8.of_int 32; W8.of_int 121; W8.of_int 32; W8.of_int 61; W8.of_int 32; W8.of_int 34].


abbrev q = Array1.of_list witness [W8.of_int 34].


abbrev z = Array1.of_list witness [W8.of_int 0].


module M = {
  var leakages : leakages_t
  
  
}.

