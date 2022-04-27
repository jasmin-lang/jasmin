require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.



theory T.
clone import ALeakageModel as LeakageModel.

module M = {
  var leakages : leakages_t
  
  proc verify_hmac_jazz (pmac:W64.t, out:W64.t, len:W64.t, pad:W32.t,
                         maxpad:W32.t, ret:W32.t) : W32.t = {
    var aux_0: W32.t;
    var aux: W64.t;
    
    var p:W64.t;
    var temp_64:W64.t;
    var off:W64.t;
    var i:W64.t;
    var j:W64.t;
    var c:W32.t;
    var cmask:W32.t;
    var temp:W32.t;
    var res_0:W32.t;
    
    aux <- out;
    p <- aux;
    aux <- (p + len);
    p <- aux;
    aux <- (p - (W64.of_int 1));
    p <- aux;
    aux <- (zeroextu64 maxpad);
    temp_64 <- aux;
    aux <- (p - temp_64);
    p <- aux;
    aux <- (p - (W64.of_int 20));
    p <- aux;
    aux <- out;
    off <- aux;
    aux <- (off - p);
    off <- aux;
    aux <- (W64.of_int 0);
    i <- aux;
    aux <- (W64.of_int 0);
    j <- aux;
    aux_0 <- (maxpad + (W32.of_int 20));
    maxpad <- aux_0;
    
    leakages <- LeakCond(((truncateu32 j) \ult maxpad)) :: LeakAddr([]) :: leakages;
    
    while (((truncateu32 j) \ult maxpad)) {
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (p + j)))]) :: leakages;
      aux_0 <- (loadW32 Glob.mem (W64.to_uint (p + j)));
      c <- aux_0;
      aux <- j;
      cmask <- (truncateu32 aux);
      aux_0 <- (cmask - (truncateu32 off));
      cmask <- aux_0;
      aux_0 <- (cmask - (W32.of_int 20));
      cmask <- aux_0;
      aux_0 <- (cmask `>>` (W8.of_int 31));
      cmask <- aux_0;
      aux_0 <- c;
      temp <- aux_0;
      aux_0 <- (temp `^` pad);
      temp <- aux_0;
      aux_0 <- (invw cmask);
      cmask <- aux_0;
      aux_0 <- (temp `&` cmask);
      temp <- aux_0;
      aux_0 <- (res_0 `|` temp);
      res_0 <- aux_0;
      aux_0 <- (invw cmask);
      cmask <- aux_0;
      aux <- off;
      temp <- (truncateu32 aux);
      aux_0 <- (temp - (W32.of_int 1));
      temp <- aux_0;
      aux_0 <- (temp - (truncateu32 j));
      temp <- aux_0;
      aux_0 <- (temp `>>` (W8.of_int 31));
      temp <- aux_0;
      aux_0 <- c;
      temp <- aux_0;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (pmac + i)))]) :: leakages;
      aux_0 <- (temp `^` (loadW32 Glob.mem (W64.to_uint (pmac + i))));
      temp <- aux_0;
      aux_0 <- (temp `&` cmask);
      temp <- aux_0;
      aux_0 <- (res_0 `|` temp);
      res_0 <- aux_0;
      aux <- (i + (W64.of_int 1));
      i <- aux;
      aux <- (zeroextu64 cmask);
      temp_64 <- aux;
      aux <- (i `&` temp_64);
      i <- aux;
      aux <- (j + (W64.of_int 1));
      j <- aux;
    leakages <- LeakCond(((truncateu32 j) \ult maxpad)) :: LeakAddr([]) :: leakages;
    
    }
    aux_0 <- (W32.of_int 0);
    temp <- aux_0;
    aux_0 <- (temp - res_0);
    temp <- aux_0;
    aux_0 <- (temp `>>` (W8.of_int 31));
    temp <- aux_0;
    aux_0 <- temp;
    res_0 <- aux_0;
    aux_0 <- (W32.of_int 0);
    temp <- aux_0;
    aux_0 <- (temp - res_0);
    temp <- aux_0;
    aux_0 <- temp;
    res_0 <- aux_0;
    aux_0 <- (invw res_0);
    temp <- aux_0;
    aux_0 <- (ret `&` (invw res_0));
    ret <- aux_0;
    return (ret);
  }
}.
end T.

