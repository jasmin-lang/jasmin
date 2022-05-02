require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.



theory T.
clone import ALeakageModel as LeakageModel.

module M = {
  var leakages : leakages_t
  
  proc verify_hmac_jazz (pmac:W64.t, out:W64.t, len:W64.t, pad:W32.t,
                         ret:W32.t, maxpad:W64.t) : W32.t = {
    var aux_1: W8.t;
    var aux_0: W32.t;
    var aux: W64.t;
    
    var p:W64.t;
    var off:W64.t;
    var res_0:W32.t;
    var i:W64.t;
    var j:W64.t;
    var c:W8.t;
    var cmask:W64.t;
    var temp:W32.t;
    var temp_64:W64.t;
    var temp_8:W8.t;
    var temp2:W32.t;
    
    aux <- out;
    p <- aux;
    aux <- (p + len);
    p <- aux;
    aux <- (p - (W64.of_int 1));
    p <- aux;
    aux <- (p - maxpad);
    p <- aux;
    aux <- (p - (W64.of_int 20));
    p <- aux;
    aux <- out;
    off <- aux;
    aux <- (off - p);
    off <- aux;
    aux_0 <- (W32.of_int 0);
    res_0 <- aux_0;
    aux <- (W64.of_int 0);
    i <- aux;
    aux <- (W64.of_int 0);
    j <- aux;
    aux <- (maxpad + (W64.of_int 20));
    maxpad <- aux;
    
    leakages <- LeakCond((j \ult maxpad)) :: LeakAddr([]) :: leakages;
    
    while ((j \ult maxpad)) {
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (p + j)))]) :: leakages;
      aux_1 <- (loadW8 Glob.mem (W64.to_uint (p + j)));
      c <- aux_1;
      aux <- j;
      cmask <- aux;
      aux <- (cmask - off);
      cmask <- aux;
      aux <- (cmask - (W64.of_int 20));
      cmask <- aux;
      aux <- (cmask `|>>` (W8.of_int 63));
      cmask <- aux;
      aux_0 <- (zeroextu32 c);
      temp <- aux_0;
      aux_0 <- (temp `^` pad);
      temp <- aux_0;
      aux <- (invw cmask);
      cmask <- aux;
      aux_0 <- (temp `&` (truncateu32 cmask));
      temp <- aux_0;
      aux_0 <- (res_0 `|` temp);
      res_0 <- aux_0;
      aux <- (invw cmask);
      cmask <- aux;
      aux <- off;
      temp_64 <- aux;
      aux <- (temp_64 - (W64.of_int 1));
      temp_64 <- aux;
      aux <- (temp_64 - j);
      temp_64 <- aux;
      aux <- (temp_64 `|>>` (W8.of_int 63));
      temp_64 <- aux;
      aux <- (cmask `&` temp_64);
      cmask <- aux;
      aux_0 <- (zeroextu32 c);
      temp <- aux_0;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (pmac + i)))]) :: leakages;
      aux_1 <- (loadW8 Glob.mem (W64.to_uint (pmac + i)));
      temp_8 <- aux_1;
      aux_0 <- (zeroextu32 temp_8);
      temp2 <- aux_0;
      aux_0 <- (temp `^` temp2);
      temp <- aux_0;
      aux_0 <- (temp `&` (truncateu32 cmask));
      temp <- aux_0;
      aux_0 <- (res_0 `|` temp);
      res_0 <- aux_0;
      aux <- cmask;
      temp_64 <- aux;
      aux <- (temp_64 `&` (W64.of_int 1));
      temp_64 <- aux;
      aux <- (i + temp_64);
      i <- aux;
      aux <- (j + (W64.of_int 1));
      j <- aux;
    leakages <- LeakCond((j \ult maxpad)) :: LeakAddr([]) :: leakages;
    
    }
    aux_0 <- (W32.of_int 0);
    temp <- aux_0;
    aux_0 <- (temp - res_0);
    temp <- aux_0;
    aux_0 <- (temp `|>>` (W8.of_int 31));
    temp <- aux_0;
    aux_0 <- temp;
    res_0 <- aux_0;
    aux_0 <- (W32.of_int 0);
    temp <- aux_0;
    aux_0 <- (temp - res_0);
    temp <- aux_0;
    aux_0 <- temp;
    res_0 <- aux_0;
    aux_0 <- (ret `&` (invw res_0));
    ret <- aux_0;
    return (ret);
  }
}.
end T.

