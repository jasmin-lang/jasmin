require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.
require import Leakage_models.



theory T.
clone import ALeakageModel as LeakageModel.

module M = {
  var leakages : leakages_t
  
  proc base64_Char2Val_jazz (c:W8.t, base64Decode:W64.t) : W8.t = {
    var aux: W8.t;
    var aux_0: W64.t;
    
    var v:W8.t;
    var mask:W8.t;
    var temp_8:W8.t;
    var temp_64:W64.t;
    
    aux <- (c - (W8.of_int 43));
    c <- aux;
    aux <- (W8.of_int 63);
    mask <- aux;
    aux <- (mask - c);
    mask <- aux;
    aux <- (mask `>>` (W8.of_int 7));
    mask <- aux;
    aux <- (mask - (W8.of_int 1));
    mask <- aux;
    aux <- c;
    temp_8 <- aux;
    aux <- (temp_8 `&` (W8.of_int 63));
    temp_8 <- aux;
    aux_0 <- (zeroextu64 temp_8);
    temp_64 <- aux_0;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (base64Decode + temp_64)))]) :: leakages;
    aux <- (loadW8 Glob.mem (W64.to_uint (base64Decode + temp_64)));
    v <- aux;
    aux <- (v `&` mask);
    v <- aux;
    aux <- (c `&` (W8.of_int 15));
    temp_8 <- aux;
    aux <- (temp_8 `|` (W8.of_int 64));
    temp_8 <- aux;
    aux_0 <- (zeroextu64 temp_8);
    temp_64 <- aux_0;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (base64Decode + temp_64)))]) :: leakages;
    aux <- (loadW8 Glob.mem (W64.to_uint (base64Decode + temp_64)));
    temp_8 <- aux;
    aux <- (invw mask);
    mask <- aux;
    aux <- (temp_8 `&` mask);
    temp_8 <- aux;
    aux <- (v `|` temp_8);
    v <- aux;
    return (v);
  }
}.
end T.

