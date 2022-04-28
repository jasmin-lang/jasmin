require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel Leakage_models.



theory T.
clone import ALeakageModel as LeakageModel.

module M = {
  var leakages : leakages_t

  proc lzcnt (x:W64.t) : bool * W64.t = {
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux_0: bool;
    var aux: bool;
    var aux_4: W64.t;

    var zf:bool;
    var result:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;

    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- LZCNT_64 x;
     _0 <- aux_3;
     _1 <- aux_2;
     _2 <- aux_1;
     _3 <- aux_0;
    zf <- aux;
    result <- aux_4;
    return (zf, result);
  }

  proc mod_TV (a:W64.t, b:W64.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;

    var result:W64.t;
    var flag:W64.t;
    var one:W64.t;
    var zero:W64.t;
    var lzbz:bool;
    var lzb:W64.t;
    var lzaz:bool;
    var lzb_m1:W64.t;
    var b_lzb_m1:W64.t;
    var dividend:W64.t;
    var b_lzb:W64.t;
    var cf:bool;
    var temp2:W64.t;
    var modulo:W64.t;
    var  _0:W64.t;

    aux <- (W64.of_int 4660);
    flag <- aux;
    aux <- (W64.of_int 1);
    one <- aux;
    aux <- (W64.of_int 0);
    zero <- aux;
    (aux_0, aux) <@ lzcnt (b);
    lzbz <- aux_0;
    lzb <- aux;
    aux <- (lzbz ? zero : flag);
    flag <- aux;
    (aux_0, aux) <@ lzcnt (a);
    lzaz <- aux_0;
     _0 <- aux;
    aux <- (lzaz ? one : flag);
    flag <- aux;
    aux <- LEA_64 (lzb - (W64.of_int 1));
    lzb_m1 <- aux;
    aux <- b;
    b_lzb_m1 <- aux;
    aux <- (b_lzb_m1 `<<` (truncateu8 lzb_m1));
    b_lzb_m1 <- aux;
    aux <- LEA_64 (b_lzb_m1 + a);
    dividend <- aux;
    aux <- (b_lzb_m1 `<<` (W8.of_int 1));
    b_lzb <- aux;
    (aux_0, aux) <- adc_64 b_lzb a false;
    cf <- aux_0;
    temp2 <- aux;
    aux <- ((! cf) ? temp2 : dividend);
    dividend <- aux;
    aux <- ((flag = (W64.of_int 1)) ? a : dividend);
    dividend <- aux;
    aux <- (W64.of_int 18446744073709551615);
    temp2 <- aux;
    aux <- ((flag = (W64.of_int 0)) ? temp2 : dividend);
    dividend <- aux;
    leakages <- LeakAddr(LeakageModel.leak_div_64 (dividend) (b)) :: leakages;
    aux <- (dividend \umod b);
    modulo <- aux;
    aux <- modulo;
    result <- aux;
    aux <- ((flag = (W64.of_int 0)) ? a : result);
    result <- aux;
    return (result);
  }
}.
end T.
