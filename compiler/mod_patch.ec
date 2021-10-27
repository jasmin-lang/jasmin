require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.




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
    
    leakages <- LeakAddr([]) :: leakages;
    (aux_3, aux_2, aux_1, aux_0, aux, aux_4) <- LZCNT_64 x;
     _0 <- aux_3;
     _1 <- aux_2;
     _2 <- aux_1;
     _3 <- aux_0;
    zf <- aux;
    result <- aux_4;
    return (zf, result);
  }
  
  proc verify_mod_const (a:W64.t, b:W64.t) : W64.t = {
    var aux_0: bool;
    var aux: W64.t;
    
    var result:W64.t;
    var flag:W64.t;
    var one:W64.t;
    var zero:W64.t;
    var lzbz:bool;
    var lzb:W64.t;
    var lzaz:bool;
    var b_lzb:W64.t;
    var temp2:W64.t;
    var temp:W64.t;
    var b_lzb_1:W64.t;
    var temp3:W64.t;
    var res_temp:W64.t;
    var  _0:W64.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 4660);
    flag <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 1);
    one <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    zero <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ lzcnt (b);
    lzbz <- aux_0;
    lzb <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (lzbz ? zero : flag);
    flag <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ lzcnt (a);
    lzaz <- aux_0;
     _0 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (lzaz ? one : flag);
    flag <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    b_lzb <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (b_lzb `<<` (truncateu8 lzb));
    b_lzb <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- LEA_64 (b_lzb + a);
    temp2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- temp2;
    temp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (lzb - (W64.of_int 1));
    lzb <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- b;
    b_lzb_1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (b_lzb_1 `<<` (truncateu8 lzb));
    b_lzb_1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- LEA_64 (b_lzb_1 + a);
    temp3 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((temp2 \ult b_lzb) ? temp3 : temp);
    temp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((flag = (W64.of_int 1)) ? a : temp);
    temp <- aux;
    leakages <- LeakAddr([(W64.ALU.leak_div (temp))]) :: leakages;
    aux <- (temp \umod b);
    res_temp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- res_temp;
    result <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((flag = (W64.of_int 0)) ? a : result);
    result <- aux;
    return (result);
  }
}.

