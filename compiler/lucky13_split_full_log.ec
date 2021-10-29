require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require import Array128.
require import WArray128.



module M = {
  var leakages : leakages_t
  
  proc duplicate_msb_to_all_jasmin (x:W32.t) : W32.t = {
    var aux: W32.t;
    
    var result:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    result <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (result `|>>` (W8.of_int 31));
    result <- aux;
    return (result);
  }
  
  proc duplicate_msb_to_all_8_jasmin (x:W32.t) : W8.t = {
    var aux_0: W8.t;
    var aux: W32.t;
    
    var result:W8.t;
    var temp:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- x;
    temp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ duplicate_msb_to_all_jasmin (temp);
    temp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- temp;
    result <- (truncateu8 aux);
    return (result);
  }
  
  proc constant_time_lt_jasmin (a:W32.t, b:W32.t) : W32.t = {
    var aux: W32.t;
    
    var result:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    result <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (result - b);
    result <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ duplicate_msb_to_all_jasmin (result);
    result <- aux;
    return (result);
  }
  
  proc constant_time_ge_jasmin (a:W32.t, b:W32.t) : W32.t = {
    var aux: W32.t;
    
    var result:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    result <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (result - b);
    result <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (invw result);
    result <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ duplicate_msb_to_all_jasmin (result);
    result <- aux;
    return (result);
  }
  
  proc constant_time_eq_8_jasmin (a:W32.t, b:W32.t) : W8.t = {
    var aux_0: W8.t;
    var aux: W32.t;
    
    var result:W8.t;
    var temp:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    temp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (temp `^` b);
    temp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (temp - (W32.of_int 1));
    temp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ duplicate_msb_to_all_8_jasmin (temp);
    result <- aux_0;
    return (result);
  }
  
  proc rotate_offset_div (md_size:W32.t, div_spoiler:W32.t, mac_start:W32.t,
                          scan_start:W32.t) : W32.t = {
    var aux: W32.t;
    
    var rotate_offset:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- md_size;
    div_spoiler <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (div_spoiler `<<` (W8.of_int 23));
    div_spoiler <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- mac_start;
    rotate_offset <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (rotate_offset - scan_start);
    rotate_offset <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (rotate_offset + div_spoiler);
    rotate_offset <- aux;
    leakages <- LeakAddr([(W32.ALU.leak_div (rotate_offset))]) :: leakages;
    aux <- (rotate_offset \umod md_size);
    rotate_offset <- aux;
    return (rotate_offset);
  }
  
  proc rotate_mac (md_size:W32.t, rotate_offset:W32.t, out:W64.t,
                   rotated_mac:W8.t Array128.t) : unit = {
    var aux_0: W8.t;
    var aux: W32.t;
    var aux_1: W64.t;
    
    var i:W32.t;
    var j:W32.t;
    var temp_8:W8.t;
    var temp:W64.t;
    var temp2_8:W8.t;
    var temp_32:W32.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    i <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W32.of_int 0);
    j <- aux;
    
    leakages <- LeakCond((i \ult md_size)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult md_size)) {
      
      leakages <- LeakCond((j \ult md_size)) :: LeakAddr([]) :: leakages;
      
      while ((j \ult md_size)) {
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <@ constant_time_eq_8_jasmin (j, rotate_offset);
        temp_8 <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <- (zeroextu64 i);
        temp <- aux_1;
        leakages <- LeakAddr([(W64.to_uint temp)]) :: leakages;
        aux_0 <- (temp_8 `&` rotated_mac.[(W64.to_uint temp)]);
        temp_8 <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <- (zeroextu64 j);
        temp <- aux_1;
        leakages <- LeakAddr([(W64.to_uint (out + temp))]) :: leakages;
        aux_0 <- (loadW8 Glob.mem (W64.to_uint (out + temp)));
        temp2_8 <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (temp2_8 `|` temp_8);
        temp2_8 <- aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- temp2_8;
        leakages <- LeakAddr([(W64.to_uint (out + temp))]) :: leakages;
        Glob.mem <- storeW8 Glob.mem (W64.to_uint (out + temp)) aux_0;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (j + (W32.of_int 1));
        j <- aux;
      leakages <- LeakCond((j \ult md_size)) :: LeakAddr([]) :: leakages;
      
      }
      leakages <- LeakAddr([]) :: leakages;
      aux <- (rotate_offset + (W32.of_int 1));
      rotate_offset <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <@ constant_time_lt_jasmin (rotate_offset, md_size);
      temp_32 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (rotate_offset `&` temp_32);
      rotate_offset <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (i + (W32.of_int 1));
      i <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (W32.of_int 0);
      j <- aux;
    leakages <- LeakCond((i \ult md_size)) :: LeakAddr([]) :: leakages;
    
    }
    return ();
  }
  
  proc ssl3_cbc_copy_mac_jasmin (out:W64.t, rec:W64.t, orig_len:W32.t,
                                 md_size:W32.t) : unit = {
    var aux_1: W8.t;
    var aux_0: W32.t;
    var aux: W64.t;
    
    var data:W64.t;
    var mac_end:W32.t;
    var mac_start:W32.t;
    var scan_start:W32.t;
    var temp_32:W32.t;
    var i:W32.t;
    var temp:W64.t;
    var rotated_mac:W8.t Array128.t;
    var j:W32.t;
    var temp2_32:W32.t;
    var mac_started:W8.t;
    var mac_ended:W8.t;
    var b:W8.t;
    var temp_8:W8.t;
    var temp2_8:W8.t;
    var div_spoiler:W32.t;
    var rotate_offset:W32.t;
    rotated_mac <- witness;
    leakages <- LeakAddr([(W64.to_uint (rec + (W64.of_int 16)))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (rec + (W64.of_int 16))));
    data <- aux;
    leakages <- LeakAddr([(W64.to_uint (rec + (W64.of_int 4)))]) :: leakages;
    aux_0 <- (loadW32 Glob.mem (W64.to_uint (rec + (W64.of_int 4))));
    mac_end <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- mac_end;
    mac_start <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (mac_start - md_size);
    mac_start <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 0);
    scan_start <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- md_size;
    temp_32 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (temp_32 + (W32.of_int 256));
    temp_32 <- aux_0;
    leakages <- LeakCond((temp_32 \ult orig_len)) :: LeakAddr([]) :: leakages;
    if ((temp_32 \ult orig_len)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- orig_len;
      scan_start <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (scan_start - temp_32);
      scan_start <- aux_0;
    } else {
      
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 0);
    i <- aux_0;
    
    leakages <- LeakCond((i \ult md_size)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult md_size)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <- (zeroextu64 i);
      temp <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (W8.of_int 0);
      leakages <- LeakAddr([(W64.to_uint temp)]) :: leakages;
      rotated_mac.[(W64.to_uint temp)] <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (i + (W32.of_int 1));
      i <- aux_0;
    leakages <- LeakCond((i \ult md_size)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- scan_start;
    i <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 0);
    j <- aux_0;
    
    leakages <- LeakCond((i \ult orig_len)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult orig_len)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- mac_end;
      temp2_32 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (temp2_32 - md_size);
      temp2_32 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ constant_time_ge_jasmin (i, temp2_32);
      temp_32 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- temp_32;
      mac_started <- (truncateu8 aux_0);
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- mac_end;
      temp2_32 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ constant_time_ge_jasmin (i, temp2_32);
      temp_32 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- temp_32;
      mac_ended <- (truncateu8 aux_0);
      leakages <- LeakAddr([]) :: leakages;
      aux <- (zeroextu64 i);
      temp <- aux;
      leakages <- LeakAddr([(W64.to_uint (data + temp))]) :: leakages;
      aux_1 <- (loadW8 Glob.mem (W64.to_uint (data + temp)));
      b <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- mac_started;
      temp_8 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (invw mac_ended);
      mac_ended <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (temp_8 `&` mac_ended);
      temp_8 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (temp_8 `&` b);
      temp_8 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (zeroextu64 j);
      temp <- aux;
      leakages <- LeakAddr([(W64.to_uint temp)]) :: leakages;
      aux_1 <- rotated_mac.[(W64.to_uint temp)];
      temp2_8 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (temp2_8 `|` temp_8);
      temp2_8 <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- temp2_8;
      leakages <- LeakAddr([(W64.to_uint temp)]) :: leakages;
      rotated_mac.[(W64.to_uint temp)] <- aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (j + (W32.of_int 1));
      j <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ constant_time_lt_jasmin (j, md_size);
      temp_32 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (zeroextu64 temp_32);
      temp <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (j `&` (truncateu32 temp));
      j <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (i + (W32.of_int 1));
      i <- aux_0;
    leakages <- LeakCond((i \ult orig_len)) :: LeakAddr([]) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ rotate_offset_div (md_size, div_spoiler, mac_start, scan_start);
    rotate_offset <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (W64.of_int 0);
    temp <- aux;
    
    leakages <- LeakCond(((truncateu32 temp) \ult md_size)) :: LeakAddr(
    []) :: leakages;
    
    while (((truncateu32 temp) \ult md_size)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- (W8.of_int 0);
      leakages <- LeakAddr([(W64.to_uint (out + temp))]) :: leakages;
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (out + temp)) aux_1;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (temp + (W64.of_int 1));
      temp <- aux;
    leakages <- LeakCond(((truncateu32 temp) \ult md_size)) :: LeakAddr(
    []) :: leakages;
    
    }
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- md_size;
    temp_32 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (temp_32 - rotate_offset);
    temp_32 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- temp_32;
    rotate_offset <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ constant_time_lt_jasmin (rotate_offset, md_size);
    temp_32 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (zeroextu64 temp_32);
    temp <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (rotate_offset `&` (truncateu32 temp));
    rotate_offset <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    rotate_mac (md_size, rotate_offset, out, rotated_mac);
    return ();
  }
}.

