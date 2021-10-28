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
  
  proc rotate_offset_div (rotate_offset:W32.t, md_size:W32.t,
                          div_spoiler:W32.t, mac_start:W32.t,
                          scan_start:W32.t) : W32.t = {
    var aux: W32.t;
    
    
    
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
    leakages <- LeakAddr([(zlog2 (to_uint (rotate_offset)))]) :: leakages;
    aux <- (rotate_offset \umod md_size);
    rotate_offset <- aux;
    return (rotate_offset);
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
    var rotate_offset:W32.t;
    var div_spoiler:W32.t;
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
    aux_0 <@ rotate_offset_div (rotate_offset, md_size, div_spoiler,
    mac_start, scan_start);
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
    aux_0 <- (W32.of_int 0);
    i <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (W32.of_int 0);
    j <- aux_0;
    
    leakages <- LeakCond((i \ult md_size)) :: LeakAddr([]) :: leakages;
    
    while ((i \ult md_size)) {
      
      leakages <- LeakCond((j \ult md_size)) :: LeakAddr([]) :: leakages;
      
      while ((j \ult md_size)) {
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <@ constant_time_eq_8_jasmin (j, rotate_offset);
        temp_8 <- aux_1;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (zeroextu64 i);
        temp <- aux;
        leakages <- LeakAddr([(W64.to_uint temp)]) :: leakages;
        aux_1 <- (temp_8 `&` rotated_mac.[(W64.to_uint temp)]);
        temp_8 <- aux_1;
        leakages <- LeakAddr([]) :: leakages;
        aux <- (zeroextu64 j);
        temp <- aux;
        leakages <- LeakAddr([(W64.to_uint (out + temp))]) :: leakages;
        aux_1 <- (loadW8 Glob.mem (W64.to_uint (out + temp)));
        temp2_8 <- aux_1;
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <- (temp2_8 `|` temp_8);
        temp2_8 <- aux_1;
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <- temp2_8;
        leakages <- LeakAddr([(W64.to_uint (out + temp))]) :: leakages;
        Glob.mem <- storeW8 Glob.mem (W64.to_uint (out + temp)) aux_1;
        leakages <- LeakAddr([]) :: leakages;
        aux_0 <- (j + (W32.of_int 1));
        j <- aux_0;
      leakages <- LeakCond((j \ult md_size)) :: LeakAddr([]) :: leakages;
      
      }
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (rotate_offset + (W32.of_int 1));
      rotate_offset <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ constant_time_lt_jasmin (rotate_offset, md_size);
      temp_32 <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (rotate_offset `&` temp_32);
      rotate_offset <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (i + (W32.of_int 1));
      i <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W32.of_int 0);
      j <- aux_0;
    leakages <- LeakCond((i \ult md_size)) :: LeakAddr([]) :: leakages;
    
    }
    return ();
  }
}.

equiv l1 : M.constant_time_lt_jasmin ~ M.constant_time_lt_jasmin :
={M.leakages}
==> ={M.leakages}.
proof.
proc; inline *; sim.
qed.

equiv l2 : M.constant_time_ge_jasmin ~ M.constant_time_ge_jasmin :
={M.leakages}
==> ={M.leakages}.
proof.
proc; inline *; sim.
qed.

equiv l3 : M.constant_time_eq_8_jasmin ~ M.constant_time_eq_8_jasmin :
={M.leakages}
==> ={M.leakages}.
proof.
proc; inline *; sim.
qed.


equiv l4 : M.rotate_offset_div ~ M.rotate_offset_div:
={M.leakages, md_size, scan_start} /\
(0 <= (to_uint (mac_start - scan_start)) < 2^8){1} /\ 
(0 <= (to_uint (mac_start - scan_start)) < 2^8){2} /\
(16 <= to_uint md_size <= 64){1}
==> ={M.leakages}.
proof.
admitted.
(*
  proc.
  wp.
  skip=> />.
  move=> &1 &2 h1.
    
  *)
(* mac_start : position of start of tag *)
(*
equiv l4 : M.rotate_offset_div ~ M.rotate_offset_div:
={M.leakages} /\
zlog2 (to_uint (mac_start{1} + (md_size{1} `>>` W8.one `<<` (of_int 24)%W8) - scan_start{1})) =
zlog2 (to_uint (mac_start{2} + (md_size{2} `>>` W8.one `<<` (of_int 24)%W8) - scan_start{2}))
(*/\
zlog2 (to_uint rotate_offset{1}) = zlog2 (to_uint rotate_offset{2})*)
==> ={M.leakages}.
proof.
proc.
wp.
skip=> /> &1 &2.
qed.
*)

(* md_size : mac tag size --> public *)
(* orig_len : length of record : header + data + mac tag + padding --> public *)
(* out : mac tag is stored in out --> public *)
(* rec : whole message including header, message, tag, padding --> public *)

lemma foo (orig_len mac_end : int) :  
  1 <= orig_len - mac_end <= 256 => 
  0 <= mac_end - orig_len +  256 < 256.
smt().
qed.

lemma foo' (orig_len mac_end md_size : int) :
(*  16 <= md_size <= 64 => *)
  md_size <= mac_end =>
  1 <= orig_len - mac_end <= 256 => 
  !(md_size + 256 < orig_len) => 
  0 <= mac_end - md_size < 256.
smt().
qed.

op cond_md_size_mac_end mac_end orig_len md_size = 
   
  if (md_size + W32.of_int 256 \ult orig_len) then 
     0 <= to_uint (mac_end - orig_len +  W32.of_int 256) < 256 
  else 0 <= to_uint (mac_end - md_size) < 256.


equiv l_final : M.ssl3_cbc_copy_mac_jasmin ~ M.ssl3_cbc_copy_mac_jasmin :
={M.leakages, md_size, orig_len, out, rec} /\
16 <= to_uint md_size{2} <= 64 /\
(* TODO : replace this two hyp by : 
   md_size <= mac_end =>
   1 <= orig_len - mac_end <= 256 *)
cond_md_size_mac_end (loadW32 Glob.mem{1} (to_uint (rec{1} + W64.of_int 4))) orig_len{1} md_size{1} /\
cond_md_size_mac_end (loadW32 Glob.mem{2} (to_uint (rec{2} + W64.of_int 4))) orig_len{2} md_size{2} /\
(loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){1} =
(loadW64 Glob.mem (to_uint (rec + (of_int 16)%W64))){2}
==> ={M.leakages}.
proof.
proc.
wp.
while (={M.leakages, out, i, j, md_size}).
inline *; sim.
conseq (: _ ==> ={M.leakages, i,j, md_size, out}) => //.
wp; call l1; wp.
while (={M.leakages, temp, out, md_size}).
+ by sim.
wp => /=.
conseq />.
call l4.
wp.
while (={i, j, orig_len, data, md_size, M.leakages}); 1: by inline*;sim.
wp => /=.
while (={i, md_size, M.leakages}); 1: by sim.
wp; skip => /> &1 &2 h1 h2 h3 h4 h5; split => h6 *.
+ pose mac_end1 := loadW32 _ _.
  pose mac_end2 := loadW32 _ _.
  have -> : (mac_end1 - md_size{2} - (orig_len{2} - (md_size{2} + W32.of_int 256))) = 
          (mac_end1 - orig_len{2} +  W32.of_int 256) by ring.
  by have -> /#: (mac_end2 - md_size{2} - (orig_len{2} - (md_size{2} + W32.of_int 256))) = 
          (mac_end2 - orig_len{2} +  W32.of_int 256) by ring.
rewrite !W32.WRingA.subr0 /#.
qed.
