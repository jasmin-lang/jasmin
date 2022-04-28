require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel Leakage_models.

require import Array64.
require import WArray64.


theory T.
clone import ALeakageModel as LeakageModel.

module M = {
  var leakages : leakages_t

  proc rotate_offset_BL (md_size:W32.t, mac_start:W32.t, scan_start:W32.t) :
  W32.t = {
    var aux: W32.t;

    var rotate_offset:W32.t;

    aux <- mac_start;
    rotate_offset <- aux;
    aux <- (rotate_offset - scan_start);
    rotate_offset <- aux;
    leakages <- LeakAddr(LeakageModel.leak_div_32 (rotate_offset) (md_size)) :: leakages;
    aux <- (rotate_offset \umod md_size);
    rotate_offset <- aux;
    return (rotate_offset);
  }

  proc rotate_offset_TV (md_size:W32.t, mac_start:W32.t, scan_start:W32.t) :
  W32.t = {
    var aux: W32.t;

    var rotate_offset:W32.t;
    var div_spoiler:W32.t;

    aux <- md_size;
    div_spoiler <- aux;
    aux <- (div_spoiler `<<` (W8.of_int 23));
    div_spoiler <- aux;
    aux <- mac_start;
    rotate_offset <- aux;
    aux <- (rotate_offset - scan_start);
    rotate_offset <- aux;
    aux <- (rotate_offset + div_spoiler);
    rotate_offset <- aux;
    leakages <- LeakAddr(LeakageModel.leak_div_32 (rotate_offset) (md_size)) :: leakages;
    aux <- (rotate_offset \umod md_size);
    rotate_offset <- aux;
    return (rotate_offset);
  }

  proc opp_mod (rotate_offset:W32.t, md_size:W32.t) : W32.t = {
    var aux: W32.t;

    var zero:W32.t;
    var temp:W32.t;

    aux <- (W32.of_int 0);
    zero <- aux;
    aux <- md_size;
    temp <- aux;
    aux <- (temp - rotate_offset);
    temp <- aux;
    aux <- temp;
    rotate_offset <- aux;
    aux <- ((rotate_offset = md_size) ? zero : rotate_offset);
    rotate_offset <- aux;
    return (rotate_offset);
  }

  proc rotate_mac_BL (md_size:W32.t, rotate_offset:W32.t, out:W64.t,
                      rotated_mac:W8.t Array64.t) : unit = {
    var aux_1: W8.t;
    var aux: W32.t;
    var aux_0: W64.t;

    var zero:W32.t;
    var i:W64.t;
    var j:W64.t;
    var old:W32.t;
    var new:W32.t;

    aux <- (W32.of_int 0);
    zero <- aux;
    aux <@ opp_mod (rotate_offset, md_size);
    rotate_offset <- aux;
    aux_0 <- (W64.of_int 0);
    i <- aux_0;

    leakages <- LeakCond(((truncateu32 i) \ult md_size)) :: LeakAddr(
    []) :: leakages;

    while (((truncateu32 i) \ult md_size)) {
      aux_0 <- (W64.of_int 0);
      j <- aux_0;

      leakages <- LeakCond(((truncateu32 j) \ult md_size)) :: LeakAddr(
      []) :: leakages;

      while (((truncateu32 j) \ult md_size)) {
        leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (out + j)))]) :: leakages;
        aux <- (zeroextu32 (loadW8 Glob.mem (W64.to_uint (out + j))));
        old <- aux;
        leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
        aux <- (zeroextu32 rotated_mac.[(W64.to_uint i)]);
        new <- aux;
        aux <- (((truncateu32 j) <> rotate_offset) ? old : new);
        new <- aux;
        aux <- new;
        leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (out + j)))]) :: leakages;
        Glob.mem <-
        storeW8 Glob.mem (W64.to_uint (out + j)) (truncateu8 aux);
        aux_0 <- (j + (W64.of_int 1));
        j <- aux_0;
      leakages <- LeakCond(((truncateu32 j) \ult md_size)) :: LeakAddr(
      []) :: leakages;

      }
      aux <- (rotate_offset + (W32.of_int 1));
      rotate_offset <- aux;
      aux <- ((md_size \ule rotate_offset) ? zero : rotate_offset);
      rotate_offset <- aux;
      aux_0 <- (i + (W64.of_int 1));
      i <- aux_0;
    leakages <- LeakCond(((truncateu32 i) \ult md_size)) :: LeakAddr(
    []) :: leakages;

    }
    return ();
  }

  proc rotate_mac_CL (md_size:W32.t, rotate_offset:W32.t, out:W64.t,
                      rotated_mac:W64.t) : unit = {
    var aux_0: W8.t;
    var aux: W64.t;

    var zero:W64.t;
    var ro:W64.t;
    var i:W64.t;
    var new:W8.t;

    aux <- (W64.of_int 0);
    zero <- aux;
    aux <- (zeroextu64 rotate_offset);
    ro <- aux;
    aux <- (W64.of_int 0);
    i <- aux;

    leakages <- LeakCond(((truncateu32 i) \ult md_size)) :: LeakAddr(
    []) :: leakages;

    while (((truncateu32 i) \ult md_size)) {
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rotated_mac + ro)))]) :: leakages;
      aux_0 <- (loadW8 Glob.mem (W64.to_uint (rotated_mac + ro)));
      new <- aux_0;
      aux_0 <- new;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (out + i)))]) :: leakages;
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (out + i)) aux_0;
      aux <- (ro + (W64.of_int 1));
      ro <- aux;
      aux <- ((md_size \ule (truncateu32 ro)) ? zero : ro);
      ro <- aux;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond(((truncateu32 i) \ult md_size)) :: LeakAddr(
    []) :: leakages;

    }
    return ();
  }

  proc rotate_mac_CL32 (md_size:W32.t, rotate_offset:W32.t, out:W64.t,
                        rotated_mac:W64.t) : unit = {
    var aux_0: W8.t;
    var aux: W64.t;

    var zero:W64.t;
    var ro:W64.t;
    var i:W64.t;
    var ro_and:W64.t;
    var new:W64.t;
    var ro_or:W64.t;
    var new_or:W64.t;

    aux <- (W64.of_int 0);
    zero <- aux;
    aux <- (zeroextu64 rotate_offset);
    ro <- aux;
    aux <- (W64.of_int 0);
    i <- aux;

    leakages <- LeakCond(((truncateu32 i) \ult md_size)) :: LeakAddr(
    []) :: leakages;

    while (((truncateu32 i) \ult md_size)) {
      aux <- ro;
      ro_and <- aux;
      aux <- (ro_and `&` (invw (W64.of_int 32)));
      ro_and <- aux;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rotated_mac + ro_and)))]) :: leakages;
      aux <- (zeroextu64 (loadW8 Glob.mem (W64.to_uint (rotated_mac + ro_and))));
      new <- aux;
      aux <- ro;
      ro_or <- aux;
      aux <- (ro_or `|` (W64.of_int 32));
      ro_or <- aux;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rotated_mac + ro_or)))]) :: leakages;
      aux <- (zeroextu64 (loadW8 Glob.mem (W64.to_uint (rotated_mac + ro_or))));
      new_or <- aux;
      aux <- ((ro = ro_or) ? new_or : new);
      new <- aux;
      aux <- new;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (out + i)))]) :: leakages;
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (out + i)) (truncateu8 aux);
      aux <- (ro + (W64.of_int 1));
      ro <- aux;
      aux <- ((md_size \ule (truncateu32 ro)) ? zero : ro);
      ro <- aux;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond(((truncateu32 i) \ult md_size)) :: LeakAddr(
    []) :: leakages;

    }
    return ();
  }

  proc init_scan_start (rec:W64.t, orig_len:W32.t, md_size:W32.t) : W64.t *
                                                                    W32.t *
                                                                    W32.t *
                                                                    W32.t = {
    var aux_0: W32.t;
    var aux: W64.t;

    var data:W64.t;
    var scan_start:W32.t;
    var mac_start:W32.t;
    var mac_end:W32.t;
    var zero:W64.t;
    var temp:W32.t;

    aux <- (W64.of_int 0);
    zero <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rec + (W64.of_int 16))))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (rec + (W64.of_int 16))));
    data <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rec + (W64.of_int 4))))]) :: leakages;
    aux_0 <- (loadW32 Glob.mem (W64.to_uint (rec + (W64.of_int 4))));
    mac_end <- aux_0;
    aux_0 <- mac_end;
    mac_start <- aux_0;
    aux_0 <- (mac_start - md_size);
    mac_start <- aux_0;
    aux_0 <- (W32.of_int 0);
    scan_start <- aux_0;
    aux_0 <- md_size;
    temp <- aux_0;
    aux_0 <- (temp + (W32.of_int 256));
    temp <- aux_0;
    leakages <- LeakCond((temp \ult orig_len)) :: LeakAddr([]) :: leakages;
    if ((temp \ult orig_len)) {
      aux_0 <- orig_len;
      scan_start <- aux_0;
      aux_0 <- (scan_start - temp);
      scan_start <- aux_0;
    } else {

    }
    return (data, scan_start, mac_start, mac_end);
  }

  proc init_rotated_mac_stk (data:W64.t, scan_start:W32.t, mac_start:W32.t,
                             mac_end:W32.t, orig_len:W32.t, md_size:W32.t) :
  W8.t Array64.t = {
    var aux_0: W8.t;
    var aux_1: W32.t;
    var aux: W64.t;

    var rotated_mac:W8.t Array64.t;
    var i:W64.t;
    var zero:W64.t;
    var j:W64.t;
    var new:W32.t;
    var old:W32.t;
    rotated_mac <- witness;
    aux <- (W64.of_int 0);
    i <- aux;

    leakages <- LeakCond((i \ult (W64.of_int 64))) :: LeakAddr([]) :: leakages;

    while ((i \ult (W64.of_int 64))) {
      aux_0 <- (W8.of_int 0);
      leakages <- LeakAddr([(W64.to_uint i)]) :: leakages;
      rotated_mac.[(W64.to_uint i)] <- aux_0;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult (W64.of_int 64))) :: LeakAddr([]) :: leakages;

    }
    aux <- (W64.of_int 0);
    zero <- aux;
    aux <- (zeroextu64 scan_start);
    i <- aux;
    aux <- (W64.of_int 0);
    j <- aux;

    leakages <- LeakCond(((truncateu32 i) \ult orig_len)) :: LeakAddr(
    []) :: leakages;

    while (((truncateu32 i) \ult orig_len)) {
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (data + (W64.of_int (W64.to_uint i)))))]) :: leakages;
      aux_1 <- (zeroextu32 (loadW8 Glob.mem (W64.to_uint (data + (W64.of_int (W64.to_uint i))))));
      new <- aux_1;
      leakages <- LeakAddr([(W64.to_uint j)]) :: leakages;
      aux_1 <- (zeroextu32 rotated_mac.[(W64.to_uint j)]);
      old <- aux_1;
      aux_1 <- (((truncateu32 i) \ult mac_start) ? old : new);
      new <- aux_1;
      aux_1 <- ((mac_end \ule (truncateu32 i)) ? old : new);
      new <- aux_1;
      aux_1 <- new;
      leakages <- LeakAddr([(W64.to_uint j)]) :: leakages;
      rotated_mac.[(W64.to_uint j)] <- (truncateu8 aux_1);
      aux <- (j + (W64.of_int 1));
      j <- aux;
      aux <- ((md_size \ule (truncateu32 j)) ? zero : j);
      j <- aux;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond(((truncateu32 i) \ult orig_len)) :: LeakAddr(
    []) :: leakages;

    }
    return (rotated_mac);
  }

  proc init_rotated_mac_mem (rotated_mac:W64.t, data:W64.t, scan_start:W32.t,
                             mac_start:W32.t, mac_end:W32.t, orig_len:W32.t,
                             md_size:W32.t) : unit = {
    var aux_0: W8.t;
    var aux_1: W32.t;
    var aux: W64.t;

    var i:W64.t;
    var zero:W64.t;
    var j:W64.t;
    var new:W32.t;
    var old:W32.t;

    aux <- (W64.of_int 0);
    i <- aux;

    leakages <- LeakCond((i \ult (W64.of_int 64))) :: LeakAddr([]) :: leakages;

    while ((i \ult (W64.of_int 64))) {
      aux_0 <- (W8.of_int 0);
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rotated_mac + i)))]) :: leakages;
      Glob.mem <- storeW8 Glob.mem (W64.to_uint (rotated_mac + i)) aux_0;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond((i \ult (W64.of_int 64))) :: LeakAddr([]) :: leakages;

    }
    aux <- (W64.of_int 0);
    zero <- aux;
    aux <- (zeroextu64 scan_start);
    i <- aux;
    aux <- (W64.of_int 0);
    j <- aux;

    leakages <- LeakCond(((truncateu32 i) \ult orig_len)) :: LeakAddr(
    []) :: leakages;

    while (((truncateu32 i) \ult orig_len)) {
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (data + (W64.of_int (W64.to_uint i)))))]) :: leakages;
      aux_1 <- (zeroextu32 (loadW8 Glob.mem (W64.to_uint (data + (W64.of_int (W64.to_uint i))))));
      new <- aux_1;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rotated_mac + j)))]) :: leakages;
      aux_1 <- (zeroextu32 (loadW8 Glob.mem (W64.to_uint (rotated_mac + j))));
      old <- aux_1;
      aux_1 <- (((truncateu32 i) \ult mac_start) ? old : new);
      new <- aux_1;
      aux_1 <- ((mac_end \ule (truncateu32 i)) ? old : new);
      new <- aux_1;
      aux_1 <- new;
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (rotated_mac + j)))]) :: leakages;
      Glob.mem <-
      storeW8 Glob.mem (W64.to_uint (rotated_mac + j)) (truncateu8 aux_1);
      aux <- (j + (W64.of_int 1));
      j <- aux;
      aux <- ((md_size \ule (truncateu32 j)) ? zero : j);
      j <- aux;
      aux <- (i + (W64.of_int 1));
      i <- aux;
    leakages <- LeakCond(((truncateu32 i) \ult orig_len)) :: LeakAddr(
    []) :: leakages;

    }
    return ();
  }

  proc ssl3_cbc_copy_mac_BL_BL (out:W64.t, rec:W64.t, orig_len:W32.t,
                                md_size:W32.t) : unit = {
    var aux_2: W32.t;
    var aux_1: W32.t;
    var aux_0: W32.t;
    var aux: W64.t;
    var aux_3: W8.t Array64.t;

    var data:W64.t;
    var scan_start:W32.t;
    var mac_start:W32.t;
    var mac_end:W32.t;
    var rotated_mac:W8.t Array64.t;
    var rotate_offset:W32.t;
    rotated_mac <- witness;
    (aux, aux_2, aux_1, aux_0) <@ init_scan_start (rec, orig_len, md_size);
    data <- aux;
    scan_start <- aux_2;
    mac_start <- aux_1;
    mac_end <- aux_0;
    aux_3 <@ init_rotated_mac_stk (data, scan_start, mac_start, mac_end,
    orig_len, md_size);
    rotated_mac <- aux_3;
    aux_2 <@ rotate_offset_BL (md_size, mac_start, scan_start);
    rotate_offset <- aux_2;
    rotate_mac_BL (md_size, rotate_offset, out, rotated_mac);
    return ();
  }

  proc ssl3_cbc_copy_mac_BL_CL (out:W64.t, rec:W64.t, orig_len:W32.t,
                                md_size:W32.t, rotated_mac:W64.t) : unit = {
    var aux_2: W32.t;
    var aux_1: W32.t;
    var aux_0: W32.t;
    var aux: W64.t;

    var data:W64.t;
    var scan_start:W32.t;
    var mac_start:W32.t;
    var mac_end:W32.t;
    var rotate_offset:W32.t;

    (aux, aux_2, aux_1, aux_0) <@ init_scan_start (rec, orig_len, md_size);
    data <- aux;
    scan_start <- aux_2;
    mac_start <- aux_1;
    mac_end <- aux_0;
    init_rotated_mac_mem (rotated_mac, data, scan_start, mac_start, mac_end,
    orig_len, md_size);
    aux_2 <@ rotate_offset_BL (md_size, mac_start, scan_start);
    rotate_offset <- aux_2;
    rotate_mac_CL (md_size, rotate_offset, out, rotated_mac);
    return ();
  }

  proc ssl3_cbc_copy_mac_TV_BL (out:W64.t, rec:W64.t, orig_len:W32.t,
                                md_size:W32.t) : unit = {
    var aux_2: W32.t;
    var aux_1: W32.t;
    var aux_0: W32.t;
    var aux: W64.t;
    var aux_3: W8.t Array64.t;

    var data:W64.t;
    var scan_start:W32.t;
    var mac_start:W32.t;
    var mac_end:W32.t;
    var rotated_mac:W8.t Array64.t;
    var rotate_offset:W32.t;
    rotated_mac <- witness;
    (aux, aux_2, aux_1, aux_0) <@ init_scan_start (rec, orig_len, md_size);
    data <- aux;
    scan_start <- aux_2;
    mac_start <- aux_1;
    mac_end <- aux_0;
    aux_3 <@ init_rotated_mac_stk (data, scan_start, mac_start, mac_end,
    orig_len, md_size);
    rotated_mac <- aux_3;
    aux_2 <@ rotate_offset_TV (md_size, mac_start, scan_start);
    rotate_offset <- aux_2;
    rotate_mac_BL (md_size, rotate_offset, out, rotated_mac);
    return ();
  }

  proc ssl3_cbc_copy_mac_TV_CL (out:W64.t, rec:W64.t, orig_len:W32.t,
                                md_size:W32.t, rotated_mac:W64.t) : unit = {
    var aux_2: W32.t;
    var aux_1: W32.t;
    var aux_0: W32.t;
    var aux: W64.t;

    var data:W64.t;
    var scan_start:W32.t;
    var mac_start:W32.t;
    var mac_end:W32.t;
    var rotate_offset:W32.t;

    (aux, aux_2, aux_1, aux_0) <@ init_scan_start (rec, orig_len, md_size);
    data <- aux;
    scan_start <- aux_2;
    mac_start <- aux_1;
    mac_end <- aux_0;
    init_rotated_mac_mem (rotated_mac, data, scan_start, mac_start, mac_end,
    orig_len, md_size);
    aux_2 <@ rotate_offset_TV (md_size, mac_start, scan_start);
    rotate_offset <- aux_2;
    rotate_mac_CL (md_size, rotate_offset, out, rotated_mac);
    return ();
  }

  proc ssl3_cbc_copy_mac_BL_CL32 (out:W64.t, rec:W64.t, orig_len:W32.t,
                                  md_size:W32.t, rotated_mac:W64.t) : unit = {
    var aux_2: W32.t;
    var aux_1: W32.t;
    var aux_0: W32.t;
    var aux: W64.t;

    var data:W64.t;
    var scan_start:W32.t;
    var mac_start:W32.t;
    var mac_end:W32.t;
    var rotate_offset:W32.t;

    (aux, aux_2, aux_1, aux_0) <@ init_scan_start (rec, orig_len, md_size);
    data <- aux;
    scan_start <- aux_2;
    mac_start <- aux_1;
    mac_end <- aux_0;
    init_rotated_mac_mem (rotated_mac, data, scan_start, mac_start, mac_end,
    orig_len, md_size);
    aux_2 <@ rotate_offset_BL (md_size, mac_start, scan_start);
    rotate_offset <- aux_2;
    rotate_mac_CL32 (md_size, rotate_offset, out, rotated_mac);
    return ();
  }

  proc ssl3_cbc_copy_mac_TV_CL32 (out:W64.t, rec:W64.t, orig_len:W32.t,
                                  md_size:W32.t, rotated_mac:W64.t) : unit = {
    var aux_2: W32.t;
    var aux_1: W32.t;
    var aux_0: W32.t;
    var aux: W64.t;

    var data:W64.t;
    var scan_start:W32.t;
    var mac_start:W32.t;
    var mac_end:W32.t;
    var rotate_offset:W32.t;

    (aux, aux_2, aux_1, aux_0) <@ init_scan_start (rec, orig_len, md_size);
    data <- aux;
    scan_start <- aux_2;
    mac_start <- aux_1;
    mac_end <- aux_0;
    init_rotated_mac_mem (rotated_mac, data, scan_start, mac_start, mac_end,
    orig_len, md_size);
    aux_2 <@ rotate_offset_TV (md_size, mac_start, scan_start);
    rotate_offset <- aux_2;
    rotate_mac_CL32 (md_size, rotate_offset, out, rotated_mac);
    return ();
  }
}.
end T.
