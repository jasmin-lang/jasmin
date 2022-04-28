require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel Leakage_models.
require Keccak1600_avx2_TV_CL64.
import StdOrder.IntOrder Ring.IntID.

clone import Keccak1600_avx2_TV_CL64.T with
theory LeakageModel <-  LeakageModelCL.

abbrev g_zero = W64.of_int 0.

op eq_reg (mem1 mem2 : global_mem_t, ptr len : int) =
    forall i, ptr <= i <= ptr + len - 8 =>
      loadW64 mem1 i = loadW64 mem2 i.

op disj_reg(ptr1 len1 ptr2 len2 : W64.t) =
  (to_uint (ptr1 + len1) < to_uint ptr2 \/ to_uint (ptr2 + len2) < to_uint ptr1).

lemma mem_sep (mem : global_mem_t) (ptr1 o1 x : W64.t) (ptr2 : int):
   0 <= ptr2 < W64.modulus - 8 /\
   to_uint ptr1 + to_uint o1 + 8 < W64.modulus /\
   disj_reg (ptr1 + o1) (W64.of_int 8) (W64.of_int ptr2) (W64.of_int 8) =>
  loadW64 (storeW64 mem (to_uint (ptr1 + o1)) x) ptr2 =
       loadW64 mem ptr2.
progress.
rewrite storeW64E.
rewrite /loadW64.
congr.
apply W8u8.Pack.init_ext.
move => x0 hxc0.
beta.
rewrite (get_storesE mem (to_uint (ptr1 + o1)) (((to_list x))%W8u8) (ptr2 + x0)).
rewrite  (_: to_uint (ptr1 + o1) <= ptr2 + x0 <
    to_uint (ptr1 + o1) + size ((to_list x))%W8u8 = false) => //=.
have bound : ( ptr2 + x0 < to_uint (ptr1 + o1) \/ to_uint (ptr1 + o1) + 8 <=ptr2 + x0); last by smt().
elim H2.
rewrite !to_uintD_small. smt(@W64).  smt(@W64). smt(@W64).
rewrite !of_uintK => />. by smt(@W64).
rewrite !to_uintD_small. smt(@W64). smt(@W64).
progress. move : H2. rewrite !of_uintK => />. by smt(@W64).
qed.

equiv ct :
  M.__keccak1600_avx2 ~ M.__keccak1600_avx2 :
     ={M.leakages,out,outlen,rhotates_left,rhotates_right,iotas,a_jagged,in_0,inlen,rate} /\
    to_uint out{2} + to_uint (outlen{2} + W64.of_int 8)  < W64.modulus /\
    to_uint a_jagged{2} + 224 < W64.modulus /\ 0 < to_uint rate{2} < 200 /\
    eq_reg Glob.mem{1} Glob.mem{2} (to_uint a_jagged{1}) 224  /\
    disj_reg out{1} (outlen{1} + W64.of_int 8) a_jagged{1} (W64.of_int 224) /\
    disj_reg out{2} (outlen{2} + W64.of_int 8) a_jagged{2} (W64.of_int 224) /\
    to_uint outlen{2} + 8 < W64.modulus ==> ={M.leakages}.
proc.
call (_: ={rhotates_left,rhotates_right,iotas,a_jagged,out,outlen,rate,M.leakages} /\        to_uint rate{2} < 200 /\
    to_uint out{2} + to_uint (outlen{2} + W64.of_int 8) < W64.modulus /\
    to_uint a_jagged{2} + 224 < W64.modulus /\
    eq_reg Glob.mem{1} Glob.mem{2} (to_uint a_jagged{1}) 224  /\
    disj_reg out{1} (outlen{1} + W64.of_int 8) a_jagged{1} (W64.of_int 224) /\
    disj_reg out{2} (outlen{2} + W64.of_int 8) a_jagged{2} (W64.of_int 224)  /\
    to_uint outlen{2} + 8 < W64.modulus ==> ={M.leakages}).
proc.
wp; call(_: ={a_jagged,out,len,M.leakages} /\
        to_uint len{2} <= 200 /\
        to_uint out{2} + to_uint (len{2} + W64.of_int 8) < W64.modulus /\
        to_uint a_jagged{2} + 224 < W64.modulus /\
        eq_reg Glob.mem{1} Glob.mem{2} (to_uint a_jagged{1}) 224 /\
        disj_reg out{1} (len{1} + W64.of_int 8) a_jagged{1} (W64.of_int 224) /\
        disj_reg out{2} (len{2} + W64.of_int 8) a_jagged{2} (W64.of_int 224)  ==> ={M.leakages}).
proc.
wp; while (={j,len,M.leakages,out,l}).
by auto => />.
+ wp; while (={j,M.leakages,out,a_jagged,len8,len} /\
               to_uint len8{2} <= 25 /\ to_uint j{2} <= to_uint len8{2} /\
               to_uint out{2} + to_uint (len{2} + W64.of_int 8) < W64.modulus /\
               to_uint a_jagged{2} + 224 < W64.modulus /\
               eq_reg Glob.mem{1} Glob.mem{2} (to_uint a_jagged{1}) 224  /\
               disj_reg out{1} (len{1} + W64.of_int 8) a_jagged{1} (W64.of_int 224) /\
               disj_reg out{2} (len{2} + W64.of_int 8) a_jagged{2} (W64.of_int 224) /\
               0 <= to_uint len8{2} < 26 /\ to_uint len8{1} = to_uint len{1} %/  8).
  + auto => />. rewrite /eq_reg /disj_reg. progress.
    + congr. move : H8; rewrite ultE => *.
      by apply H3;rewrite to_uintD_small;by smt(@W64).
    by smt(@W64).
    rewrite (mem_sep Glob.mem{1} out{2} (((of_int 8)%W64 * j{2}))). split.
    + by smt(@W64).
    split. + by smt(@W64).
    rewrite /disj_reg.
    elim H4.
    + rewrite !to_uintD_small => />. + by smt(@W64). + by smt(@W64). + by smt(@W64). + by smt(@W64).
      + by smt(@W64). + by smt(@W64). by smt(@W64).
      move => H4. left. rewrite !to_uintM_small. + by smt(@W64).
      rewrite of_uintK => />. move : H8; rewrite ultE H7. move => *.
      have hh : (8 * to_uint j{2} < to_uint len{2}).
      + by smt(@W64).
      rewrite of_uintK => //=. rewrite (_: i0 %% 18446744073709551616 = i0).
      + by smt(@W64). by smt(@W64).
    rewrite !to_uintD_small. + by smt(@W64). + by smt(@W64). + by smt(@W64). + by smt(@W64). + by smt(@W64).
    by smt(@W64).
 rewrite  (mem_sep Glob.mem{2} out{2} (((of_int 8)%W64 * j{2}))).
 + split. + by smt(@W64).
   + split. + by smt(@W64).
   rewrite /disj_reg. elim H4.
   + rewrite !to_uintD_small => />. + by smt(@W64). + by smt(@W64). + by smt(@W64).  + by smt(@W64).
     + by smt(@W64). + by smt(@W64). by smt(@W64).
     move => H4. left. rewrite !to_uintM_small. + by smt(@W64).
     rewrite of_uintK => />. move : H8; rewrite ultE H7. move => *.
     have hh : (8 * to_uint j{2} < to_uint len{2}). + by smt(@W64).
     rewrite of_uintK => //=. rewrite (_: i0 %% 18446744073709551616 = i0).
     + by smt(@W64). by smt(@W64).
   rewrite !to_uintD_small. + by smt(@W64). + by smt(@W64). + by smt(@W64). + by smt(@W64). + by smt(@W64).
   by smt(@W64).
  apply H3. by smt(@W64).
+ unroll for {1} 4.
  unroll for {2} 4.
  auto => />. progress.
  rewrite shr_div => />. + by smt().
  + rewrite shr_div => />. by smt(@W64).
  + rewrite shr_div => />. by smt(@W64).
  + rewrite shr_div => />. by smt(@W64).
  by rewrite shr_div => />.
  move : H8; rewrite /eq_reg => H8. rewrite H8 =>//=.
  by rewrite to_uintD_small; by smt(@W64).
+ wp;call(_: ={M.leakages,_rhotates_left,_rhotates_right,_iotas} ==> ={M.leakages}).
  + proc. by sim.
  wp;while(={M.leakages,rate,outlen,rhotates_left,rhotates_right,iotas,a_jagged,out} /\
             to_uint rate{2} < 200 /\
             to_uint out{2} + to_uint (outlen{2} + W64.of_int 8) < W64.modulus /\
             to_uint a_jagged{2} + 224 < W64.modulus /\
             eq_reg Glob.mem{1} Glob.mem{2} (to_uint a_jagged{1}) 224  /\
             disj_reg out{1} (outlen{1} + W64.of_int 8) a_jagged{1} (W64.of_int 224) /\
             disj_reg out{2} (outlen{2} + W64.of_int 8) a_jagged{2} (W64.of_int 224) /\
             to_uint outlen{2} + 8 < W64.modulus).
  + exists* a_jagged{1}, outlen{1}, rate{1}, out{1}.
    elim* => a_j ol rt ot.
    wp; call(_: ={a_jagged,out,len,M.leakages} /\
                  to_uint len{2} < 200 /\ a_jagged{1} = a_j /\ len{1} = rt /\ out{1} = ot /\
                  to_uint out{2} + to_uint (len{2} + W64.of_int 8) < W64.modulus /\
                  to_uint a_jagged{2} + 224 < W64.modulus /\
                  eq_reg Glob.mem{1} Glob.mem{2} (to_uint a_jagged{1}) 224 /\
                  disj_reg out{1} (ol{1} + W64.of_int 8) a_jagged{1} (W64.of_int 224) /\
                  disj_reg out{2} (ol{2} + W64.of_int 8) a_jagged{2} (W64.of_int 224) /\ len{1} \ult ol /\
                  to_uint out{2} + (to_uint ol + 8) < W64.modulus
              ==> ={M.leakages,res} /\
                  eq_reg Glob.mem{1} Glob.mem{2} (to_uint a_j) 224 /\
                  res{1} = ot + rt).
    + proc.
      wp; while (={j,M.leakages,out,a_jagged,len8,len} /\ out{1} = ot /\
                   a_jagged{1} = a_j /\ to_uint len8{1} = to_uint rt %/ 8 /\
                   to_uint len8{2} < 25 /\ to_uint j{2} <= to_uint len8{2} /\
                   to_uint out{2} + to_uint  (len{2} + W64.of_int 8)< W64.modulus /\
                   to_uint a_jagged{2} + 224 < W64.modulus /\
                   eq_reg Glob.mem{1} Glob.mem{2} (to_uint a_jagged{1}) 224  /\
                   disj_reg out{1}  (ol{1} + W64.of_int 8) a_jagged{1} (W64.of_int 224) /\
                   disj_reg out{2}  (ol{2} + W64.of_int 8) a_jagged{2} (W64.of_int 224) /\
                   0 <= to_uint len8{2} < 26 /\ to_uint len8{1} = to_uint len{1} %/  8
                   /\ len{1} \ult ol  /\ to_uint out{2} + (to_uint ol + 8) < W64.modulus).
      + auto => />. rewrite /eq_reg /disj_reg. progress.
        + congr. move : H9; rewrite ultE => *. by apply H4;rewrite to_uintD_small; smt(@W64).
        by smt(@W64).
      rewrite mem_sep. split. + by smt(@W64). split. + by smt(@W64).
      + rewrite /disj_reg. elim H5.
        + rewrite !to_uintD_small => />. + by smt(@W64). + by smt(@W64). + by smt(@W64). + by smt(@W64).
          + by smt(@W64). + by smt(@W64).
          + move => H5. left. rewrite !to_uintM_small. + by smt(@W64).
            rewrite of_uintK => />. move : H11; rewrite ultE H8. move => *.
            have hh : (8 * to_uint j{2} < to_uint len{2}). + by smt(@W64).
            rewrite of_uintK => //=. rewrite (_: i0 %% 18446744073709551616 = i0).
            + by smt(@W64).
            by smt(@W64).
          rewrite !to_uintD_small. + by smt(@W64). + by smt(@W64). + by smt(@W64). + by smt(@W64).
          + by smt(@W64).
          by smt(@W64).
        rewrite mem_sep. + split. + by smt(@W64).
        + split. + by smt(@W64).
        rewrite /disj_reg. elim H5.
        + rewrite !to_uintD_small => />. + by smt(@W64). + by smt(@W64). + by smt(@W64). + by smt(@W64).
          + by smt(@W64). by smt(@W64).
        move => H5. left. rewrite !to_uintM_small. + by smt(@W64).
        rewrite of_uintK => />. move : H11; rewrite ultE H8. move => *.
        have hh : (8 * to_uint j{2} < to_uint len{2}).
        + by smt(@W64).
        rewrite of_uintK => //=. rewrite (_: i0 %% 18446744073709551616 = i0).
        + by smt(@W64).
        by smt(@W64).
      rewrite !to_uintD_small. + by smt(@W64). + by smt(@W64). + by smt(@W64). + by smt(@W64). + by smt(@W64).
      by smt(@W64).
    by apply H4.
    unroll for {1} 4. unroll for {2} 4.
    auto => />. progress.
    + by rewrite shr_div => />.
    + rewrite shr_div => />. by smt(@W64).
    + rewrite shr_div => />. by smt(@W64).
    + rewrite shr_div => />. by smt(@W64).
    + rewrite shr_div => />. by smt(@W64).
    by rewrite shr_div => />.
  wp;call(_: ={M.leakages,_rhotates_left,_rhotates_right,_iotas} ==> ={M.leakages}).
  proc. + by sim.
  auto => />. progress.
  + move : H5; rewrite ultE => *.
  + move : H0. rewrite !to_uintD_small => />. + by smt(@W64). by smt(@W64).
  + move : H5; rewrite ultE => *. move : H0. by rewrite !to_uintD_small => />.
  + by smt(@W64).
  + move : H3; rewrite /disj_reg => H3. elim H3.
    + move => h1. left. rewrite  (_: (ot + rt + (ol - rt + (of_int 8)%W64)) = (ot + (ol + (of_int 8))%W64)). + by ring. by apply h1.
    move=> h1. right. rewrite (_: to_uint (ot + rt) = to_uint ot + to_uint rt). rewrite to_uintD_small. + by smt(@W64).
    by smt(@W64).
  by smt(@W64).
  + move : H3; rewrite /disj_reg => H3. elim H3. move => h1.
    left. rewrite  (_: (ot + rt + (ol - rt + (of_int 8)%W64)) = (ot + (ol + (of_int 8)%W64))). + by ring. by apply h1.
  + move => *. right. rewrite (_: to_uint (ot + rt) = to_uint ot + to_uint rt).
    + rewrite to_uintD_small. by smt(@W64).
    by smt(@W64).
  by smt(@W64).
  rewrite to_uintB /=. by smt(@W64). by smt(@W64).
+ auto => />. progress. by smt(@W64).
wp;call(_: ={rhotates_left, rhotates_right,iotas,a_jagged, in_0, inlen,rate,M.leakages} /\
             eq_reg Glob.mem{1} Glob.mem{2} (to_uint a_jagged{1}) 224 /\
             to_uint a_jagged{2} + 224 < W64.modulus /\ 0 < to_uint rate{2} < 200
           ==> ={M.leakages}).
+ proc.
  wp; call(_: ={a_jagged,in_0,inlen,rate,M.leakages} /\
                eq_reg Glob.mem{1} Glob.mem{2} (to_uint a_jagged{1}) 224 /\
                to_uint a_jagged{2} + 224 < W64.modulus /\ 0 < to_uint rate{2} < 200 /\
                to_uint inlen{2} < to_uint rate{2}
              ==> ={M.leakages}).
  + proc. while(={i,M.leakages}).
    + by auto => />.
    wp;while(={j,in_0,inlen,M.leakages,l}). + by auto => />.
    wp;while(={j,in_0,inlen8,M.leakages,a_jagged} /\
               to_uint inlen8{2} <= 25 /\ to_uint j{2} <= to_uint inlen8{2} /\
               eq_reg Glob.mem{1} Glob.mem{2} (to_uint a_jagged{1}) 224 /\
               to_uint a_jagged{2} + 224 < W64.modulus /\ to_uint rate{2} < 200).
    + auto => />. rewrite /eq_reg /disj_reg. progress.
      + congr. move : H4; rewrite ultE => *. by apply H1;rewrite to_uintD_small;by smt(@W64).
      by smt(@W64).
    auto => />. progress.
    + congr. move : (H11); rewrite /eq_reg => H14. rewrite H14 => //=.
      rewrite to_uintD_small. + by smt(@W64). by smt(@W64).
    move : (H11); rewrite /eq_reg => H16 //=.
    congr. congr. congr. rewrite H16 => //=.
    split; last first.
    + have hh : (to_uint ((of_int 8)%W64 * (rate{2} - W64.one `>>` (of_int 3)%W8)) < 216).
      + rewrite to_uintM_small.
        have hh: (to_uint (rate{2} - W64.one `>>` (of_int 3)%W8) < 200).
        + rewrite shr_div => />. rewrite to_uintB /=. by smt(@W64).
        by smt(@W64).
      by smt(@W64).
    rewrite shr_div => />. rewrite to_uintB /=. by smt(@W64).
    by smt(@W64).
    move=> /= H'. by smt.
  rewrite to_uintD_small.
  + have hh : (to_uint ((of_int 8)%W64 * (rate{2} - W64.one `>>` (of_int 3)%W8)) < 216).
    + rewrite to_uintM_small.
      have hh: (to_uint (rate{2} - W64.one `>>` (of_int 3)%W8) < 200).
      rewrite shr_div => />. rewrite to_uintB /=. + by smt(@W64). + by smt(@W64).
      + by smt(@W64). + rewrite shr_div => />. rewrite to_uintB /=. by smt(@W64). + by smt(@W64). + by smt(@W64).
      by smt(@W64).
    move : (H11); rewrite /eq_reg => H16 //=. congr. congr. congr. rewrite H16 => //=.
    split; last first.
    + have hh : (to_uint ((of_int 8)%W64 * (rate{2} - W64.one `>>` (of_int 3)%W8)) < 216).
      + rewrite to_uintM_small.
        have hh: (to_uint (rate{2} - W64.one `>>` (of_int 3)%W8) < 200).
        + rewrite shr_div => />. rewrite to_uintB /=. by smt(@W64).
        by smt(@W64).
      by smt(@W64).
    rewrite shr_div => />. rewrite to_uintB /=. + by smt(@W64).
    by smt(@W64).
  by smt(@W64).
  rewrite to_uintD_small.
  + have hh : (to_uint ((of_int 8)%W64 * (rate{2} - W64.one `>>` (of_int 3)%W8)) < 216).
    rewrite to_uintM_small.
    + have hh: (to_uint (rate{2} - W64.one `>>` (of_int 3)%W8) < 200).
      rewrite shr_div => />. + rewrite to_uintB /=. by smt(@W64).
    by smt(@W64).
  by smt(@W64).
  rewrite shr_div => />.
  + rewrite to_uintB /=. + by smt(@W64). by smt(@W64).
  by smt(@W64).
  by smt(@W64).
 inline *.
 unroll for {1} 6.
 unroll for {2} 6.
 auto => />. progress.
 + rewrite shr_div => />. by smt(@W64).
 + rewrite shr_div => />. by smt(@W64).
 + move : (H); rewrite /eq_reg => H7 //=.
   congr. rewrite H7 => //=. rewrite to_uintD_small.
   by smt(@W64).
 + by smt(@W64).
 + congr. move : (H); rewrite /eq_reg => H8 //=.
   congr. rewrite H8 => //=. split.
   + rewrite to_uintD_small.
     have hh : (to_uint ((of_int 8)%W64 * (rate{2} - W64.one `>>` (of_int 3)%W8)) < 224).
     + rewrite to_uintM_small.
       + have hh: (to_uint (rate{2} - W64.one `>>` (of_int 3)%W8) < 200).
         + rewrite shr_div => />. rewrite to_uintB /=. by smt(@W64).
         by smt(@W64).
       by smt(@W64).
     rewrite shr_div => />. rewrite to_uintB /=. by smt(@W64).
     by smt(@W64).
   + by smt(@W64).
   + by smt(@W64).
 + progress. have hh : (to_uint ((of_int 8)%W64 * (rate{2} - W64.one `>>` (of_int 3)%W8)) < 216).
   rewrite to_uintM_small.
   + have hh: (to_uint (rate{2} - W64.one `>>` (of_int 3)%W8) < 200).
     rewrite shr_div => />. rewrite to_uintB /=. by smt(@W64).
   by smt(@W64).
 by smt(@W64).
 rewrite shr_div => />. rewrite to_uintB /=. by smt(@W64).
 + by smt(@W64).
 + by smt(@W64).
 + congr. move : (H); rewrite /eq_reg => H8 //=. congr. rewrite H8 => //=.
   split.
   + rewrite to_uintD_small.
     + have hh : (to_uint ((of_int 8)%W64 * (rate{2} - W64.one `>>` (of_int 3)%W8)) < 216).
       rewrite to_uintM_small.
       + have hh: (to_uint (rate{2} - W64.one `>>` (of_int 3)%W8) < 200).
         + rewrite shr_div => />. rewrite to_uintB /=. by smt(@W64). by smt(@W64).
         by smt(@W64).
       rewrite shr_div => />. rewrite to_uintB. + by smt(@W64). by smt(@W64).
       by smt(@W64).
     by smt(@W64).
   progress. have hh : (to_uint ((of_int 8)%W64 * (rate{2} - W64.one `>>` (of_int 3)%W8)) < 216).
   + rewrite to_uintM_small.
     + have hh: (to_uint (rate{2} - W64.one `>>` (of_int 3)%W8) < 200).
       rewrite shr_div => />. rewrite to_uintB /=. by smt(@W64). by smt(@W64).
     by smt(@W64).
   rewrite shr_div => />. rewrite to_uintB. by smt(@W64). by smt(@W64).
   by smt(@W64).
 wp; while (={M.leakages,rate,inlen,a_jagged,in_0,rhotates_left,rhotates_right,iotas} /\
              to_uint a_jagged{2} + 224 < W64.modulus /\ 0 < to_uint rate{2} < 200 /\
              eq_reg Glob.mem{1} Glob.mem{2} (to_uint a_jagged{1}) 224).
 wp;call(_: ={M.leakages,_rhotates_left,_rhotates_right,_iotas} ==> ={M.leakages}).
 + proc.
   + by sim.
   exists* rate{2}, inlen{2}.
   elim* => rt il.
   wp;call(_: ={M.leakages,rate,inlen,a_jagged,in_0} /\
                rate{2} = rt /\ inlen{2} = il /\
                to_uint a_jagged{2} + 224 < W64.modulus /\ 0 < to_uint rate{2} < 200 /\
                eq_reg Glob.mem{1} Glob.mem{2} (to_uint a_jagged{1}) 224 ==>
                res{1}.`3 = res{2}.`3 /\ res{1}.`4 = res{2}.`4 /\ ={M.leakages} /\
                res{1}.`4 = il - rt).
   + proc. wp; while (={M.leakages,i}).
     + by auto => />.
     wp; while (={j,rate8,M.leakages,a_jagged,in_0} /\ to_uint rate8{2} < 25 /\
                  to_uint a_jagged{2} + 224 < W64.modulus /\ 0 < to_uint rate{2} < 200 /\
                  eq_reg Glob.mem{1} Glob.mem{2} (to_uint a_jagged{1}) 224).
     + auto => />. progress. congr. move : H3;rewrite /eq_reg => H3.
       rewrite H3. + rewrite to_uintD_small => />. by smt(@W64).
       by smt(@W64).
     rewrite to_uintD_small => />. by smt(@W64).
     auto => />. progress. rewrite shr_div => />.
     by smt(@W64).
   auto => />. progress. rewrite !uleE. by smt(@W64).
   rewrite !uleE. by smt(@W64).
 rewrite !uleE. by smt(@W64).
wp; inline *; rewrite /=; auto.
unroll for {1} 7. unroll for {2} 7.
auto => />. progress. move : H3; rewrite uleE; by smt(@W64).
inline *. unroll for {1} 8. unroll for {2} 8. by auto => />.
qed.
