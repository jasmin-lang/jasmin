require import AllCore IntDiv List Jasmin_model Chacha20_hacl Chacha20_hacl_x2 Chacha20_s_avx2.

(* --------------------------------------------------------------------------- *)
(* First we prove that the hacl implementation correspond to the hacl_x2       *)
(* implementation. The last one allows to express most easyly the invariant    *)
(* for the s-avx version                                                       *)

equiv hacl_x2_quarter_round : 
  Chacha20_hacl.M.hacl_Impl_Chacha20_quarter_round ~
  Chacha20_hacl_x2.M.hacl_Impl_Chacha20_quarter_round : ={arg} ==> ={res}.
proof. by sim. qed.

equiv hacl_x2_rounds_x2 : 
  Chacha20_hacl.M.hacl_Impl_Chacha20_rounds_x2 ~
  Chacha20_hacl_x2.M.hacl_Impl_Chacha20_rounds_x2 : 
    ={k1,k2} ==> ={res}.
proof.
  proc=> /=.
  inline{1} Chacha20_hacl.M.hacl_Impl_Chacha20_rounds.
  (* One solution is to unroll the loop and then perform some 
     swap, I prefer to do the proof by induction so that 
     the proof do not depend of the number of iteration *)
  swap{1} 4 3. swap{1} 4 -2. swap{1} 5 -1. wp.
  seq 4 1 : (exists k, 0 <= k /\  
       10 - i{1} = k /\ i0{1} = i{1} /\ i{2} = i{1} /\ #post).
  + by auto => />;exists 10.
  elim * => k;case @[ambient] (0 <= k); last by move=> ?; exfalso => /#.
  elim /intind: k.
  + rcondf{1} 1; 1: by auto => /#.
    rcondf{1} 1; 1: by auto => /#.
    by rcondf{2} 1;auto => /#.
  move=> k hk hrec.
  rcondt{1} 1; 1: by auto => /#.
  rcondt{2} 1; 1: by auto => /#.
  rcondt{1} 4.
  + move=> &2;conseq (_: true) => // /#.
  swap{1} 4 -2; swap{1} 5 -1.
  seq 4 2: (10 - i{1} = k /\
    i0{1} = i{1} /\ i{2} = i{1} /\ st{1} = k1{2} /\ st0{1} = k2{2});last by apply hrec.
  inline{1} Chacha20_hacl.M.hacl_Impl_Chacha20_double_round.
  inline{2} Chacha20_hacl_x2.M.hacl_Impl_Chacha20_double_round_x2.
  swap{1} [6..10] 5.
  inline{2} Chacha20_hacl_x2.M.hacl_Impl_Chacha20_round_x2.
  by do !(wp;call hacl_x2_quarter_round);
    wp;skip => /> &1 h; ring h.
qed.

equiv hacl_x2_double : 
  Chacha20_hacl.M.hacl_2rounds ~
  Chacha20_hacl_x2.M.hacl_2rounds : 
   ={st1,st2} ==> ={res}.
proof.
  proc => /=; sim; call hacl_x2_rounds_x2; sim />.
qed.

(* --------------------------------------------------------------------------- *)

hint simplify (x86_ROL_32_E, W32.rol_xor_simplify).

(* --------------------------------------------------------------------------- *)
(* hacl-x2 versus s-avx2                                                       *)

lemma x86_VPSHUFD_256_E (w0 w1 w2 w3 w4 w5 w6 w7 :W32.t) m :
  x86_VPSHUFD_256 (pack8 [w0; w1; w2; w3; w4; w5; w6; w7]) m = 
  pack2 [x86_VPSHUFD_128 (pack4 [w0; w1; w2; w3]) m;
         x86_VPSHUFD_128 (pack4 [w4; w5; w6; w7]) m].
proof. by rewrite /x86_VPSHUFD_256 -pack2_4u32_8u32. qed.

hint simplify (x86_VPSHUFD_256_E, pack2_4u32_8u32).

op rela_i k i (st1 st2:W32.t Array16.t) =
  pack8 [ 
          st1.[4*i+(0+k)%%4]; st1.[4*i+(1+k)%%4]; st1.[4*i+(2+k)%%4]; st1.[4*i+(3+k)%%4];
          st2.[4*i+(0+k)%%4]; st2.[4*i+(1+k)%%4]; st2.[4*i+(2+k)%%4]; st2.[4*i+(3+k)%%4] ].

op rela (st1 st2:W32.t Array16.t) (s:W256.t Array4.t) =
   s = Array4.init (fun i => rela_i 0 i st1 st2).

(*
op rela_after (st1 st2:W32.t Array16.t) (s:W256.t Array4.t) = 
   s = Array4.init (fun i => rela_i i i st1 st2).
*)

equiv s_avx2_double_round : 
  Chacha20_hacl_x2.M.hacl_Impl_Chacha20_double_round_x2 ~ 
  Chacha20_s_avx2.M.chacha20_double_round : 
    rela st1{1} st2{1} st{2} ==> rela res{1}.`1 res{1}.`2 res{2}.
proof.
  proc.
  seq 1 1: (rela st1{1} st2{1} st{2}).
  + conseq (: Array4.all_eq st{2}
                (Array4.init (fun i => rela_i 0 i st1 st2)){1}). 
    + by move=> ?????? h;apply Array4.ext_eq_all;apply h. 
    inline *; wp;skip=> &1 &2 h.
    rewrite $h.
    by cbv Array4.all_eq rela_i x86_VPADD_8u32 x86_VPSRL_8u32 x86_VPSLL_8u32 (%%) (%/)
         W32.(`>>`) W32.(`<<`) => /=.
  conseq (: Array4.all_eq st{2}
              (Array4.init (fun i => rela_i 0 i st1 st2)){1}). 
  + by move=> ?????? h;apply Array4.ext_eq_all;apply h. 
  inline *; wp;skip=> &1 &2 h.
  rewrite $h.
  by cbv Array4.all_eq rela_i x86_VPADD_8u32 x86_VPSRL_8u32 x86_VPSLL_8u32 (%%) (%/)
         W32.(`>>`) W32.(`<<`) x86_VPSHUFD_128 x86_VPSHUFD_128_B => /=.
qed.

equiv s_avx2_chacha20_rounds :
  Chacha20_hacl_x2.M.hacl_Impl_Chacha20_rounds_x2 ~
  Chacha20_s_avx2.M.chacha20_rounds :
   rela k1{1} k2{1} st{2} ==> rela res{1}.`1 res{1}.`2 res{2}.
proof.
  proc.
  while (={i} /\ rela k1{1} k2{1} st{2});last by auto.
  by wp; call s_avx2_double_round;skip.
qed.

equiv s_avx2_copy_states : 
  Chacha20_hacl_x2.M.hacl_Impl_Chacha20_copy_state_x2 ~ 
  Chacha20_s_avx2.M.chacha20_copy_state : 
    rela st1{1} st2{1} s{2} ==> rela res{1}.`1 res{1}.`2 res{2}.
proof.
  proc;inline *.
  unroll for {1} 11;unroll for {1} 6.
  unroll for {2} 3;wp;skip => />.
  move=> &1 &2 ->;rewrite /rela;apply Array4.ext_eq_all.
  by cbv Array4.all_eq rela_i (%%) (%/).
qed.

equiv s_avx2_sum_states : 
  Chacha20_hacl_x2.M.hacl_Impl_Chacha20_sum_states_x2 ~ 
  Chacha20_s_avx2.M.chacha20_sum_states : 
    rela k1{1} k2{1} k{2} /\
    rela st1{1} st2{1} s{2} ==> rela res{1}.`1 res{1}.`2 res{2}.
proof.
  proc;inline *.
  unroll for {1} 9;unroll for {1} 4.
  unroll for {2} 2;wp;skip => &1 &2 /= /> -> ->.
  apply Array4.ext_eq_all.  
  by cbv Array4.all_eq rela_i x86_VPADD_8u32 (%%) (%/).
qed.

equiv s_avx2_2rounds : 
  Chacha20_hacl_x2.M.hacl_2rounds ~
  Chacha20_s_avx2.M.avx2_2rounds : 
   rela st1{1} st2{1} s{2} ==> rela res{1}.`1 res{1}.`2 res{2}.
proof.
  proc => /=.
  call s_avx2_sum_states.
  call s_avx2_chacha20_rounds.
  by call s_avx2_copy_states;wp;skip.
qed.


(* ------------------------------------------------------------ *)

equiv hacl_s_avx2_2rounds : 
  Chacha20_hacl.M.hacl_2rounds ~
  Chacha20_s_avx2.M.avx2_2rounds : 
   rela st1{1} st2{1} s{2} ==> rela res{1}.`1 res{1}.`2 res{2}.
proof.
  transitivity Chacha20_hacl_x2.M.hacl_2rounds
    (={st1,st2} ==> ={res}) 
    (rela st1{1} st2{1} s{2} ==> rela res{1}.`1 res{1}.`2 res{2}) => //.
  + by move=> &1 &2 h;exists (st1{1}, st2{1}).
  + by apply hacl_x2_double.
  by apply s_avx2_2rounds.
qed.

