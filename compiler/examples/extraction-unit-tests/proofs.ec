require import AllCore IntDiv List.
from Jasmin require import JUtils JWord JMemory.

require Gcd.
require Loops.
require Sdiv.
require Add_in_mem.
require String.

lemma loops_forty_correct : hoare [ Loops.M.forty: true ==> res = W32.of_int 40 ].
proof. by proc; unroll for ^while; auto. qed.

lemma loops_for_nest_correct : hoare [ Loops.M.for_nest: true ==> res = W32.of_int 2000 ].
proof.
  proc; wp.
  while (0 <= i <= inc /\ k = 100 * i).
  - wp.
    while (0 <= j <= inc_0 /\ k = 100 * i + j); auto => &m /> j_ge0 _ j_lt_inc0.
    + rewrite addzA /= -ltzE j_lt_inc0 /=.
      apply: (lez_trans _ _ _ j_ge0).
      by rewrite lez_addl /=.
    move => k ? _ ?.
    have -> : k = 100; smt().
  auto => /#.
qed.

lemma sdiv_correct : hoare [ Sdiv.M.main: true ==> res = (W64.of_int (-1), W64.of_int (-1)) ].
proof.
  proc; auto => _ _.
  rewrite sdivE smodE /slift2 /(\zquot) /(\zrem) /zsign.
  do 4! (rewrite to_sintK_small; first done).
  done.
qed.

hoare euclid_correct x y :
  Gcd.M.euclid : x = a /\ y = b ==> `|res| = gcd x y.
proof.
  proc.
  while (gcd a b = gcd x y).
  - auto => &m /> ih a_nz.
    by rewrite gcd_modl gcdC.
  skip => &m [] /= <- <- _ g' ->.
  by rewrite gcd0z.
qed.

(* ------------------------------------------------ *)
hoare string_correct :
  String.M.main : true ==> res = W32.of_int 16416.
proof. by proc; auto => />; rewrite to_uint_eq !(to_uintD, to_uint_shl, of_uintK). qed.

(* ------------------------------------------------ *)

op to_list (m:global_mem_t) (p len : int) =
  map (fun i => loadW64 m (p + 8*i)) (iota_ 0 len).

lemma size_to_list m p len : 0 <= len => size (to_list m p len) = len.
proof. rewrite /to_list size_map size_iota /#. qed.

lemma to_list0 m p : to_list m p 0 = [].
proof. by rewrite /to_list iota0. qed.

lemma to_listS m p len : 0 <= len => to_list m p (len + 1) = rcons (to_list m p len) (loadW64 m (p + 8*len)).
proof. by move=> ?; rewrite /to_list iotaSr // map_rcons. qed.

op addl (l1 l2 : W64.t list) = map (fun (p:W64.t * W64.t) => p.`1 + p.`2) (zip l1 l2).

lemma addl_rcons l1 l2 w1 w2 :
  size l1 = size l2 => addl (rcons l1 w1) (rcons l2 w2) = rcons (addl l1 l2) (w1 + w2).
proof. by move=> heq; rewrite /addl zip_rcons // map_rcons. qed.

op disjoint_ptr (out inp len : int) = out <= inp || inp + len <= out .

hoare add_mem_correct (m_ : global_mem_t) (out_ in1_ in2_ len_ : int) :
  Add_in_mem.M.add_mem :
    Glob.mem = m_ /\ out = out_ /\ in1 = in1_ /\ in2 = in2_ /\ len = len_ /\
    disjoint_ptr out in1 (8*len) /\ disjoint_ptr out in2 (8*len)
    ==>
    to_list Glob.mem out_ len_ = addl (to_list m_ in1_ len_) (to_list m_ in2_ len_).
proof.
  proc.
  case: (len <= 0).
  + rcondf ^while; auto => />; 1: by smt().
    by move=> _ _ hlen; rewrite /to_list iota0.
  while (0 <= i <= len /\
         out = out_ /\ in1 = in1_ /\ in2 = in2_ /\ len = len_ /\
         disjoint_ptr out in1 (8*len) /\ disjoint_ptr out in2 (8*len) /\
         (forall j, i <= j < len => loadW64 Glob.mem (in1 + 8*j) = loadW64 m_ (in1 + 8*j) /\
                                    loadW64 Glob.mem (in2 + 8*j) = loadW64 m_ (in2 + 8*j)) /\
         to_list Glob.mem out_ i = addl (to_list m_ in1_ i) (to_list m_ in2_ i)).
  + auto => /> &hr h0i _ hdisj1 hdisj2 heqm_ hrec hilen.
    rewrite !to_listS // addl_rcons 1:!size_to_list // -hrec; split; 1: smt().
    split.
    + move=> j hij hj; rewrite !store_load64_neq 1, 2:/#.
      apply: heqm_; smt().
    congr.
    + apply List.eq_in_map => j /mem_iota hj /=; rewrite store_load64_neq; smt().
    by rewrite store_load64_eq; have [-> ->]:= heqm_ i{hr} _.
  auto => />; smt (to_list0).
qed.
