(* This file is the second part of [stack_alloc_proof_1.v] that was split to
   ease the development process.
*)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
From mathcomp Require Import ssralg.
From mathcomp Require Import word_ssrZ.
Require Import Uint63.
Require Import psem psem_facts compiler_util.
Require Export stack_alloc stack_alloc_proof_1.
From mathcomp Require Import ring.
From Coq Require Import Utf8 Lia.

Local Open Scope seq_scope.
Local Open Scope Z_scope.

(* When the boolean is set to false, some checks are disable. On the Coq side,
   we want to perform all the checks, so we set it to true.
*)
Notation alloc_fd   := (alloc_fd true).
Notation alloc_i    := (alloc_i true).
Notation alloc_prog := (alloc_prog true).

Section INIT.

Variable global_data : seq u8.
Variable global_alloc : seq (var * wsize * Z).

Let glob_size := Z.of_nat (size global_data).

Context
  {wsw : WithSubWord}
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  (rip : pointer)
  (no_overflow_glob_size : no_overflow rip glob_size)
  (mglob : Mvar.t (Z * wsize))
  (P : uprog) (ev: @extra_val_t progUnit)
  (hmap : init_map global_alloc global_data (p_globs P) = ok mglob).

Notation gd := (p_globs P).

Lemma ztakeP (A:Type) z (l l1 l2:list A) :
  ztake z l = Some(l1, l2) -> l = l1 ++ l2 /\ size l1 = Z.to_nat z.
Proof.
  case: z => //= [ [<- <-] // | p ].
  case heq: (ptake p [::] l) => [ [r l2']| //].
  move=> [<- <- {l1 l2}].
  suff : rev [::] ++ l = rev r ++ l2' ∧ size (rev r) = (Pos.to_nat p + size (@nil A))%nat.
  + by rewrite /= addn0.
  elim: p [::] l r l2' heq => /= [p hp | p hp | ] acc l r l2.
  + case: l => // x l.
    case: ptake (hp (x::acc) l) => // -[r1 l21] /(_ _ _ erefl) [h1 h2] /hp [h3 h4].
    rewrite -cat_rcons -rev_cons h1 h3 h4 -(size_rev r1) h2; split => //=.
    rewrite Pos2Nat.inj_xI.
    change ((Pos.to_nat p + (Pos.to_nat p + (size acc).+1))%nat = ((2 * Pos.to_nat p).+1 + size acc)%nat); ring.
  + case: ptake (hp acc l) => // -[r1 l21] /(_ _ _ erefl) [h1 h2] /hp [h3 h4].
    rewrite h1 h3 h4 -(size_rev r1) h2; split => //=.
    rewrite Pos2Nat.inj_xO.
    change ((Pos.to_nat p + (Pos.to_nat p + (size acc)))%nat = ((2 * Pos.to_nat p) + size acc)%nat); ring.
  by case: l => // x l [<- <-]; rewrite rev_cons cat_rcons size_rcons size_rev.
Qed.

Lemma check_globP data gv tt :
  check_glob data gv = ok tt -> size data = Z.to_nat (size_glob gv) ->
  forall k w, get_val_byte (gv2val gv) k = ok w -> nth 0%R data (Z.to_nat k) = w.
Proof.
  case: gv; rewrite /check_glob.
  + move=> ws s; t_xrbindP => /eqP <- hsz k w /=.
    case:ifP => // ? [] <-.
    rewrite /LE.wread8; f_equal.
    apply (LE.decode_inj (sz:=ws)) => //.
    + by rewrite LE.size_encode.
    by rewrite LE.decodeK.
  move=> p t /=.
  set test := λ (wd : u8) (i : Z),
       match read t Aligned i U8 with
       | ok _ w => if wd == w then ok (i + 1) else Error (E.stk_ierror_no_var "bad decode array eq")
       | Error _ => Error (E.stk_ierror_no_var "bad decode array len")
       end.
  t_xrbindP => z hf _ hsz.
  assert (H : forall data' i l z,
    foldM test i data' = ok z →
    data = l ++ data' →
    Z.of_nat (size l) = i →
    (∀ (k : Z) (w : u8), 0%Z <= k < i -> read t Aligned k U8 = ok w → (data`_(Z.to_nat k))%R = w) →
    ∀ (k : Z) (w : u8), read t Aligned k U8 = ok w → (data`_(Z.to_nat k))%R = w); last first.
  + by move=> hfold hsize; apply (H data 0%Z [::] z) => //; lia.
  move=> {z hf }; elim => [ | w data' hrec] i l z /=.
  + rewrite cats0 => _ <- <- h k w hr.
    have /= ? := @get_val_byte_bound (Varr t) k _ hr.
    by apply h => //; rewrite hsz positive_nat_Z.
  rewrite {2}/test; t_xrbindP => i'.
  case heq: read => [ wp | ] //.
  case: eqP => [? | //] [?] h heq' hi hr; subst wp i' i.
  apply (hrec _ (rcons l w) _ h).
  + by rewrite cat_rcons.
  + by rewrite size_rcons Nat2Z.inj_succ.
  move=> k w0 hk.
  case (k =P  Z.of_nat (size l)) => [-> | ].
  + by rewrite heq heq' Nat2Z.id => -[<-]; rewrite nth_cat ltnn subnn.
  move=> ?; apply hr; lia.
Qed.

Lemma init_mapP : forall x1 ofs1 ws1,
  Mvar.get mglob x1 = Some (ofs1, ws1) -> [/\
    ofs1 mod wsize_size ws1 = 0,
    0 <= ofs1 /\ ofs1 + size_slot x1 <= glob_size,
    (forall gv, get_global_value gd x1 = Some gv ->
                forall k w, get_val_byte (gv2val gv) k = ok w ->
                            nth 0%R global_data (Z.to_nat (ofs1 + k)) = w) &
    (forall x2 ofs2 ws2,
      Mvar.get mglob x2 = Some (ofs2, ws2) -> x1 <> x2 ->
      ofs1 + size_slot x1 <= ofs2 \/ ofs2 + size_slot x2 <= ofs1)].
Proof.
  move: hmap; rewrite /init_map.
  t_xrbindP=> -[[mglob' size] data'] hfold; t_xrbindP => /= _ ? x1 ofs1 ws1 hget; subst mglob'.
  move: hfold x1 ofs1 ws1 hget.
  have : [/\
    0 <= (Mvar.empty (Z * wsize), 0, global_data).1.2,
    (exists l, seq.size l = Z.to_nat (Mvar.empty (Z * wsize), 0, global_data).1.2 /\
       global_data = l ++ (Mvar.empty (Z * wsize), 0, global_data).2) &
    forall x1 ofs1 ws1,
    Mvar.get (Mvar.empty (Z * wsize), 0, global_data).1.1 x1 = Some (ofs1, ws1) -> [/\
    ofs1 mod wsize_size ws1 = 0,
    0 <= ofs1 /\ ofs1 + size_slot x1 <= (Mvar.empty (Z * wsize), 0, global_data).1.2,
    (forall gv, get_global_value gd x1 = Some gv ->
                forall k w, get_val_byte (gv2val gv) k = ok w ->
                            nth 0%R global_data (Z.to_nat (ofs1 + k)) = w) &
    (forall x2 ofs2 ws2,
       Mvar.get (Mvar.empty (Z * wsize), 0, global_data).1.1 x2 = Some (ofs2, ws2) -> x1 <> x2 ->
       ofs1 + size_slot x1 <= ofs2 \/ ofs2 + size_slot x2 <= ofs1)]].
  + by split => //; exists [::].
  elim: global_alloc (Mvar.empty _, 0, global_data).
  + move=> [[mglob0 size0] data0] /= [] ? [l [hsize heq]] hbase2 [???]; subst mglob0 size0 data0.
    move=> ??? /hbase2 [????]; split=> //.
    rewrite /glob_size heq size_cat hsize Nat2Z.inj_add Z2Nat.id //.
    by lia.
  move=> [[x wsx] ofsx] l ih [[mglob0 size0] data0] /= [hbase1 [l0 [heqsz heq]] hbase2].
  t_xrbindP=> -[[mglob1 size1] data1].
  case: ZleP => [h1|//].
  case: eqP => [h2|//].
  case heqt : (ztake (ofsx - size0) data0) => [[rdata ldata] | //].
  case heqt' : (ztake (size_slot x) ldata) => [[vdata data] | //].
  rewrite -/(get_global_value gd x).
  case heqg: (get_global_value gd x) => [gv | //].
  t_xrbindP => /eqP heqszg hcheck ???; subst data1 size1 mglob1.
  apply ih.
  have [? hsz1] := ztakeP heqt; subst data0.
  have [? hsz2] := ztakeP heqt'; subst ldata.
  split=> /=.
  + by have := size_slot_gt0 x; lia.
  + exists (l0 ++ rdata ++ vdata).
    rewrite heq -!catA; split => //.
    have ? := size_slot_gt0 x.
    rewrite -Nat2Z.inj_iff !size_cat !Nat2Z.inj_add Z2Nat.id //; last by lia.
    by rewrite hsz1 hsz2 heqsz !Z2Nat.id //; first ring; lia.
  move=> x1 ofs1 ws1.
  rewrite Mvar.setP.
  case: eqP => [|_].
  + move=> <- [<- <-].
    split.
    + by rewrite -Zland_mod.
    + by lia.
    + rewrite heqg => _ [<-].
      move=> k w hget; rewrite heq.
      have ? := get_val_byte_bound hget.
      rewrite /= Z2Nat.inj_add; last first. + lia. + lia.
      rewrite catA nth_cat.
      have heqo : Z.to_nat ofsx = seq.size (l0 ++ rdata).
      + rewrite size_cat heqsz hsz1 Z2Nat.inj_sub // subnKC //.
        by apply /leP; apply Z2Nat.inj_le => //; lia.
      have /negP/negbTE-> : ~((Z.to_nat ofsx + Z.to_nat k)%coq_nat < seq.size (l0 ++ rdata))%nat.
      + by rewrite -heqo => /ltP; lia.
      rewrite -heqo sub_nmn.
      have hh : seq.size vdata = Z.to_nat (size_glob gv) by rewrite hsz2 heqszg.
      have := check_globP hcheck hh hget.
      rewrite nth_cat.
      have ? : size_glob gv = size_val (gv2val gv) by case: (gv).
      have -> // : (Z.to_nat k < seq.size vdata)%nat.
      by apply/ltP; rewrite Nat2Z.inj_lt hsz2 !Z2Nat.id; lia.
    move=> x2 ofs2 ws2.
    rewrite Mvar.setP.
    case: eqP => [//|_].
    by move=> /hbase2 [_ ? _] _; right; lia.
  move=> /hbase2 [???]; split=> //.
  + by have := size_slot_gt0 x; lia.
  move=> x2 ofs2 ws2.
  rewrite Mvar.setP.
  case: eqP; last by eauto.
  by move=> <- [<- _] _; left; lia.
Qed.

Lemma init_map_align x1 ofs1 ws1 :
  Mvar.get mglob x1 = Some (ofs1, ws1) -> ofs1 mod wsize_size ws1 = 0.
Proof. by move=> /init_mapP [? _ _]. Qed.

Lemma init_map_bounded x1 ofs1 ws1 :
  Mvar.get mglob x1 = Some (ofs1, ws1) ->
  0 <= ofs1 /\ ofs1 + size_slot x1 <= glob_size.
Proof. by move=> /init_mapP [_ ? _]. Qed.

Lemma init_map_full : forall x gv,
  get_global_value gd x = Some gv ->
  exists ofs ws, Mvar.get mglob x = Some (ofs, ws).
Proof.
  move: hmap; rewrite /init_map.
  t_xrbindP=> -[[mglob' size] data'] hfold; t_xrbindP => /= /SvD.F.subset_iff hsub ? x gv h; subst mglob'.
  move: hfold.
  have : x \in (map (fun t => t.1.1) global_alloc) \/
         ∃ (ofs : Z) (ws : wsize), Mvar.get (Mvar.empty (Z * wsize), 0, global_data).1.1 x = Some (ofs, ws).
  + left; apply /sv_of_listP/hsub/sv_of_listP.
    by apply: assoc_mem_dom' h.
  elim: global_alloc (Mvar.empty (Z * wsize), 0, global_data) => /=.
  + by move=> p [] // [ofs [ws ?]] [?]; subst p; exists ofs, ws.
  move=> [[ x1 ws] z] glob_alloc ih [[mvar pos] data] hx1.
  t_xrbindP => -[[mvar1 pos1] data1]; case: ZleP => // ?.
  case: ifP => // ?.
  case: ztake => // -[_ data0].
  case: ztake => // -[vdata data2].
  case: assoc => // gv1; t_xrbindP => ?????.
  apply ih; case: hx1.
  + rewrite in_cons => /orP [/eqP | ] /= ?; subst; last by left.
    by right; exists z, ws; rewrite Mvar.setP eqxx.
  move=> ?; subst; right.
  rewrite Mvar.setP; case: eqP => // *; by exists z, ws.
Qed.

Lemma check_globsP g gv :
  get_global_value gd g = Some gv ->
  exists ofs ws,
    Mvar.get mglob g = Some (ofs, ws) /\
    forall k w,
      get_val_byte (gv2val gv) k = ok w ->
      nth 0%R global_data (Z.to_nat (ofs + k)) = w.
Proof.
  move=> h; move: (h) => /init_map_full [ofs [ws hget]].
  exists ofs, ws; split => //.
  have [_ _ h1 _] := init_mapP hget.
  apply (h1 _ h).
Qed.

Section LOCAL.

Variable sao : stk_alloc_oracle_t.
Variable stack : Mvar.t (Z * wsize).

Hypothesis hlayout : init_stack_layout mglob sao = ok stack.

Lemma init_stack_layoutP :
  [/\ 0 <= sao.(sao_ioff),
      sao.(sao_ioff) <= sao.(sao_size) &
      forall x1 ofs1 ws1,
        Mvar.get stack x1 = Some (ofs1, ws1) -> [/\
          (ws1 <= sao.(sao_align))%CMP,
          ofs1 mod wsize_size ws1 = 0,
          sao.(sao_ioff) <= ofs1 /\ ofs1 + size_slot x1 <= sao.(sao_size),
          (forall x2 ofs2 ws2,
            Mvar.get stack x2 = Some (ofs2, ws2) -> x1 <> x2 ->
            ofs1 + size_slot x1 <= ofs2 \/ ofs2 + size_slot x2 <= ofs1) &
          Mvar.get mglob x1 = None]].
Proof.
  move: hlayout; rewrite /init_stack_layout.
  t_xrbindP=> /ZleP hioff -[stack' size] hfold.
  rewrite zify.
  case: ZleP => [hle|//] [?]; subst stack'.
  have: sao.(sao_ioff) <= size /\
    forall x1 ofs1 ws1,
    Mvar.get stack x1 = Some (ofs1, ws1) -> [/\
      (ws1 ≤ sao_align sao)%CMP, ofs1 mod wsize_size ws1 = 0,
      sao.(sao_ioff) <= ofs1 /\ ofs1 + size_slot x1 <= size,
      (forall x2 ofs2 ws2,
        Mvar.get stack x2 = Some (ofs2, ws2) -> x1 <> x2 ->
        ofs1 + size_slot x1 <= ofs2 \/ ofs2 + size_slot x2 <= ofs1) &
      Mvar.get mglob x1 = None];
  last first.
  + move=> [h1 h2]; split => //; first by lia.
    by move=> x1 ofs1 ws1 /h2 [?????]; split=> //; lia.
  move: hfold.
  have: sao.(sao_ioff) <= (Mvar.empty (Z * wsize), sao.(sao_ioff)).2 /\
    forall x1 ofs1 ws1,
    Mvar.get (Mvar.empty (Z * wsize), sao.(sao_ioff)).1 x1 = Some (ofs1, ws1) -> [/\
      (ws1 <= sao.(sao_align))%CMP,
      ofs1 mod wsize_size ws1 = 0,
      sao.(sao_ioff) <= ofs1 /\ ofs1 + size_slot x1 <= (Mvar.empty (Z * wsize), sao.(sao_ioff)).2,
      (forall x2 ofs2 ws2,
        Mvar.get (Mvar.empty (Z * wsize), sao.(sao_ioff)).1 x2 = Some (ofs2, ws2) -> x1 <> x2 ->
        ofs1 + size_slot x1 <= ofs2 \/ ofs2 + size_slot x2 <= ofs1) &
      Mvar.get mglob x1 = None].
  + by split => //=; apply Z.le_refl.
  elim: sao.(sao_slots) (Mvar.empty _, sao.(sao_ioff)).
  + by move=> [stack0 size0] /= hbase [<- <-].
  move=> [[x wsx] ofsx] l ih [stack0 size0] /= [hbase1 hbase2].
  t_xrbindP=> -[stack1 size1].
  case: Mvar.get => //.
  case heq: Mvar.get => //.
  case: ifP => [|//]; rewrite zify => /ZleP h1.
  case: ifP => [h2|//].
  case: eqP => [h3|//].
  move=> [<- <-].
  apply ih.
  split=> /=.
  + by have := size_slot_gt0 x; lia.
  move=> x1 ofs1 ws1.
  rewrite Mvar.setP.
  case: eqP => [|_].
  + move=> <- [<- <-].
    split=> //.
    + by rewrite -Zland_mod.
    + by lia.
    move=> x2 ofs2 ws2.
    rewrite Mvar.setP.
    case: eqP => [|_]; first by congruence.
    by move=> /hbase2 [_ _ ? _]; lia.
  move=> /hbase2 /= [????]; split=> //.
  + by have := size_slot_gt0 x; lia.
  move=> x2 ofs2 ws2.
  rewrite Mvar.setP.
  case: eqP; last by eauto.
  by move=> <- [<- _]; lia.
Qed.

Lemma init_stack_layout_size_ge0 : 0 <= sao.(sao_size).
Proof. by have [? ? _] := init_stack_layoutP; lia. Qed.

Lemma init_stack_layout_stack_align x1 ofs1 ws1 :
  Mvar.get stack x1 = Some (ofs1, ws1) -> (ws1 <= sao.(sao_align))%CMP.
Proof. by have [_ _ h] := init_stack_layoutP => /h [? _ _ _ _]. Qed.

Lemma init_stack_layout_align x1 ofs1 ws1 :
  Mvar.get stack x1 = Some (ofs1, ws1) -> ofs1 mod wsize_size ws1 = 0.
Proof. by have [_ _ h] := init_stack_layoutP => /h [_ ? _ _ _]. Qed.

Lemma init_stack_layout_bounded_ioff x1 ofs1 ws1 :
  Mvar.get stack x1 = Some (ofs1, ws1) ->
  sao.(sao_ioff) <= ofs1 /\ ofs1 + size_slot x1 <= sao.(sao_size).
Proof. by have [_ _ h] := init_stack_layoutP => /h [_ _ ? _ _]. Qed.

Lemma init_stack_layout_bounded x1 ofs1 ws1 :
  Mvar.get stack x1 = Some (ofs1, ws1) ->
  0 <= ofs1 /\ ofs1 + size_slot x1 <= sao.(sao_size).
Proof. have [? _ h] := init_stack_layoutP => /h [_ _ ? _ _]; lia. Qed.

Lemma init_stack_layout_disjoint x1 ofs1 ws1 :
  Mvar.get stack x1 = Some (ofs1, ws1) ->
  forall x2 ofs2 ws2,
    Mvar.get stack x2 = Some (ofs2, ws2) -> x1 <> x2 ->
    ofs1 + size_slot x1 <= ofs2 \/ ofs2 + size_slot x2 <= ofs1.
Proof. by have [_ _ h] := init_stack_layoutP => /h [_ _ _ ? _]. Qed.

Lemma init_stack_layout_not_glob x1 ofs1 ws1 :
  Mvar.get stack x1 = Some (ofs1, ws1) -> Mvar.get mglob x1 = None.
Proof. by have [_ _ h] := init_stack_layoutP => /h [_ _ _ _ ?]. Qed.

(* We pack the hypotheses about slots in a record for the sake of simplicity. *)
Record wf_Slots (Slots : Sv.t) Addr (Writable:slot-> bool) Align := {
  wfsl_no_overflow : forall s, Sv.In s Slots -> no_overflow (Addr s) (size_slot s);
  wfsl_disjoint : forall s1 s2, Sv.In s1 Slots -> Sv.In s2 Slots -> s1 <> s2 ->
    Writable s1 -> disjoint_zrange (Addr s1) (size_slot s1) (Addr s2) (size_slot s2);
  wfsl_align : forall s, Sv.In s Slots -> is_align (Addr s) (Align s);
  wfsl_not_glob : forall s, Sv.In s Slots -> Writable s ->
    0 < glob_size -> disjoint_zrange rip glob_size (Addr s) (size_slot s)
}.

Variable rsp : pointer.
Hypothesis no_overflow_size : no_overflow rsp sao.(sao_size).
Hypothesis disjoint_zrange_globals_locals :
  0 < glob_size -> 0 < sao.(sao_size) ->
  disjoint_zrange rip glob_size rsp sao.(sao_size).
Hypothesis rip_align : is_align rip U256.
  (* could be formulated [forall ws, is_align rip ws] (cf. extend_mem) *)
Hypothesis rsp_align : is_align rsp sao.(sao_align).

Definition Slots_slots (m : Mvar.t (Z * wsize)) :=
  SvP.MP.of_list (map fst (Mvar.elements m)).

Lemma in_Slots_slots m s :
  Sv.In s (Slots_slots m) <-> Mvar.get m s <> None.
Proof.
  rewrite /Slots_slots; split.
  + move=> /SvP.MP.of_list_1 /SetoidList.InA_alt.
    move=> [_ [<- /InP /mapP]].
    move=> [[s' ?]] /Mvar.elementsP /= ??; subst s'.
    by congruence.
  move=> hget.
  apply SvP.MP.of_list_1; apply SetoidList.InA_alt.
  exists s; split=> //.
  apply /InP; apply /mapP.
  case heq: (Mvar.get m s) => [ofs_align|//].
  exists (s, ofs_align) => //.
  by apply /Mvar.elementsP.
Qed.

Definition Offset_slots (m : Mvar.t (Z * wsize)) s :=
  match Mvar.get m s with
  | Some (ofs, _) => ofs
  | _ => 0
  end.

Definition Align_slots (m : Mvar.t (Z * wsize)) s :=
  match Mvar.get m s with
  | Some (_, ws) => ws
  | _ => U8
  end.

Definition Slots_globals := Slots_slots mglob.
Definition Addr_globals s := (rip + wrepr _ (Offset_slots mglob s))%R.
Definition Writable_globals (s:slot) := false.
Definition Align_globals := Align_slots mglob.

Definition Slots_locals := Slots_slots stack.
Definition Addr_locals s := (rsp + wrepr _ (Offset_slots stack s))%R.
Definition Writable_locals (s:slot) := true.
Definition Align_locals := Align_slots stack.

Variable params : seq var_i.
Variables vargs1 vargs2 : seq value.
Variable scs1 : syscall_state.
Variable m1 m2 : mem.

Hypothesis Hargs :
  wf_args glob_size rip m1 m2
    (map (omap pp_writable) sao.(sao_params))
    (map (oapp pp_align U8) sao.(sao_params))
    vargs1 vargs2.
Hypothesis Huincl :
  Forall3 (value_eq_or_in_mem m2) sao.(sao_params) vargs1 vargs2.
Hypothesis Hsub :
  Forall3
    (fun opi (x:var_i) v => opi <> None -> subtype x.(vtype) (type_of_val v))
    sao.(sao_params) params vargs1.

Definition param_tuples :=
  let s := zip params (zip sao.(sao_params) (zip vargs1 vargs2)) in
  pmap (fun '(x, (opi, (v1, v2))) =>
    omap (fun pi => (x.(v_var), (pi, (v1, v2)))) opi) s.

Definition Slots_params := SvP.MP.of_list (map fst param_tuples).

(* For a parameter slot [s], [get_pi] returns the param_info and the two values
   (in the source and in the target) that correspond to it.
*)
Definition get_pi s := assoc param_tuples s.

Definition Addr_params s :=
  match get_pi s with
  | Some (_, (_, Vword sz w)) => if (sz == Uptr)%CMP
                                 then zero_extend Uptr w
                                 else 0%R
  | _                         => 0%R
  end.

Definition Writable_params s :=
  match get_pi s with
  | Some (pi, _) => pi.(pp_writable)
  | None         => false
  end.

Definition Align_params s :=
  match get_pi s with
  | Some (pi, _) => pi.(pp_align)
  | None         => U8
  end.

(* Slots : glob + stack + params *)
Definition Slots :=
  Sv.union Slots_globals (Sv.union Slots_locals Slots_params).

Lemma in_Slots s :
  Sv.In s Slots <->
    Sv.In s Slots_globals \/ Sv.In s Slots_locals \/ Sv.In s Slots_params.
Proof. by rewrite /Slots; rewrite !Sv.union_spec. Qed.

Definition pick_slot A (f_globals f_locals f_params : slot -> A) s :=
  if Sv.mem s Slots_globals then f_globals s
  else if Sv.mem s Slots_locals then f_locals s
  else f_params s.

Definition Addr := pick_slot Addr_globals Addr_locals Addr_params.
Definition Writable := pick_slot Writable_globals Writable_locals Writable_params.
Definition Align := pick_slot Align_globals Align_locals Align_params.

Lemma wunsigned_Addr_globals s ofs ws :
  Mvar.get mglob s = Some (ofs, ws) ->
  wunsigned (Addr_globals s) = wunsigned rip + ofs.
Proof.
  clear rsp_align rip_align.
  clear disjoint_zrange_globals_locals.
  move=> hget.
  rewrite /Addr_globals /Offset_slots hget.
  rewrite wunsigned_add //.
  have hbound := init_map_bounded hget.
  move: no_overflow_glob_size; rewrite /no_overflow zify => hover.
  have := wunsigned_range rip.
  have := size_slot_gt0 s.
  by lia.
Qed.

Lemma zbetween_Addr_globals s :
  Sv.In s Slots_globals ->
  zbetween rip glob_size (Addr_globals s) (size_slot s).
Proof.
  clear rsp_align rip_align.
  move=> /in_Slots_slots.
  case heq: Mvar.get => [[ofs ws]|//] _.
  rewrite /zbetween !zify (wunsigned_Addr_globals heq).
  have hbound := init_map_bounded heq.
  by lia.
Qed.

Lemma wunsigned_Addr_locals s ofs ws :
  Mvar.get stack s = Some (ofs, ws) ->
  wunsigned (Addr_locals s) = wunsigned rsp + ofs.
Proof.
  clear disjoint_zrange_globals_locals rsp_align rip_align.
  move=> hget.
  rewrite /Addr_locals /Offset_slots hget.
  rewrite wunsigned_add //.
  have hbound := init_stack_layout_bounded hget.
  move: no_overflow_size; rewrite /no_overflow zify => hover.
  have := wunsigned_range rsp.
  have := size_slot_gt0 s.
  by lia.
Qed.

Lemma zbetween_Addr_locals s :
  Sv.In s Slots_locals ->
  zbetween rsp sao.(sao_size) (Addr_locals s) (size_slot s).
Proof.
  clear rsp_align rip_align.
  move=> /in_Slots_slots.
  case heq: Mvar.get => [[ofs ws]|//] _.
  rewrite /zbetween !zify (wunsigned_Addr_locals heq).
  have hbound := init_stack_layout_bounded heq.
  by lia.
Qed.

Lemma zbetween_Addr_locals_ioff s :
  wunsigned (rsp + wrepr _ sao.(sao_ioff)) = wunsigned rsp + sao.(sao_ioff) ->
  Sv.In s Slots_locals ->
  zbetween (rsp + wrepr _ sao.(sao_ioff)) (sao.(sao_size) - sao.(sao_ioff)) (Addr_locals s) (size_slot s).
Proof.
  clear rsp_align rip_align.
  move=> hadd /in_Slots_slots.
  case heq: Mvar.get => [[ofs ws]|//] _.
  rewrite /zbetween !zify (wunsigned_Addr_locals heq).
  have hbound := init_stack_layout_bounded_ioff heq.
  rewrite hadd.
  by lia.
Qed.

Lemma disjoint_globals_locals : disjoint Slots_globals Slots_locals.
Proof.
  apply /disjointP => s /in_Slots_slots ? /in_Slots_slots.
  case heq: Mvar.get => [[ofs ws]|//].
  by move /init_stack_layout_not_glob in heq.
Qed.

Lemma pick_slot_globals s :
  Sv.In s Slots_globals ->
  forall A (f_globals f_locals f_params : slot -> A),
  pick_slot f_globals f_locals f_params s = f_globals s.
Proof. by rewrite /pick_slot => /Sv_memP ->. Qed.

Lemma pick_slot_locals s :
  Sv.In s Slots_locals ->
  forall A (f_globals f_locals f_params : slot -> A),
  pick_slot f_globals f_locals f_params s = f_locals s.
Proof.
  rewrite /pick_slot.
  case: Sv_memP => [|_].
  + by move /disjointP : disjoint_globals_locals => h /h.
  by move=> /Sv_memP ->.
Qed.


Variable vripn : Ident.ident.
Let vrip0 := {| vtype := spointer; vname := vripn |}.
Variable vrspn : Ident.ident.
Let vrsp0 := {| vtype := spointer; vname := vrspn |}.
Variable vlen : Ident.ident.
Let vxlen0 := {| vtype := spointer; vname := vlen |}.
Variable locals1 : Mvar.t ptr_kind.
Variable rmap1 : region_map.
Variable vnew1 : Sv.t.
Hypothesis hlocal_map : init_local_map vrip0 vrsp0 vxlen0 mglob stack sao = ok (locals1, rmap1, vnew1).
Variable vnew2 : Sv.t.
Variable locals2 : Mvar.t ptr_kind.
Variable rmap2 : region_map.
Variable alloc_params : seq (option sub_region * var_i).
Hypothesis hparams : init_params mglob stack vnew1 locals1 rmap1 sao.(sao_params) params = ok (vnew2, locals2, rmap2, alloc_params).
Definition empty_table :=
  {| bindings := Mvar.empty _; counter := 0; vars := Sv.empty |}.

Lemma uniq_param_tuples : uniq (map fst param_tuples).
Proof.
  have: uniq (map fst param_tuples) /\
    forall x, x \in map fst param_tuples -> Mvar.get locals1 x = None;
  last by move=> [].
  rewrite /param_tuples.
  move: hparams; rewrite /init_params.
  elim: sao.(sao_params) params vargs1 vargs2 vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params;
    first by move=> [|??] [|??] [|??].
  move=> opi sao_params ih [|x params'] [|varg1 vargs1'] [|varg2 vargs2'] //.
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params' /=.
  t_xrbindP=> -[[[vnew1' locals1'] rmap1'] alloc_param'] _.
  case heq: Mvar.get => //.
  case: opi => [pi|]; last first.
  + by move=> [<- <- <- <-] [[[??]?]?] /ih -/(_ vargs1' vargs2').
  t_xrbindP => _ _ _.
  case: Mvar.get => //.
  case: Mvar.get => //.
  case: Mvar.get => //.
  move=> [_ ? _ _]; subst locals1'.
  move=> [[[_ _] _] _] /ih -/(_ vargs1' vargs2') [ih1 ih2] _ _.
  split=> /=.
  + apply /andP; split=> //.
    apply /negP => /ih2.
    by rewrite Mvar.setP_eq.
  move=> y; rewrite in_cons => /orP.
  case.
  + by move=> /eqP ->.
  move=> /ih2.
  by rewrite Mvar.setP; case: eqP.
Qed.

Lemma in_Slots_params s :
  Sv.In s Slots_params <-> get_pi s <> None.
Proof.
  rewrite /Slots_params /get_pi SvP.MP.of_list_1 SetoidList.InA_alt.
  split.
  + move=> [] _ [<-] /InP /in_map [[x [opi v]] hin ->].
    by have -> := mem_uniq_assoc hin uniq_param_tuples.
  case heq: assoc => [[pi [v1 v2]]|//] _.
  exists s; split=> //.
  apply /InP; apply /in_map.
  exists (s, (pi, (v1, v2))) => //.
  by apply assoc_mem'.
Qed.

Lemma init_params_not_glob_nor_stack s pi :
  get_pi s = Some pi ->
  Mvar.get mglob s = None /\ Mvar.get stack s = None.
Proof.
  rewrite /get_pi /param_tuples.
  move: hparams; rewrite /init_params.
  elim: params sao.(sao_params) vargs1 vargs2 vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params;
    first by move=> [|??] [|??] [|??].
  move=> x params' ih [|opi2 sao_params] [|varg1 vargs1'] [|varg2 vargs2'] //.
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params' /=.
  t_xrbindP=> -[[[??]?]?] _.
  case: Mvar.get => //.
  case: opi2 => [pi2|]; last first.
  + by move=> [<- <- <- <-] [[[??]?]?] /ih{}ih _ _; apply ih.
  t_xrbindP => _ _ _.
  case: Mvar.get => //.
  case heq1: Mvar.get => //.
  case heq2: Mvar.get => //.
  move=> _ [[[_ _] _] _] /ih{}ih _ _ /=.
  case: eqP => [-> //|_].
  by apply ih.
Qed.

Lemma get_pi_Forall :
  List.Forall (fun '(x, (opi, (v1, v2))) =>
    forall pi, opi = Some pi -> get_pi x.(v_var) = Some (pi, (v1, v2)))
    (zip params (zip sao.(sao_params) (zip vargs1 vargs2))).
Proof.
  apply List.Forall_forall.
  move=> [x [opi [v1 v2]]] hin pi ?; subst opi.
  rewrite /get_pi.
  apply: mem_uniq_assoc uniq_param_tuples.
  rewrite /param_tuples.
  have [s1 [s2 ->]] := List.in_split _ _ hin.
  rewrite pmap_cat.
  by apply List.in_app_iff; right; left.
Qed.

Lemma get_pi_size_le s pi v1 v2 :
  get_pi s = Some (pi, (v1, v2)) -> size_slot s <= size_val v1.
Proof.
  rewrite /get_pi => -/(assoc_mem' (w:=_)).
  rewrite /param_tuples.
  elim: Hsub vargs2; first by move=> [].
  move=> opi x varg1 sao_params params' vargs1' hsub _ ih [//|varg2 vargs2'].
  case: opi hsub => [pi'|] hsub; last by apply ih.
  move=> [[<- _ <- _] //|]; last by apply ih.
  apply size_of_le.
  by apply hsub.
Qed.

Lemma get_pi_nth s pi v1 v2 :
  get_pi s = Some (pi, (v1, v2)) ->
  exists k,
    [/\ oseq.onth (map v_var params) k = Some s,
        nth None sao.(sao_params) k = Some pi,
        nth (Vbool true) vargs1 k = v1 &
        nth (Vbool true) vargs2 k = v2].
Proof.
  rewrite /get_pi => -/(assoc_mem' (w:=_)).
  rewrite /param_tuples.
  elim: sao.(sao_params) params vargs1 vargs2; first by move=> [|??] [|??] [|??].
  move=> opi sao_params ih [|x params'] [|varg1 vargs1'] [|varg2 vargs2'] //.
  case: opi => [pi'|].
  + move=> /=.
    case.
    + by move=> [-> -> -> ->]; exists 0%nat.
    by move=> /ih{ih} [k ih]; exists (S k).
  by move=> /ih{ih} [k ih]; exists (S k).
Qed.

Lemma get_pi_wf_arg s pi v1 v2 :
  get_pi s = Some (pi, (v1, v2)) ->
  exists i (p:word Uptr),
    v2 = Vword p /\
    wf_arg_pointer glob_size rip m1 m2
      (map (omap pp_writable) sao.(sao_params))
      vargs1 vargs2 pi.(pp_writable) pi.(pp_align) v1 p i.
Proof.
  move=> /get_pi_nth [i [h1 h2 h3 h4]].
  have := Hargs i; rewrite /wf_arg (nth_map None);
    last by apply (nth_not_default h2 ltac:(discriminate)).
  rewrite h2 /= => -[p [heq hargp]].
  exists i, p; split.
  + by rewrite -h4 heq.
  move: hargp.
  rewrite (nth_map None);
    last by apply (nth_not_default h2 ltac:(discriminate)).
  by rewrite h2 h3.
Qed.

Lemma disjoint_globals_params : disjoint Slots_globals Slots_params.
Proof.
  apply /disjointP => s /in_Slots_slots ? /in_Slots_params.
  case heq: get_pi => [pi|//].
  by have [] := init_params_not_glob_nor_stack heq; congruence.
Qed.

Lemma disjoint_locals_params : disjoint Slots_locals Slots_params.
Proof.
  apply /disjointP => s /in_Slots_slots ? /in_Slots_params.
  case heq: get_pi => [pi|//].
  by have [] := init_params_not_glob_nor_stack heq; congruence.
Qed.

Lemma pick_slot_params s :
  Sv.In s Slots_params ->
  forall A (f_globals f_locals f_params : slot -> A),
  pick_slot f_globals f_locals f_params s = f_params s.
Proof.
  rewrite /pick_slot.
  case: Sv_memP => [|_].
  + by move /disjointP : disjoint_globals_params => h /h.
  case: Sv_memP => //.
  by move /disjointP : disjoint_locals_params => h /h.
Qed.

Lemma disjoint_zrange_globals_params :
  forall s, Sv.In s Slots_params -> Writable_params s ->
  0 < glob_size -> disjoint_zrange rip glob_size (Addr_params s) (size_slot s).
Proof.
  move=> s hin hw hgsize.
  have /in_Slots_params := hin.
  case hpi: get_pi => [[pi [varg1 varg2]]|//] _.
  rewrite /Addr_params hpi.
  have [i [p [? hargp]]] := get_pi_wf_arg hpi; subst varg2.
  move: hw; rewrite /Writable_params hpi => hw.
  have := hargp.(wap_writable_not_glob) hw hgsize.
  apply disjoint_zrange_incl_r.
  rewrite eq_refl zero_extend_u.
  by apply: zbetween_le (get_pi_size_le hpi).
Qed.

Hypothesis Hdisjoint_zrange_locals :
  Forall3 (fun opi varg1 varg2 =>
    forall pi, opi = Some pi ->
    forall (p:pointer), varg2 = Vword p ->
    0 < sao.(sao_size) ->
    disjoint_zrange rsp sao.(sao_size) p (size_val varg1)) sao.(sao_params) vargs1 vargs2.

Lemma disjoint_zrange_locals_params :
  forall s, Sv.In s Slots_params -> 0 < sao.(sao_size) ->
  disjoint_zrange rsp sao.(sao_size) (Addr_params s) (size_slot s).
Proof.
  move=> s hin hlt.
  have /in_Slots_params := hin.
  case hpi: get_pi => [[pi [varg1 varg2]]|//] _.
  rewrite /Addr_params hpi.
  have [i [p [? hargp]]] := get_pi_wf_arg hpi; subst varg2.
  have hle := get_pi_size_le hpi.
  apply (disjoint_zrange_incl_r (zbetween_le _ hle)).
  have [k [hnth1 hnth2 hnth3 hnth4]] := get_pi_nth hpi.
  rewrite -hnth3.
  rewrite eq_refl zero_extend_u.
  by apply (Forall3_nth Hdisjoint_zrange_locals None (Vbool true) (Vbool true)
    (nth_not_default hnth2 ltac:(discriminate)) _ hnth2 _ hnth4 hlt).
Qed.

Lemma wf_Slots_params :
  wf_Slots Slots_params Addr_params Writable_params Align_params.
Proof.
  split.
  + move=> s /in_Slots_params.
    case hpi: get_pi => [[pi [v1 v2]]|//] _.
    have [i [p [? hargp]]] := get_pi_wf_arg hpi; subst v2.
    have hle := get_pi_size_le hpi.
    rewrite /Addr_params hpi.
    apply: no_overflow_incl hargp.(wap_no_overflow).
    rewrite eq_refl zero_extend_u.
    by apply zbetween_le.
  + move=> sl1 sl2 /in_Slots_params hsl1 /in_Slots_params hsl2 hneq.
    case hpi1: get_pi hsl1 => [[pi1 [v11 v12]]|//] _.
    case hpi2: get_pi hsl2 => [[pi2 [v21 v22]]|//] _.
    have [i1 [hnth11 hnth12 hnth13 hnth14]] := get_pi_nth hpi1.
    have [i2 [hnth21 hnth22 hnth23 hnth24]] := get_pi_nth hpi2.
    have := Hargs i1; rewrite /wf_arg (nth_map None);
      last by apply (nth_not_default hnth12 ltac:(discriminate)).
    rewrite hnth12 /= => -[p1 [hp1 hargp1]].
    have := Hargs i2; rewrite /wf_arg (nth_map None);
      last by apply (nth_not_default hnth22 ltac:(discriminate)).
    rewrite hnth22 /= => -[p2 [hp2 _]].
    rewrite /Writable_params /Addr_params hpi1 hpi2 => hw1.
    rewrite -hnth14 hp1 -hnth24 hp2 eq_refl 2!zero_extend_u.
    have hle1 := get_pi_size_le hpi1.
    have hle2 := get_pi_size_le hpi2.
    apply (disjoint_zrange_incl_l (zbetween_le _ hle1)).
    apply (disjoint_zrange_incl_r (zbetween_le _ hle2)).
    rewrite -hnth13 -hnth23.
    apply (hargp1.(wap_writable_disjoint) hw1 (j:=i2)) => //.
    + congruence.
    rewrite (nth_map None);
      last by apply (nth_not_default hnth22 ltac:(discriminate)).
    by rewrite hnth22.
  + move=> s /in_Slots_params.
    case hpi: get_pi => [[pi [v1 v2]]|//] _.
    have [i [p [? hargp]]] := get_pi_wf_arg hpi; subst v2.
    rewrite /Addr_params /Align_params hpi.
    rewrite eq_refl zero_extend_u.
    by apply hargp.(wap_align).
  by apply disjoint_zrange_globals_params.
Qed.

Lemma Haddr_no_overflow : forall s, Sv.In s Slots -> no_overflow (Addr s) (size_slot s).
Proof.
  move=> s /in_Slots [hin|[hin|hin]].
  + rewrite /Addr (pick_slot_globals hin).
    apply: no_overflow_incl no_overflow_glob_size.
    by apply zbetween_Addr_globals.
  + rewrite /Addr (pick_slot_locals hin).
    apply: no_overflow_incl no_overflow_size.
    by apply zbetween_Addr_locals.
  rewrite /Addr (pick_slot_params hin).
  by apply wf_Slots_params.
Qed.

Lemma Hdisjoint_writable : forall s1 s2, Sv.In s1 Slots -> Sv.In s2 Slots -> s1 <> s2 ->
  Writable s1 -> disjoint_zrange (Addr s1) (size_slot s1) (Addr s2) (size_slot s2).
Proof.
  move=> sl1 sl2 hin1 hin2 hneq hw.
  have hover1 := Haddr_no_overflow hin1.
  have hover2 := Haddr_no_overflow hin2.
  move /in_Slots : hin1 => [hin1|[hin1|hin1]].
  + by move: hw; rewrite /Writable (pick_slot_globals hin1).
  + move /in_Slots : hin2 => [hin2|[hin2|hin2]].
    + apply disjoint_zrange_sym.
      apply: disjoint_zrange_incl (disjoint_zrange_globals_locals _ _).
      + rewrite /Addr (pick_slot_globals hin2).
        by apply (zbetween_Addr_globals hin2).
      + rewrite /Addr (pick_slot_locals hin1).
        by apply (zbetween_Addr_locals hin1).
      + move /in_Slots_slots : hin2.
        case heq: Mvar.get => [[ofs ws]|//] _.
        have := init_map_bounded heq.
        have := size_slot_gt0 sl2.
        by lia.
      move /in_Slots_slots : hin1.
      case heq: Mvar.get => [[ofs ws]|//] _.
      have := init_stack_layout_bounded heq.
      have := size_slot_gt0 sl1.
      by lia.
    + split=> //.
      rewrite /Addr (pick_slot_locals hin1) (pick_slot_locals hin2).
      move /in_Slots_slots : hin1.
      case heq1 : Mvar.get => [[ofs1 ws1]|//] _.
      move /in_Slots_slots : hin2.
      case heq2 : Mvar.get => [[ofs2 ws2]|//] _.
      rewrite (wunsigned_Addr_locals heq1).
      rewrite (wunsigned_Addr_locals heq2).
      have := init_stack_layout_disjoint heq1 heq2 hneq.
      by lia.
    rewrite /Addr (pick_slot_locals hin1) (pick_slot_params hin2).
    apply: disjoint_zrange_incl_l (disjoint_zrange_locals_params hin2 _).
    + by apply (zbetween_Addr_locals hin1).
    move /in_Slots_slots : hin1.
    case heq: Mvar.get => [[ofs ws]|//] _.
    have := init_stack_layout_bounded heq.
    have := size_slot_gt0 sl1.
    by lia.
  move /in_Slots : hin2 => [hin2|[hin2|hin2]].
  + rewrite /Addr (pick_slot_params hin1) (pick_slot_globals hin2).
    rewrite /Writable (pick_slot_params hin1) in hw.
    apply disjoint_zrange_sym.
    apply: disjoint_zrange_incl_l (disjoint_zrange_globals_params hin1 hw _).
    + by apply (zbetween_Addr_globals hin2).
    move /in_Slots_slots : hin2.
    case heq: Mvar.get => [[ofs ws]|//] _.
    have := init_map_bounded heq.
    have := size_slot_gt0 sl2.
    by lia.
  + rewrite /Addr (pick_slot_params hin1) (pick_slot_locals hin2).
    apply disjoint_zrange_sym.
    apply: disjoint_zrange_incl_l (disjoint_zrange_locals_params hin1 _).
    + by apply (zbetween_Addr_locals hin2).
    move /in_Slots_slots : hin2.
    case heq: Mvar.get => [[ofs ws]|//] _.
    have := init_stack_layout_bounded heq.
    have := size_slot_gt0 sl2.
    by lia.
  rewrite /Addr (pick_slot_params hin1) (pick_slot_params hin2).
  rewrite /Writable (pick_slot_params hin1) in hw.
  by apply wf_Slots_params.
Qed.

Lemma Hslot_align : forall s, Sv.In s Slots -> is_align (Addr s) (Align s).
Proof.
  move=> s /in_Slots [hin|[hin|hin]].
  + rewrite /Addr /Align !(pick_slot_globals hin).
    move /in_Slots_slots : hin.
    case heq: Mvar.get => [[ofs ws]|//] _.
    rewrite /Addr_globals /Offset_slots /Align_globals /Align_slots heq.
    apply is_align_add.
    + apply: is_align_m rip_align.
      by apply wsize_ge_U256.
    rewrite WArray.arr_is_align.
    by apply /eqP; apply (init_map_align heq).
  + rewrite /Addr /Align !(pick_slot_locals hin).
    move /in_Slots_slots : hin.
    case heq: Mvar.get => [[ofs ws]|//] _.
    rewrite /Addr_locals /Offset_slots /Align_locals /Align_slots heq.
    apply is_align_add.
    + apply: is_align_m rsp_align.
      by apply (init_stack_layout_stack_align heq).
    rewrite WArray.arr_is_align.
    by apply /eqP; apply (init_stack_layout_align heq).
  rewrite /Addr /Align !(pick_slot_params hin).
  by apply wf_Slots_params.
Qed.

Lemma Hwritable_not_glob :
  forall s, Sv.In s Slots -> Writable s ->
  0 < glob_size -> disjoint_zrange rip glob_size (Addr s) (size_slot s).
Proof.
  move=> s /in_Slots [hin|[hin|hin]].
  + by rewrite /Writable (pick_slot_globals hin).
  + move=> _ hlt.
    apply: disjoint_zrange_incl_r (disjoint_zrange_globals_locals _ _) => //.
    + rewrite /Addr (pick_slot_locals hin).
      by apply (zbetween_Addr_locals hin).
    move /in_Slots_slots : hin.
    case heq: Mvar.get => [[ofs ws]|//] _.
    have := init_stack_layout_bounded heq.
    have := size_slot_gt0 s.
    by lia.
  rewrite /Writable /Addr !(pick_slot_params hin).
  by apply wf_Slots_params.
Qed.

Lemma Hwf_Slots : wf_Slots Slots Addr Writable Align.
Proof.
  split.
  + by apply Haddr_no_overflow.
  + by apply Hdisjoint_writable.
  + by apply Hslot_align.
  by apply Hwritable_not_glob.
Qed.

Definition lmap locals' vnew' := {|
  vrip := vrip0;
  vrsp := vrsp0;
  vxlen := vxlen0;
  globals := mglob;
  locals := locals';
  vnew := vnew'
|}.

Lemma init_map_wf g ofs ws :
  Mvar.get mglob g = Some (ofs, ws) ->
  wf_global rip Slots Addr Writable Align g ofs ws.
Proof.
  move=> hget.
  have hin: Sv.In g Slots_globals.
  + by apply in_Slots_slots; congruence.
  split=> /=.
  + by apply in_Slots; left.
  + by rewrite /Writable (pick_slot_globals hin).
  + by rewrite /Align (pick_slot_globals hin) /Align_globals /Align_slots hget.
  by rewrite /Addr (pick_slot_globals hin) /Addr_globals /Offset_slots hget.
Qed.

Lemma init_map_wf_rmap vnew' se s1 s2 :
  (forall i, 0 <= i < glob_size ->
    read (emem s2) Aligned (rip + wrepr Uptr i)%R U8 = ok (nth 0%R global_data (Z.to_nat i))) ->
  wf_rmap (lmap (Mvar.empty _) vnew') Slots Addr Writable Align P Sv.empty empty se s1 s2.
Proof.
  clear rsp_align rip_align.
  clear disjoint_zrange_globals_locals.
  move=> heqvalg.
  split=> //=.
  move=> y sry bytesy vy.
  rewrite /check_gvalid /=.
  case: (@idP (is_glob y)) => // hg.
  case heq: Mvar.get => [[ofs ws]|//] [<- <-].
  rewrite get_gvar_glob // => /get_globalI [v [hv -> hty]].
  split=> // off addr w ok_addr _ ok_w.
  move: ok_addr; rewrite /sub_region_addr /= wrepr0 GRing.addr0 => -[<-].
  have hin: Sv.In y.(gv) Slots_globals.
  + by apply in_Slots_slots; congruence.
  rewrite /Addr (pick_slot_globals hin) /Addr_globals /Offset_slots heq.
  rewrite -GRing.addrA -wrepr_add.
  rewrite heqvalg.
  + f_equal.
    have /check_globsP := hv.
    rewrite heq => -[? [? [[<- _]]]].
    by apply.
  have := init_map_bounded heq.
  have := get_val_byte_bound ok_w; rewrite hty.
  by lia.
Qed.

Lemma add_alloc_wf_pmap locals1' rmap1' vnew1' x pki locals2' rmap2' vnew2' :
  add_alloc mglob stack (x, pki) (locals1', rmap1', vnew1') = ok (locals2', rmap2', vnew2') ->
  wf_pmap (lmap locals1' vnew1') rsp rip Slots Addr Writable Align ->
  wf_pmap (lmap locals2' vnew2') rsp rip Slots Addr Writable Align.
Proof.
  move=> hadd hpmap.
  case: (hpmap) => /= htlen hnew1 hneq1 hneq2 hneq3 hnew2 hnew3 hrip hrsp hglobals hlocals hnew.
  move: hadd => /=.
  case: Sv_memP => [//|hnnew].
  case hregx: Mvar.get => //.
  set wf_pmap := wf_pmap. (* hack due to typeclass interacting badly *)
  t_xrbindP=> {rmap2'} -[[sv pk] rmap2'] hpki [<- _ <-].
  case: pki hpki.
  + move=> s z sc.
    case heq: Mvar.get => [[ofs ws]|//].
    case: ifP => [/and3P []|//].
    rewrite !zify => h1 h2 h3 [<- <- _].
    split=> //=.
    + by move=> y pky; rewrite Mvar.setP; case: eqP => // ?; apply hneq3.
    + move=> y pky.
      rewrite Mvar.setP.
      case: eqP.
      + move=> <- [<-].
        case: sc heq => heq.
        + have hin: Sv.In s Slots_locals.
          + by apply in_Slots_slots; congruence.
          split=> //=.
          + by apply in_Slots; right; left.
          + by rewrite /Writable (pick_slot_locals hin).
          + by rewrite /Align (pick_slot_locals hin) /Align_locals /Align_slots heq.
          by rewrite /Addr (pick_slot_locals hin) /Addr_locals /Offset_slots heq.
        have hin: Sv.In s Slots_globals.
        + by apply in_Slots_slots; congruence.
        split=> //=.
        + by apply in_Slots; left.
        + by rewrite /Writable (pick_slot_globals hin).
        + by rewrite /Align (pick_slot_globals hin) /Align_globals /Align_slots heq.
        by rewrite /Addr (pick_slot_globals hin) /Addr_globals /Offset_slots heq.
      move=> hneq /hlocals.
      case: pky => //=.
      + move=> p [] hty1 hty2 hrip' hrsp' hnew' hneq'.
        split=> //=.
        rewrite /get_local /= => w wr.
        rewrite Mvar.setP.
        case: eqP => //.
        by move=> _; apply hneq'.
      move=> sy ofsy wsy zy yf [] hslot hty hlen hofs hw hal hcmp hal2 haddr hnew' hneq'.
      split=> //=.
      rewrite /get_local /= => w sw ofsw wsw' zw wf.
      rewrite Mvar.setP.
      case: eqP => //.
      by move=> _; apply hneq'.
    move=> y pky.
    rewrite Mvar.setP.
    case: eqP.
    + by move=> <- _.
    by move=> _; apply hnew.
  + move=> p.
    case harr: is_sarr => //=.
    case: Sv_memP => [//|hnnew2].
    case heq0: Mvar.get => //.
    case: eqP => [hty|//] /= [<- <- _].
    split=> //=.
    + by apply SvD.F.add_2.
    + move=> y pky; rewrite Mvar.setP; case: eqP => ?; last by apply hneq3.
      by move=> [?] ?; subst y p pky; elim hnnew2.
    + by apply SvD.F.add_2.
    + by apply SvD.F.add_2.
    + move=> y pky.
      rewrite Mvar.setP.
      case: eqP.
      + move=> <- [<-].
        split=> //=.
        + by congruence.
        + by congruence.
        + by apply SvD.F.add_1.
        rewrite /get_local /= => w wr.
        rewrite Mvar.setP.
        case: eqP => //.
        by move=> hneq /hlocals /wfr_new /=; congruence.
      move=> hneq /hlocals.
      case: pky => //=.
      + move=> p' [] /= hty1 hty2 hrip' hrsp' hnew' hneq'.
        split=> //=.
        + by apply SvD.F.add_2.
        rewrite /get_local /= => w wr.
        rewrite Mvar.setP.
        case: eqP.
        + by move=> _ [<-]; congruence.
        by move=> _; apply hneq'.
      move=> sy ofsy wsy zy yf [] hslot hty' hlen hofs hw hal hcmp hal2 haddr hnew' hneq'.
      split=> //=.
      + by apply SvD.F.add_2.
      move=> w sw ofsw wsw' zw wf.
      rewrite /get_local /= Mvar.setP.
      case: eqP => //.
      by move=> _; apply hneq'.
    move=> y pky.
    rewrite Mvar.setP.
    case: eqP.
    + move=> <- _.
      have ?: x <> p.
      + by move /is_sarrP: harr => [n]; congruence.
      by move=> /SvD.F.add_3; auto.
    move=> ? /[dup] ? /hnew ?.
    have ?: p <> y by congruence.
    by move=> /SvD.F.add_3; auto.
  move=> s z f.
  case harr: is_sarr => //.
  case heq: Mvar.get => [[ofs ws]|//].
  case: Sv_memP => [//|hnnew2].
  case: eqP => [//|hneq0].
  case heqf: Mvar.get => //.
  case: ifP => [/and5P []|//].
  move=> h1.
  rewrite !zify.
  move=> h2 /eqP; rewrite (Zland_mod _ Uptr) => h3 h4 h5 [<- <- _].
  split=> //=.
  + by apply SvD.F.add_2.
  + by move=> y pky; rewrite Mvar.setP; case: eqP => // ?; apply hneq3.
  + by apply SvD.F.add_2.
  + by apply SvD.F.add_2.
  + move=> y pky.
    rewrite Mvar.setP.
    case: eqP.
    + move=> <- [<-].
      have hin: Sv.In s Slots_locals.
      + by apply in_Slots_slots; congruence.
      split=> //=.
      + by apply in_Slots; right; left.
      + by rewrite /Writable (pick_slot_locals hin).
      + by rewrite /Align (pick_slot_locals hin) /Align_locals /Align_slots heq.
      + by rewrite WArray.arr_is_align; apply /eqP.
      + by rewrite /Addr (pick_slot_locals hin) /Addr_locals /Offset_slots heq.
      + by apply SvD.F.add_1.
      move=> w sw ofsw wsw' zw wf.
      rewrite /get_local /= Mvar.setP.
      case: eqP => //.
      by move=> _ /hlocals /wfs_new /=; congruence.
    move=> hneq /hlocals.
    case: pky => //=.
    + move=> p [] hty1 hty2 hrip' hrsp' hnew' hneq'.
      split=> //=.
      + by apply SvD.F.add_2.
      move=> w wr /=.
      rewrite /get_local /= Mvar.setP.
      case: eqP => //.
      by move=> _; apply hneq'.
    move=> sy ofsy wsy zy yf [] /= hslot hty' hlen hofs hw hal hcmp hal2 haddr hnew' hneq'.
    split=> //=.
    + by apply SvD.F.add_2.
    move=> w sw ofsw wsw' zw wf.
    rewrite /get_local /= Mvar.setP.
    case: eqP.
    + by move=> _ [_ _ _ _ <-]; congruence.
    by move=> _; apply hneq'.
  move=> y pky.
  rewrite Mvar.setP.
  case: eqP.
  + move=> <- _.
    by move=> /SvD.F.add_3; auto.
  move=> ? /[dup] ? /hnew ?.
  have ?: f <> y by congruence.
  by move=> /SvD.F.add_3; auto.
Qed.

Lemma add_alloc_wf_rmap locals1' rmap1' vnew1' x pki locals2' rmap2' vnew2' vars vme s2 :
  wf_pmap (lmap locals1' vnew1') rsp rip Slots Addr Writable Align ->
  add_alloc mglob stack (x, pki) (locals1', rmap1', vnew1') = ok (locals2', rmap2', vnew2') ->
  let: s1 := {| escs := scs1; emem := m1; evm := Vm.init |} in
  wf_rmap (lmap locals1' vnew1') Slots Addr Writable Align P vars rmap1' vme s1 s2 ->
  wf_rmap (lmap locals2' vnew2') Slots Addr Writable Align P vars rmap2' vme s1 s2.
Proof.
  move=> hpmap hadd hrmap.
  case: (hrmap) => hwfsr hwfst hvarsz hvarss hval hptr.
  move: hadd => /=.
  case: Sv_memP => [//|hnnew].
  case hregx: Mvar.get => //.
  set wf_rmap := wf_rmap. (* hack due to typeclass interacting badly *)
  t_xrbindP=> {rmap2'} -[[sv pk] rmap2'] hpki [<- <- <-].
  case: pki hpki.
  + move=> s z sc.
    case heq: Mvar.get => [[ofs ws]|//].
    case: ifP => [/and3P []|//].
    rewrite !zify => h1 h2 h3 [<- <- <-].
    case: sc heq => heq.
    + split.
      + move=> y sry.
        rewrite Mvar.setP.
        case: eqP.
        + move=> <- [<-].
          have hin: Sv.In s Slots_locals.
          + by apply in_Slots_slots; congruence.
          split; last by eexists; first by reflexivity.
          split.
          + by apply in_Slots; right; left.
          + by rewrite /Writable (pick_slot_locals hin).
          by rewrite /Align (pick_slot_locals hin) /Align_locals /Align_slots heq.
        by move=> _; apply hwfsr.
      + by apply: wfr_STATUS_set_move_status hwfst.
      + apply wfr_VARS_ZONE_set_move => //.
        rewrite /wf_vars_zone /= /read_slice /= /read_e /=.
        by clear; SvD.fsetdec.
      + by apply wfr_VARS_STATUS_set_move_status.
      + move=> y sry statusy vy /check_gvalid_set_move [].
        + move=> [hg ? _ _]; subst x.
          rewrite get_gvar_nglob; last by apply /negP.
          rewrite /get_var /= Vm.initP; t_xrbindP => /is_defined_undef_addr [len] hlen <-.
          split; rewrite hlen => // off addr w _ _ /=; rewrite WArray.get_empty.
          by case: ifP.
        by move=> [] _; apply hval.
      move=> y sry.
      rewrite /get_local /=.
      rewrite !Mvar.setP.
      case: eqP.
      + move=> _ [<-].
        by eexists; split; first by reflexivity.
      move=> hneq /hptr [pky [hly hpky]].
      exists pky; split=> //.
      case: pky hly hpky => //= sy ofsy wsy csy yf hly hpky.
      rewrite /check_stack_ptr get_var_status_set_move_status /=.
      case: eqP => //=.
      case: eqP => //.
      by have /wf_locals /wfs_new /= := hly; congruence.
    split=> //.
    move=> y sry /hptr.
    rewrite /get_local /= => -[pky [hly hpky]].
    exists pky; split=> //.
    rewrite Mvar.setP.
    by case: eqP; first by congruence.
  + move=> p.
    case harr: is_sarr => //=.
    case: Sv_memP => [//|hnnew2].
    case heq0: Mvar.get => //.
    case: eqP => [hty|//] /= [<- <- <-].
    split=> //=.
    move=> y sry /hptr.
    rewrite /get_local /= => -[pky [hly hpky]].
    exists pky; split=> //.
    rewrite Mvar.setP.
    by case: eqP; first by congruence.
  move=> s cs f.
  case harr: is_sarr => //.
  case heq: Mvar.get => [[ofs ws]|//].
  case: Sv_memP => [//|hnnew2].
  case: eqP => [//|hneq0].
  case heqf: Mvar.get => //.
  case: ifP => [/and5P []|//].
  move=> h1.
  rewrite !zify.
  move=> h2 /eqP; rewrite (Zland_mod _ Uptr) => h3 h4 h5 [<- <- <-].
  split=> //.
  move=> y sry /hptr.
  rewrite /get_local /= => -[pky [hly hpky]].
  exists pky; split=> //.
  rewrite Mvar.setP.
  by case: eqP; first by congruence.
Qed.

Lemma init_local_map_wf_pmap :
  wf_pmap (lmap locals1 vnew1) rsp rip Slots Addr Writable Align.
Proof.
  move: hlocal_map; rewrite /init_local_map.
  set wf_pmap := wf_pmap. (* hack due to typeclass interacting badly *)
  t_xrbindP=> /eqP hneq1 /eqP hneq2 -[[locals1' rmap1'] vnew1'] hfold [???];
    subst locals1' rmap1' vnew1'.
  move: hfold.
  have: wf_pmap (lmap (Mvar.empty ptr_kind, empty, Sv.add vxlen0 (Sv.add vrip0 (Sv.add vrsp0 Sv.empty))).1.1
                      (Mvar.empty ptr_kind, empty, Sv.add vxlen0 (Sv.add vrip0 (Sv.add vrsp0 Sv.empty))).2) rsp rip
                      Slots Addr Writable Align.
  + split=> //=.
    + by apply SvD.F.add_1.
    + by apply/SvD.F.add_2/SvD.F.add_1.
    + by do 2 apply SvD.F.add_2; apply SvD.F.add_1.
    by apply init_map_wf.
  elim: sao.(sao_alloc) (Mvar.empty _, _, _).
  + by move=> /= [[locals0 rmap0] vnew0] ? [<- _ <-].
  move=> [x pki] l ih [[locals0 rmap0] vnew0] /= hpmap.
  t_xrbindP=> -[[locals1' rmap1'] vnew1'] halloc.
  apply ih.
  by apply (add_alloc_wf_pmap halloc hpmap).
Qed.

Lemma init_local_map_wf_rmap vme s2 :
  let: s1 := {| escs := scs1; emem := m1; evm := Vm.init |} in
  (forall i, 0 <= i < glob_size ->
    read (emem s2) Aligned (rip + wrepr Uptr i)%R U8 = ok (nth 0%R global_data (Z.to_nat i))) ->
  wf_rmap (lmap locals1 vnew1) Slots Addr Writable Align P Sv.empty rmap1 vme s1 s2.
Proof.
  clear rsp_align rip_align.
  move=> heqvalg.
  move: hlocal_map; rewrite /init_local_map.
  set wf_rmap := wf_rmap. (* hack due to typeclass interacting badly *)
  t_xrbindP=> /eqP hneq1 /eqP hneq2 -[[locals1' rmap1'] vnew1'] hfold [???]; subst locals1' rmap1' vnew1'.
  move: hfold.
  have: wf_pmap (lmap (Mvar.empty ptr_kind, empty, Sv.add vxlen0 (Sv.add vrip0 (Sv.add vrsp0 Sv.empty))).1.1
                      (Mvar.empty ptr_kind, empty, Sv.add vxlen0 (Sv.add vrip0 (Sv.add vrsp0 Sv.empty))).2) rsp rip
                      Slots Addr Writable Align
     /\ wf_rmap (lmap (Mvar.empty ptr_kind, empty, Sv.add vxlen0 (Sv.add vrip0 (Sv.add vrsp0 Sv.empty))).1.1
                      (Mvar.empty ptr_kind, empty, Sv.add vxlen0 (Sv.add vrip0 (Sv.add vrsp0 Sv.empty))).2)
                Slots Addr Writable Align P Sv.empty (Mvar.empty ptr_kind, empty, Sv.add vxlen0 (Sv.add vrip0 (Sv.add vrsp0 Sv.empty))).1.2
            vme {| escs := scs1; emem := m1; evm := Vm.init |} s2.
  + split.
    + split=> //=.
      + by apply/SvD.F.add_1.
      + by apply/SvD.F.add_2/SvD.F.add_1.
      + by apply/SvD.F.add_2/SvD.F.add_2/SvD.F.add_1.
      by apply init_map_wf.
    by apply init_map_wf_rmap.
  elim: sao.(sao_alloc) (Mvar.empty _, _, _).
  + by move=> /= [[locals0 rmap0] vnew0] [??] [<- <- <-].
  move=> [x pki] l ih [[locals0 rmap0] vnew0] /= [hpmap hrmap].
  t_xrbindP=> -[[locals1' rmap1'] vnew1'] halloc.
  apply ih.
  split.
  + by apply (add_alloc_wf_pmap halloc hpmap).
  by apply (add_alloc_wf_rmap hpmap halloc hrmap).
Qed.

Lemma init_param_wf_pmap vnew1' locals1' rmap1' sao_param (param:var_i) vnew2' locals2' rmap2' alloc_param :
  init_param mglob stack (vnew1', locals1', rmap1') sao_param param =
    ok (vnew2', locals2', rmap2', alloc_param) ->
  wf_pmap (lmap locals1' vnew1') rsp rip Slots Addr Writable Align ->
  wf_pmap (lmap locals2' vnew2') rsp rip Slots Addr Writable Align.
Proof.
  move=> hparam hpmap.
  case: (hpmap) => /= htlen hnew1 hneq1 hneq2 hneq3 hnew2 hnew3 hrip hrsp hglobals hlocals hnew.
  move: hparam => /=.
  set wf_pmap := wf_pmap. (* hack due to typeclass interacting badly *)
  t_xrbindP=> /Sv_memP hnnew.
  case heq: Mvar.get => //.
  case: sao_param => [pi|[<- <- _ _] //].
  t_xrbindP=> /eqP hregty /Sv_memP hnnew2 harrty.
  case heq1: Mvar.get => //.
  case heq2: Mvar.get => //.
  case heq3: Mvar.get => //.
  move=> [<- <- _ _].
  split=> //=.
  + by apply SvD.F.add_2.
  + move=> y pky; rewrite Mvar.setP; case: eqP => ?; last by apply hneq3.
    by move=> [?] h; subst y pky; elim hnnew2; rewrite -h.
  + by apply SvD.F.add_2.
  + by apply SvD.F.add_2.
  + move=> y pky.
    rewrite Mvar.setP.
    case: eqP.
    + move=> <- [<-] /=.
      split=> //=.
      + by congruence.
      + by congruence.
      + by apply SvD.F.add_1.
      move=> w wr.
      rewrite /get_local /= Mvar.setP.
      case: eqP => //.
      by move=> _ /hlocals /wfr_new /=; congruence.
    move=> ? /hlocals.
    case: pky => //=.
    + move=> p [] /= hty1 hty2 hrip' hrsp' hnew' hneq'.
      split=> //=.
      + by apply SvD.F.add_2.
      move=> w wr.
      rewrite /get_local /= Mvar.setP.
      case: eqP.
      + by move=> _ [<-]; congruence.
      by move=> _; apply hneq'.
    move=> sy ofsy wsy zy yf [] /= hslot hty' hlen hofs hw hal hcmp hal2 haddr hnew' hneq'.
    split=> //=.
    + by apply SvD.F.add_2.
    move=> w sw ofsw wsw' zw wf.
    rewrite /get_local /= Mvar.setP.
    case: eqP => //.
    by move=> _; apply hneq'.
  move=> y pky.
  rewrite Mvar.setP.
  case: eqP.
  + move=> <- _.
    have ?: param.(v_var) <> pi.(pp_ptr).
    + by move /is_sarrP : harrty => [n]; congruence.
    by move=> /SvD.F.add_3; auto.
  move=> ? /[dup] ? /hnew ?.
  have ?: pi.(pp_ptr) <> y by congruence.
  by move=> /SvD.F.add_3; auto.
Qed.

Lemma valid_state_init_param wdb table rmap vme m0 s1 s2 vnew1' locals1' sao_param (param:var_i) vnew2' locals2' rmap2' alloc_param :
  wf_pmap (lmap locals1' vnew1') rsp rip Slots Addr Writable Align ->
  valid_state (lmap locals1' vnew1') glob_size rsp rip Slots Addr Writable Align P table rmap vme m0 s1 s2 ->
  init_param mglob stack (vnew1', locals1', rmap) sao_param param = ok (vnew2', locals2', rmap2', alloc_param) ->
  forall s1' varg1 varg2,
    write_var wdb param varg1 s1 = ok s1' ->
    (forall pi, sao_param = Some pi -> get_pi param = Some (pi, (varg1, varg2))) ->
    value_eq_or_in_mem (emem s2) sao_param varg1 varg2 ->
    exists2 s2',
      write_var wdb alloc_param.2 varg2 s2 = ok s2' &
      valid_state (lmap locals2' vnew2') glob_size rsp rip Slots Addr Writable Align P (remove_binding table param) rmap2' vme m0 s1' s2'.
Proof.
  clear rsp_align rip_align no_overflow_size.
  move=> hpmap hvs hparam.
  have hpmap2 := init_param_wf_pmap hparam hpmap.
  move: hparam => /=.
  t_xrbindP=> /Sv_memP hnnew.
  case heq1: Mvar.get => [//|].
  case: sao_param => [pi|]; last first.
  + move=> [<- <- <- <-] /=.
    move=> s1' varg1 varg2 hw _ ->.
    move/write_varP: hw => [-> hdb h] /=.
    rewrite (write_var_truncate hdb h).
    by (eexists; first by reflexivity); apply valid_state_set_var.
  t_xrbindP=> /eqP hty1 /Sv_memP hnnew2 /is_sarrP [n hty2].
  case heq2: Mvar.get => //.
  case heq3: Mvar.get => //.
  case heq4: Mvar.get => //.
  move=> [? ? <- <-]; subst vnew2' locals2'.
  move=> s1' varg1 varg2 hw /(_ _ refl_equal) hpi [w [? hread]]; subst varg2 => /=.
  have hvpi: type_of_val (Vword w) = vtype pi.(pp_ptr) by rewrite hty1.
  eexists; first by apply: write_var_eq_type => //=; rewrite /DB /= orbT.
  set valid_state := valid_state. (* hack due to typeclass interacting badly *)
  move /write_varP: hw => [-> hdb h].
  set sr := sub_region_full _ _.
  have hin: Sv.In sr.(sr_region).(r_slot) Slots_params.
  + by apply in_Slots_params => /=; congruence.
  have hwf: wf_sub_region Slots Writable Align vme sr (sarr n).
  + split.
    + split=> /=.
      + by apply in_Slots; right; right.
      + by rewrite /Writable (pick_slot_params hin) /Writable_params hpi.
      + by rewrite /Align (pick_slot_params hin) /Align_params hpi.
    eexists; first by reflexivity.
    split=> /=.
    + by rewrite hty2 /=; lia.
    by rewrite hty2 /=; lia.
  have haddr: sub_region_addr Addr vme sr = ok w.
  + rewrite /sub_region_addr /= wrepr0 GRing.addr0.
    rewrite /Addr (pick_slot_params hin) /= /Addr_params hpi.
    by rewrite eq_refl zero_extend_u.
  have := h; rewrite {1}hty2 => /vm_truncate_valEl; rewrite -hty2 => -[a1 heq htreq].
  apply: (valid_state_set_move_regptr hpmap2) => //; last first.
  + split; rewrite htreq; last by rewrite /= hty2.
    rewrite /eq_sub_region_val_read haddr => off _ w' [<-] _ ok_w'.
    by apply hread; rewrite heq.
  + by rewrite /truncatable heq hty2 /= eqxx.
  + by rewrite /get_local /= Mvar.setP_eq.
  + rewrite /wf_vars_zone /= /read_slice /= /read_e /=.
    by clear; SvD.fsetdec.
  + by rewrite hty2.
  case:(hvs) => hscs hvalid hdisj hincl hincl2 hunch hrip hrsp heqvm hwft hwfr heqmem hglobv htop.
  split=> //.
  + move=> x /=;rewrite Mvar.setP.
    case: eqP => // ? hlx hnnew3; apply heqvm => // ?.
    by apply hnnew3; apply Sv.add_spec; right.
  case: (hwfr) => hwfsr hwfst hvarsz hvarss hval hptr; split=> //.
  move=> y sry /hptr.
  rewrite /get_local /= => -[pky [hly hpky]].
  exists pky; split=> //.
  rewrite Mvar.setP.
  by case: eqP => //; congruence.
Qed.

Lemma init_params_wf_pmap :
  wf_pmap (lmap locals2 vnew2) rsp rip Slots Addr Writable Align.
Proof.
  move: hparams.
  set wf_pmap := wf_pmap. (* hack due to typeclass interacting badly *)
  have := init_local_map_wf_pmap.
  elim: sao.(sao_params) params vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params.
  + by move=> [|//] ??????? hbase [<- <- _ _].
  move=> opi sao_params ih [//|param params'].
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params' hpmap.
  rewrite /init_params /=.
  apply rbindP => -[[[vnew1' locals1'] rmap1'] alloc_param] hparam.
  t_xrbindP=> -[[[??]?]?] /ih{}ih [<- <- _] _.
  apply ih.
  by apply (init_param_wf_pmap hparam).
Qed.

Lemma incl_table_merge_table_l table1 table2 :
  incl_table (merge_table table1 table2) table1.
Proof.
  apply /and3P; split=> /=.
  + apply /Mvar.inclP => x.
    rewrite Mvar.map2P //.
    case: Mvar.get => [e1|//].
    case: Mvar.get => [e2|//].
    by case: ifP.
  + case: ifP.
    + move=> _.
      apply /lebP.
      by clear; lia.
    move=> /lebP hle; apply /lebP.
    by clear -hle; lia.
  apply Sv.subset_spec.
  by clear; SvD.fsetdec.
Qed.

Lemma incl_table_merge_table_r table1 table2 :
  incl_table (merge_table table1 table2) table2.
Proof.
  apply /and3P; split=> /=.
  + apply /Mvar.inclP => x.
    rewrite Mvar.map2P //.
    case: Mvar.get => [e1|//].
    case: Mvar.get => [e2|//].
    by case: ifP.
  + case: ifP => //.
    move=> _.
    apply /lebP.
    by clear; lia.
  apply Sv.subset_spec.
  by clear; SvD.fsetdec.
Qed.

Lemma wf_table_incl table1 table2 vme vm :
  incl_table table2 table1 ->
  wft_VARS table2 ->
  wf_table table1 vme vm ->
  wf_table table2 vme vm.
Proof.
  move=> /and3P [hincl _ hsubset] hvars2 [hvars1 hdef1 hsem1].
  split=> //.
  + move: hsubset => /Sv.subset_spec hsubset.
    move=> x /hsubset.
    by apply hdef1.
  move=> x e2 v hget2 ok_v.
  have /Mvar.inclP /(_ x) := hincl.
  rewrite hget2.
  case hget1: Mvar.get => [e1|//].
  move=> /eqP ->.
  by apply (hsem1 _ _ _ hget1 ok_v).
Qed.

Lemma wft_VARS_merge_table table1 table2 :
  wft_VARS table1 ->
  wft_VARS table2 ->
  wft_VARS (merge_table table1 table2).
Proof.
  move=> hvars1 hvars2 x e /=.
  rewrite Mvar.map2P //.
  case he1: Mvar.get => [e1|//].
  case he2: Mvar.get => [e2|//].
  case: eqP => // ? [?]; subst e1 e2.
  have := hvars1 _ _ he1.
  have := hvars2 _ _ he2.
  by clear; SvD.fsetdec.
Qed.

Lemma valid_state_init_params wdb vme m0 vm1 vm2 :
  let: s1 := {| escs := scs1; emem := m1; evm := vm1 |} in
  let: s2 := {| escs := scs1; emem := m2; evm := vm2 |} in
  valid_state (lmap locals1 vnew1) glob_size rsp rip Slots Addr Writable Align P empty_table rmap1 vme m0 s1 s2 ->
  forall s1',
    write_vars wdb params vargs1 s1 = ok s1' ->
    exists2 s2',
      write_vars wdb (map snd alloc_params) vargs2 s2  = ok s2' &
      valid_state (lmap locals2 vnew2) glob_size rsp rip Slots Addr Writable Align P empty_table rmap2 vme m0 s1' s2'.
Proof.
  clear rsp_align rip_align no_overflow_size.
  move=> hvs.
  have {hvs}:
     wf_pmap (lmap locals1 vnew1) rsp rip Slots Addr Writable Align /\
     valid_state (lmap locals1 vnew1) glob_size rsp rip Slots Addr Writable Align P empty_table rmap1 vme m0
        {| escs := scs1; emem := m1; evm := vm1 |} {| escs := scs1; emem := m2; evm := vm2 |}.
  + split=> //.
    by apply init_local_map_wf_pmap.
  elim: Huincl params get_pi_Forall vnew1
    locals1 rmap1 vnew2 locals2 rmap2 alloc_params hparams vm1 vm2.
  + move=> [|//] _ ??????? [<- <- <- <-] vm1 vm2 [_ hvs] _ [<-].
    by eexists.
  move=> opi varg1 varg2 sao_params vargs1' vargs2' heqinmem _ ih [//|x params'].
  move=> /= /List_Forall_inv [hpi hforall].
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params'.
  rewrite /init_params /=.
  apply: rbindP=> -[[[vnew1' locals1'] rmap1'] alloc_param] hparam.
  t_xrbindP=> -[[[??]?]?] /ih{}ih [<- <- <-] <- vm1 vm2 [hpmap hvs].
  move=> s1'' s1' hs1' hs1''.
  have [//|s2' hs2' hvs'] := valid_state_init_param hpmap hvs hparam hs1' _ heqinmem.
  rewrite /= hs2'.
  move: hs1' hs2'.
  rewrite /write_var.
  t_xrbindP=> /= vm1' hvm1' ? vm2' hvm2' ?; subst s1' s2'.
  have hpmap' := init_param_wf_pmap hparam hpmap.
  (* TODO: could this be (the consequence of) a more generic lemma? *)
  have {}hvs':
    valid_state (lmap locals1' vnew1') glob_size rsp rip Slots Addr Writable Align P empty_table rmap1' vme m0
      {| escs := scs1; emem := m1; evm := vm1' |} {| escs := scs1; emem := m2; evm := vm2' |}.
  + case:(hvs') => hscs hvalid hdisj hincl hincl2 hunch hrip hrsp heqvm hwft hwfr heqmem hglobv htop.
    split=> //.
    case: hwft => hvars hdef hsem.
    by split.
  have [//|s2'' hs2'' hvs''] := ih _ _ _ (conj hpmap' hvs') _ hs1''.
  rewrite hs2''.
  by eexists.
Qed.

Lemma init_param_alloc_param se vnew1' locals1' rmap1' sao_param (param:var_i) vnew2' locals2' rmap2' alloc_param :
  init_param mglob stack (vnew1', locals1', rmap1') sao_param param = ok (vnew2', locals2', rmap2', alloc_param) ->
  forall varg1 varg2,
    (forall pi, sao_param = Some pi -> get_pi param = Some (pi, (varg1, varg2))) ->
    forall sr addr,
      fst alloc_param = Some sr ->
      sub_region_addr Addr se sr = ok addr ->
      varg2 = Vword addr.
Proof.
  rewrite /init_param.
  t_xrbindP=> _.
  case: Mvar.get => //.
  case: sao_param => [pi|].
  + t_xrbindP => _ _ _.
    case: Mvar.get => //.
    case: Mvar.get => //.
    case: Mvar.get => //.
    move=> [_ _ _ <-] /=.
    move=> varg1 varg2 /(_ _ refl_equal) hpi sr addr [<-].
    rewrite /sub_region_addr /= wrepr0 GRing.addr0 => -[<-].
    have hin: Sv.In param Slots_params.
    + by apply in_Slots_params; congruence.
    rewrite /Addr (pick_slot_params hin) /Addr_params hpi.
    have [_ [p [-> _]]] := get_pi_wf_arg hpi.
    by rewrite eq_refl zero_extend_u.
  by move=> [_ _ _ <-].
Qed.

Lemma init_params_alloc_params se :
  List.Forall2
    (fun osr varg2 =>
      forall sr addr,
        osr = Some sr ->
        sub_region_addr Addr se sr = ok addr ->
        varg2 = Vword addr)
    (map fst alloc_params) vargs2.
Proof.
  have [hsize1 hsize2] := Forall3_size Huincl.
  elim: sao.(sao_params) vargs1 vargs2 hsize1 hsize2 params get_pi_Forall
    vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params hparams.
  + move=> [|//] [|//] _ _ [|//] _ ??????? [_ _ _ <-].
    by constructor.
  move=> opi sao_params ih [//|varg1 vargs1'] [//|varg2 vargs2'] /= [/ih{}ih] [/ih{}ih] [//|param params'].
  move=> /List_Forall_inv [hpi hforall].
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params'.
  rewrite /init_params /=.
  apply: rbindP=> -[[[vnew1' locals1'] rmap1'] alloc_param] hparam.
  t_xrbindP=> -[[[??]?]?] /ih{}ih _ <- /=.
  constructor; last by apply ih.
  by apply (init_param_alloc_param hparam hpi).
Qed.

Lemma init_params_alloc_params_not_None :
  List.Forall2 (fun osr opi => osr <> None -> opi <> None) (map fst alloc_params) sao.(sao_params).
Proof.
  elim: sao.(sao_params) params vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params hparams.
  + move=> [|//] ??????? [_ _ _ <-].
    by constructor.
  move=> opi sao_params ih [//|x params'].
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params'.
  rewrite /init_params /=.
  apply: rbindP=> -[[[vnew1' locals1'] rmap1'] alloc_param] hparam.
  t_xrbindP=> -[[[??]?]?] /ih{}ih _ <- /=.
  constructor=> //.
  move: hparam.
  t_xrbindP=> _.
  case: Mvar.get => //.
  case: opi => [//|].
  by move=> [_ _ _ <-].
Qed.

Lemma init_params_sarr :
  List.Forall2 (fun opi (x:var_i) => opi <> None -> is_sarr x.(vtype)) sao.(sao_params) params.
Proof.
  elim: sao.(sao_params) params vnew1 locals1 rmap1 vnew2 locals2 rmap2 alloc_params hparams.
  + by move=> [|//] _ _ _ _ _ _ _ _.
  move=> opi sao_params ih [//|x params'].
  move=> vnew0 locals0 rmap0 vnew2' locals2' rmap2' alloc_params'.
  rewrite /init_params /=.
  apply: rbindP=> -[[[vnew1' locals1'] rmap1'] alloc_param] hparam.
  t_xrbindP=> -[[[_ _] _] _] /ih{}ih _ _.
  constructor=> //.
  move: hparam.
  t_xrbindP=> _.
  case: Mvar.get => //.
  case: opi => [pi|//].
  by t_xrbindP.
Qed.

(* [m2] is (at least) [m1] augmented with data [data] at address [rip]. *)
Record extend_mem (m1 m2:mem) (rip:pointer) (data:seq u8) := {
  em_no_overflow : no_overflow rip (Z.of_nat (size data));
    (* [rip] is able to store a block large enough *)
  em_align       : is_align rip U256;
    (* [rip] is 32-bytes aligned (and thus is 1,2,4,8,16-bytes aligned) *)
    (* could be formulated, [forall ws, is_align rip ws] *)
  em_read_old8   : forall p, validw m1 Aligned p U8 -> read m1 Aligned p U8 = read m2 Aligned p U8;
    (* [m2] contains [m1] *)
  em_fresh       : forall p, validw m1 Aligned p U8 -> disjoint_zrange rip (Z.of_nat (size data)) p (wsize_size U8);
   (* the bytes in [rip; rip + Z.of_nat (size data) - 1] are disjoint from the valid bytes of [m1] *)
  em_valid       : forall p, validw m1 Aligned p U8 || between rip (Z.of_nat (size data)) p U8 -> validw m2 Aligned p U8;
    (* [m2] contains at least [m1] and [rip; rip + Z.of_nat (size data) - 1] *)
  em_read_new    : forall i, 0 <= i < Z.of_nat (size data) ->
                     read m2 Aligned (rip + wrepr _ i)%R U8 = ok (nth 0%R data (Z.to_nat i))
    (* the memory at address [rip] contains [data] *)
}.

(* TODO: should we assume init_stk_state = ok ... as section hypothesis and reason about it,
   it would in particular ease the proof of params <> locals, since we would have the properties
   of alloc_stack_spec to reason with. The advantages are not clear. For now, I leave it like this.
*)
(* cf. init_stk_stateI in merge_varmaps_proof *)
Lemma init_stk_state_valid_state ws sz' m3 :
  extend_mem m1 m2 rip global_data ->
  alloc_stack_spec m2 ws sao.(sao_size) sao.(sao_ioff) sz' m3 ->
  rsp = top_stack m3 ->
  vripn <> vrspn ->
  let s1 := {| escs := scs1; evm := Vm.init; emem := m1 |} in
  let s2 := {| escs := scs1; emem := m3; evm :=
       Vm.init.[vrsp0 <- Vword rsp ]
              .[vrip0 <- Vword rip ] |} in
  valid_state (lmap locals1 vnew1) glob_size rsp rip Slots Addr Writable Align
    P empty_table rmap1 Vm.init m2 s1 s2.
Proof.
  clear disjoint_zrange_globals_locals rsp_align rip_align.
  move=> hext hass hrsp hneq /=.
  constructor=> //=.
  + move=> s w hin hb.
    rewrite hass.(ass_valid); apply /orP.
    case /in_Slots : hin => [hin|[hin|hin]].
    + left.
      apply hext.(em_valid).
      apply /orP; right.
      apply: zbetween_trans hb.
      rewrite /Addr (pick_slot_globals hin).
      by apply (zbetween_Addr_globals hin).
    + right.
      apply: zbetween_trans hb.
      rewrite /Addr (pick_slot_locals hin).
      have := (ass_add_ioff hass). rewrite -{1 2}hrsp => hadd.
      have := zbetween_Addr_locals_ioff hadd hin.
      by rewrite hrsp.
    left.
    have /in_Slots_params := hin.
    case hpi: get_pi => [[pi [v1 v2]]|//] _.
    have [i [p [? hargp]]] := get_pi_wf_arg hpi; subst v2.
    apply hargp.(wap_valid).
    apply: zbetween_trans hb.
    rewrite /Addr (pick_slot_params hin) /Addr_params hpi.
    rewrite eq_refl zero_extend_u.
    by apply (zbetween_le _ (get_pi_size_le hpi)).
  + move=> s w hin hvalid.
    case /in_Slots : hin => [hin|[hin|hin]].
    + rewrite /Addr (pick_slot_globals hin).
      apply (disjoint_zrange_incl_l (zbetween_Addr_globals hin)).
      by apply: hext.(em_fresh) hvalid.
    + rewrite /Addr (pick_slot_locals hin).
      apply: (disjoint_zrange_incl_l (zbetween_Addr_locals hin)).
      have hvalid2: validw m2 Aligned w U8.
      + apply hext.(em_valid).
        by rewrite hvalid.
      have hdisj := hass.(ass_fresh) hvalid2.
      split.
      + by apply no_overflow_size.
      + by apply is_align_no_overflow; apply is_align8.
      by rewrite hrsp; apply or_comm.
    have /in_Slots_params := hin.
    case hpi: get_pi => [[pi [v1 v2]]|//] _.
    have [i [p [? hargp]]] := get_pi_wf_arg hpi; subst v2.
    apply: disjoint_zrange_incl_l (hargp.(wap_fresh) hvalid).
    rewrite /Addr (pick_slot_params hin) /Addr_params hpi.
    rewrite eq_refl zero_extend_u.
    by apply (zbetween_le _ (get_pi_size_le hpi)).
  + move=> p hvalid.
    rewrite hass.(ass_valid); apply /orP; left.
    by apply hext.(em_valid); apply /orP; left.
  + move=> p hvalid.
    by rewrite hass.(ass_valid); apply /orP; left.
  + by move=> p hvalid1 hvalid2 hdisj; apply hass.(ass_read_old8).
  + by rewrite Vm.setP_eq /= cmp_le_refl orbT.
  + rewrite Vm.setP_neq; first by rewrite Vm.setP_eq /= cmp_le_refl orbT.
    by apply/eqP;rewrite /vrip0 /vrsp0; congruence.
  + move=> x /= hget hnnew.
    rewrite !Vm.setP_neq //; apply /eqP.
    + by have /rsp_in_new /= := init_local_map_wf_pmap; congruence.
    by have /rip_in_new /= := init_local_map_wf_pmap; congruence.
  + split=> //=.
    by move=> ? /Sv.empty_spec.
  + apply init_local_map_wf_rmap.
    move=> i hi /=.
    rewrite -hass.(ass_read_old8); first by apply hext.(em_read_new).
    apply hext.(em_valid); apply /orP; right.
    apply: between_byte hi.
    + by apply hext.(em_no_overflow).
    by apply zbetween_refl.
  + move=> w hvalid.
    rewrite -hass.(ass_read_old8); first by apply hext.(em_read_old8).
    by apply hext.(em_valid); apply /orP; left.
  + move=> p hb.
    by apply hext.(em_valid); apply /orP; right.
Qed.

(* It is not clear whether we should use the size of the value [varg1] or the
   size of the corresponding parameter [x] in this definition. Initially,
   we used the latter, but at one point it seemed easier to use the former.
   Since several proofs have been reworked since, this choice could be rethought.
   At least, it works with the current formulation.
*)
Definition disjoint_from_writable_param p wptr varg1 varg2 :=
  forall p2, wptr = Some true -> varg2 = @Vword Uptr p2 ->
  disjoint_zrange p2 (size_val varg1) p (wsize_size U8).

(* [disjoint_from_writable_params] correctly captures the notion of being
   disjoint from writable param slots
*)
Lemma disjoint_from_writable_params_param_slots p :
  Forall3 (disjoint_from_writable_param p)
    (map (omap pp_writable) sao.(sao_params)) vargs1 vargs2 ->
  forall s, Sv.In s Slots_params -> Writable_params s ->
  disjoint_zrange (Addr_params s) (size_slot s) p (wsize_size U8).
Proof.
  move=> hdisj s hin.
  have /in_Slots_params := hin.
  case hpi: get_pi => [[pi [v1 v2]]|//] _.
  have [_ [p2 [? _]]] := get_pi_wf_arg hpi; subst v2.
  rewrite /Writable_params /Addr_params hpi => hw.
  have [i [hnth1 hnth2 hnth3 hnth4]] := get_pi_nth hpi.
  have hi := nth_not_default hnth2 ltac:(discriminate).
  have := Forall3_nth hdisj None (Vbool true) (Vbool true);
    rewrite size_map => /(_ _ hi).
  rewrite (nth_map None) //.
  rewrite hnth2 /= hw hnth4 => /(_ _ refl_equal refl_equal).
  apply disjoint_zrange_incl_l.
  rewrite eq_refl zero_extend_u.
  apply: zbetween_le.
  rewrite hnth3.
  by apply: get_pi_size_le hpi.
Qed.

(* If p is [disjoint_from_writable_params] and from local variables, it is
   disjoint from all writable params.
*)
Corollary disjoint_from_writable_params_all_slots p :
  Forall3 (disjoint_from_writable_param p)
    (map (omap pp_writable) sao.(sao_params)) vargs1 vargs2 ->
  disjoint_zrange rsp sao.(sao_size) p (wsize_size U8) ->
  forall s, Sv.In s Slots -> Writable s ->
  disjoint_zrange (Addr s) (size_slot s) p (wsize_size U8).
Proof.
  move=> hdisj1 hdisj2 s hin hw.
  case /in_Slots : hin => [hin|[hin|hin]].
  + by move: hw; rewrite /Writable (pick_slot_globals hin).
  + rewrite /Addr (pick_slot_locals hin).
    by apply (disjoint_zrange_incl_l (zbetween_Addr_locals hin)).
  rewrite /Writable (pick_slot_params hin) in hw.
  rewrite /Addr (pick_slot_params hin).
  by apply (disjoint_from_writable_params_param_slots hdisj1).
Qed.

End LOCAL.

Lemma valid_state_extend_mem pmap rsp Slots Addr Writable Align table rmap se m0 s1 s2 :
  wf_Slots Slots Addr Writable Align ->
  valid_state pmap glob_size rsp rip Slots Addr Writable Align P table rmap se m0 s1 s2 ->
  extend_mem (emem s1) (emem s2) rip global_data ->
  forall table' rmap' se' s1' s2',
    valid_state pmap glob_size rsp rip Slots Addr Writable Align P table' rmap' se' m0 s1' s2' ->
    validw (emem s1) =3 validw (emem s1') ->
    validw (emem s2) =3 validw (emem s2') ->
    extend_mem (emem s1') (emem s2') rip global_data.
Proof.
  move=> hwf hvs hext table' rmap' se' s1' s2' hvs' hvalideq1 hvalideq2.
  case:(hext) => hover halign hold hfresh hvalid hnew.
  split=> //=.
  + exact: vs_eq_mem hvs'.
  + by move=> p hvalidp; apply hfresh; rewrite hvalideq1.
  + by move=> p; rewrite -hvalideq1 -hvalideq2; apply hvalid.
  move=> i hi.
  have hb: between rip glob_size (rip + wrepr _ i)%R U8.
  + apply: between_byte hi => //.
    by apply zbetween_refl.
  have hvalid0: validw m0 Aligned (rip + wrepr _ i)%R U8.
  + exact: vs_glob_valid.
  have hnvalid1: ~ validw (emem s1) Aligned (rip + wrepr _ i)%R U8.
  + move=> /hfresh.
    by apply zbetween_not_disjoint_zrange.
  have hdisjoint: forall s, Sv.In s Slots -> Writable s ->
    disjoint_zrange (Addr s) (size_slot s) (rip + wrepr Uptr i) (wsize_size U8).
  + move=> s hin hw.
    apply disjoint_zrange_sym.
    apply (disjoint_zrange_incl_l hb).
    apply hwf.(wfsl_not_glob) => //.
    by lia.
  rewrite -hnew // -vs_unchanged //; last by rewrite -hvalideq1.
  exact: vs_unchanged.
Qed.

Section PROC.

Variable (P' : sprog).
Hypothesis P'_globs : P'.(p_globs) = [::].

Context
  (shparams : slh_lowering.sh_params)
  (hshparams : slh_lowering_proof.h_sh_params shparams)
  (saparams : stack_alloc_params)
  (hsaparams : h_stack_alloc_params saparams).

Context
  (is_move_op : asm_op_t -> bool)
  (fresh_var_ident  : v_kind -> Uint63.int -> string -> stype -> Ident.ident)
  (pp_sr : sub_region -> pp_error).

Context
  (is_move_opP :
    forall op vx v,
      is_move_op op ->
      exec_sopn (Oasm op) [:: vx ] = ok v ->
      List.Forall2 value_uincl v [:: vx ]).

Local Lemma clone_ty : forall x n, vtype (clone fresh_var_ident x n) = vtype x.
Proof. by []. Qed.

Notation alloc_fd   := (alloc_fd shparams saparams is_move_op fresh_var_ident pp_sr P).
Notation alloc_i    := (alloc_i shparams saparams is_move_op fresh_var_ident pp_sr).
Notation alloc_prog := (alloc_prog shparams saparams is_move_op fresh_var_ident pp_sr).

Variable (local_alloc : funname -> stk_alloc_oracle_t).
Hypothesis Halloc_fd : forall fn fd,
  get_fundef P.(p_funcs) fn = Some fd ->
  exists2 fd', alloc_fd P'.(p_extra) mglob local_alloc fn fd = ok fd' &
               get_fundef P'.(p_funcs) fn = Some fd'.

(* RAnone -> export function (TODO: rename RAexport?) *)
Definition enough_size m sao :=
  let sz := sao_frame_size sao in
  allocatable_stack m (sao.(sao_max_size) - sz).

Record wf_sao rsp m sao := {
  wf_sao_size     : enough_size m sao;
  wf_sao_align    : is_align rsp sao.(sao_align);
}.

Lemma stack_stable_wf_sao rsp m1 m2 sao :
  stack_stable m1 m2 ->
  wf_sao rsp m1 sao ->
  wf_sao rsp m2 sao.
Proof.
  move=> hss [hsize halign]; split=> //.
  rewrite /enough_size /allocatable_stack.
  by rewrite -(ss_top_stack hss) -(ss_limit hss).
Qed.

Section SYNTACTIC_INVARIANTS.

(* We prove four properties for which we don't need semantics :
   - wft_VARS
   - wfr_VARS_ZONE
   - wfr_VARS_STATUS
   - inclusion of table.(vars)

   We need these to justify the merge. In the proofs involving the merge, we
   have semantical hypothesis about one argument only. We need some info on the
   other argument to be able to conclude.
*)

Definition wf_table_vars table rmap :=
  [/\ wft_VARS table, wfr_VARS_ZONE (vars table) rmap & wfr_VARS_STATUS (vars table) rmap].

Context (pmap : pos_map) (sao : stk_alloc_oracle_t).

Let Pi_r (i:instr_r) :=
  forall table1 rmap1 table2 rmap2 ii c2,
  alloc_i pmap local_alloc P sao (table1, rmap1) (MkI ii i) = ok (table2, rmap2, c2) ->
  wf_table_vars table1 rmap1 ->
  wf_table_vars table2 rmap2 /\ Sv.Subset table1.(vars) table2.(vars).

Let Pi (i:instr) :=
  forall table1 rmap1 table2 rmap2 c2,
  alloc_i pmap local_alloc P sao (table1, rmap1) i = ok (table2, rmap2, c2) ->
  wf_table_vars table1 rmap1 ->
  wf_table_vars table2 rmap2 /\ Sv.Subset table1.(vars) table2.(vars).

Let Pc (c1:cmd) :=
  forall table1 rmap1 table2 rmap2 c2,
  fmapM (alloc_i pmap local_alloc P sao) (table1, rmap1) c1 = ok (table2, rmap2, c2) ->
  wf_table_vars table1 rmap1 ->
  wf_table_vars table2 rmap2 /\ Sv.Subset table1.(vars) table2.(vars).

Local Lemma Wmk i ii: Pi_r i -> Pi (MkI ii i).
Proof. by move=> Hi ?????; apply Hi. Qed.

Local Lemma Wnil : Pc [::].
Proof. by move=> ????? /= [<- <- _]; split. Qed.

Local Lemma Wcons i c:  Pi i -> Pc c -> Pc (i::c).
Proof.
  move=> Hi Hc table1 rmap1 table2 rmap2 c2 /=.
  t_xrbindP=> -[[table1' rmap1'] ?] /Hi{}Hi [[{}table2 {}rmap2] ?] /Hc{}Hc /= [<- <-] _ hvars1.
  have [hvars1' hsubset1] := Hi hvars1.
  have [hvars2 hsubset2] := Hc hvars1'.
  split=> //.
  by clear -hsubset1 hsubset2; SvD.fsetdec.
Qed.

Lemma wft_VARS_remove_binding_lval table r :
  wft_VARS table ->
  wft_VARS (remove_binding_lval table r).
Proof.
  case: r => //=.
  + move=> x hwft y ey /=.
    rewrite Mvar.removeP.
    case: eqP => // _.
    by apply hwft.
  + move=> _ _ _ x _ hwft y ey /=.
    rewrite Mvar.removeP.
    case: eqP => // _.
    by apply hwft.
  move=> _ _ _ x _ hwft y ey /=.
  rewrite Mvar.removeP.
  case: eqP => // _.
  by apply hwft.
Qed.

Lemma wft_VARS_remove_binding_lvals table rs :
  wft_VARS table ->
  wft_VARS (remove_binding_lvals table rs).
Proof.
  elim: rs table => [//|r rs ih] table /= hvars.
  by apply /ih /wft_VARS_remove_binding_lval.
Qed.

(* cf. set_lvE in propagate_inline_proof *)
Lemma update_tableE table r oe :
  (exists x e, [/\ r = Lvar x, oe = Some e & update_table table r oe = table_set_var table x e])
  \/ update_table table r oe = table.
Proof.
  case: oe => [e|] /=; last by right.
  case: r => /=; try by move=> >; right.
  move=> x.
  by left; exists x, e.
Qed.

Lemma wft_VARS_table_set_var table x e :
  Sv.Subset (read_e e) table.(vars) ->
  wft_VARS table ->
  wft_VARS (table_set_var table x e).
Proof.
  move=> hsubset hvars1 y ey /=.
  rewrite Mvar.setP.
  case: eqP => _.
  + by move=> [<-].
  by apply hvars1.
Qed.

Local Lemma Wasgn r t ty e: Pi_r (Cassgn r t ty e).
Proof.
  move=> table1 rmap1 table2 rmap2 ii c2 /=.
  case: is_sarr.
  + t_xrbindP=> -[[{}table2 {}rmap2] i] hinit [<- <- _] [hvars1 hvarsz1 hvarss1].
    suff: wf_table_vars table2 rmap2 /\ Sv.Subset table1.(vars) table2.(vars).
    + move=> [[hvars2 hvarsz2 hvarss2] hsubset].
      rewrite /wf_table_vars remove_binding_lval_vars.
      do 2!split=> //.
      by apply wft_VARS_remove_binding_lval.
    move: hinit; rewrite /alloc_array_move_init.
    case: ifP => _.
    + case: r => // x.
      t_xrbindP=> sr /get_sub_regionP hsr <- <- _.
      do 2!split=> //.
      + by apply (wfr_VARS_ZONE_set_move (hvarsz1 _ _ hsr) hvarsz1).
      by apply wfr_VARS_STATUS_set_move_status.
    rewrite /alloc_array_move.
    t_xrbindP=> -[[[[[table1' sry] statusy]?]?]?] htable1'.
    have [hvars1' hsubset1 sry_vars statusy_vars]: [/\
      wft_VARS table1',
      Sv.Subset table1.(vars) table1'.(vars),
      wf_vars_zone table1'.(vars) (sr_zone sry) &
      wf_vars_status table1'.(vars) statusy].
    + case: e htable1' => //=.
      + t_xrbindP=> y vpky hkindy.
        case: vpky hkindy => [vpky|//] hkindy.
        t_xrbindP=> -[sry' statusy'] /(get_gsub_region_statusP hkindy) hgvalidy.
        t_xrbindP=> _ _ <- <- <- _ _ _.
        split=> //.
        + by apply (check_gvalid_wf_vars_zone hvarsz1 hgvalidy).
        by apply (check_gvalid_wf_vars_status hvarss1 hgvalidy).
      t_xrbindP=> aa ws len y e vpky hkindy.
      case: vpky hkindy => [vpky|//] hkindy.
      t_xrbindP=> -[sry' statusy'] /(get_gsub_region_statusP hkindy) hgvalidy.
      t_xrbindP=> -[table1'' e1] /get_symbolic_of_pexprP hsym.
      case hsub: sub_region_status_at_ofs => [sry'' statusy''].
      t_xrbindP=> _ _ _ _ <- <- <- _ _ _.
      have hsubset := symbolic_of_pexpr_subset_vars hsym hvars1.
      have hsubset' := symbolic_of_pexpr_subset_read hsym hvars1.
      split=> //.
      + by apply (wft_VARS_symbolic_of_pexpr hsym hvars1).
      + apply: sub_region_status_at_ofs_wf_vars_zone hsub.
        + apply (subset_vars_wf_vars_zone hsubset).
          by apply (check_gvalid_wf_vars_zone hvarsz1 hgvalidy).
        + have := @mk_ofs_int_vars aa ws e1.
          by clear -hsubset'; SvD.fsetdec.
        rewrite /read_e /=.
        by clear; SvD.fsetdec.
      + apply: sub_region_status_at_ofs_wf_vars_status hsub.
        apply (subset_vars_wf_vars_status hsubset).
        by apply (check_gvalid_wf_vars_status hvarss1 hgvalidy).
    have hvarsz1': wfr_VARS_ZONE table1'.(vars) rmap1.
    + move=> ?? /hvarsz1.
      by apply (subset_vars_wf_vars_zone hsubset1).
    have hvarss1': wfr_VARS_STATUS table1'.(vars) rmap1.
    + move=> ??.
      apply (subset_vars_wf_vars_status hsubset1).
      by apply hvarss1.
    case: r => //.
    + move=> x.
      have hvarsz1'': wfr_VARS_ZONE table1'.(vars) (set_move rmap1 x sry statusy).
      + by apply wfr_VARS_ZONE_set_move.
      have hvarss1'': wfr_VARS_STATUS table1'.(vars) (set_move rmap1 x sry statusy).
      + by apply wfr_VARS_STATUS_set_move_status.
      case: get_local => [pk|//].
      case: pk.
      + t_xrbindP=> _ _ _ _ _ _ <- <- _.
        by split.
      + t_xrbindP=> _ _ _ <- <- _.
        by split.
      move=> ?????.
      case: ifP => _.
      + move=> [<- <- _].
        by split.
      t_xrbindP=> _ _ <- <- _.
      do 2!split=> //=.
      apply wfr_VARS_STATUS_set_word_status => //.
      rewrite /wf_vars_zone /= /read_slice /= /read_e /=.
      by clear; SvD.fsetdec.
    move=> aa ws len x e'.
    case: get_local => [_|//].
    t_xrbindP=> -[srx statusx] /get_sub_region_statusP [hsrx ->].
    t_xrbindP=> -[table1'' e1] /get_symbolic_of_pexprP hsym.
    case hsub: sub_region_status_at_ofs => [srx' statusx'].
    t_xrbindP=> _ <- <- _.
    have hsubset2 := symbolic_of_pexpr_subset_vars hsym hvars1'.
    have hsubset' := symbolic_of_pexpr_subset_read hsym hvars1'.
    split=> /=; last by clear -hsubset1 hsubset2; SvD.fsetdec.
    split.
    + by apply (wft_VARS_symbolic_of_pexpr hsym hvars1').
    + move=> ?? /hvarsz1'.
      by apply (subset_vars_wf_vars_zone hsubset2).
    apply wfr_VARS_STATUS_set_move_status => //.
    + apply wf_vars_status_insert_status.
      + apply (subset_vars_wf_vars_status hsubset2).
        by apply hvarss1'.
      + by apply (subset_vars_wf_vars_status hsubset2).
      + have := @mk_ofs_int_vars aa ws e1.
        by clear -hsubset'; SvD.fsetdec.
      + rewrite /read_e /=.
        by clear; SvD.fsetdec.
      move=> ??.
      apply (subset_vars_wf_vars_status hsubset2).
      by apply hvarss1'.
  t_xrbindP=> ote hsym.
  case hote: (match ote with | Some _ => _ | _ => _ end) => [table1' oe].
  t_xrbindP=> _ _ [{}rmap2 r2] hlval <- <- _.
  move=> [hvars1 hvarsz1 hvarss1].
  have [hvars1' hsubset hread]: [/\
    wft_VARS table1',
    Sv.Subset table1.(vars) table1'.(vars) &
    forall e, oe = Some e -> Sv.Subset (read_e e) table1'.(vars)].
  + case: ote hote hsym => [[table e']|] [<- <-] hsym; last by split.
    split.
    + by apply (wft_VARS_symbolic_of_pexpr hsym hvars1).
    + by apply (symbolic_of_pexpr_subset_vars hsym hvars1).
    move=> _ [<-].
    by apply (symbolic_of_pexpr_subset_read hsym hvars1).
  have hvarsz1': wfr_VARS_ZONE table1'.(vars) rmap1.
  + move=> ?? /hvarsz1.
    by apply (subset_vars_wf_vars_zone hsubset).
  have hvarss1': wfr_VARS_STATUS table1'.(vars) rmap1.
  + move=> ??.
    apply (subset_vars_wf_vars_status hsubset).
    by apply hvarss1.
  have hvarsz2 := wfr_VARS_ZONE_alloc_lval hlval hvarsz1'.
  have hvarss2 := wfr_VARS_STATUS_alloc_lval hlval hvarsz1' hvarss1'.
  have [] := update_tableE (remove_binding_lval table1' r) r oe; last first.
  + move=> ->.
    rewrite /wf_table_vars remove_binding_lval_vars.
    do 2!split=> //.
    by apply wft_VARS_remove_binding_lval.
  move=> [x [e' [?? ->]]]; subst r oe.
  do 2!split=> //.
  apply wft_VARS_table_set_var.
  + by apply hread.
  by apply (wft_VARS_remove_binding_lval hvars1').
Qed.

Local Lemma Wopn xs t o es: Pi_r (Copn xs t o es).
Proof.
  move=> table1 rmap1 table2 rmap2 ii c2 /=.
  case: is_protect_ptr_fail => [[[r ?]?]|].
  + t_xrbindP=> -[{}rmap2 i2] halloc <- <- _.
    move=> [hvars1 hvarsz1 hvarss1].
    rewrite /wf_table_vars remove_binding_lval_vars.
    do 2!split=> //.
    + by apply wft_VARS_remove_binding_lval.
    + by apply (wfr_VARS_ZONE_alloc_protect_ptr halloc).
    by apply (wfr_VARS_STATUS_alloc_protect_ptr halloc).
  case: is_swap_array.
  + t_xrbindP=> -[{}rmap2 i2] halloc <- <- _.
    rewrite /wf_table_vars remove_binding_lvals_vars.
    move=> [*]; do 2!split=> //.
    + by apply wft_VARS_remove_binding_lvals.
    + by apply (wfr_VARS_ZONE_alloc_array_swap halloc).
    by apply (wfr_VARS_STATUS_alloc_array_swap halloc).
  t_xrbindP=> {}table2 htable2 _ _ [{}rmap2 xs2] hallocs <- <- _.
  move=> [hvars1 hvarsz1 hvarss1].
  have hvarsz2 := wfr_VARS_ZONE_alloc_lvals hallocs hvarsz1.
  have hvarss2 := wfr_VARS_STATUS_alloc_lvals hallocs hvarsz1 hvarss1.
  have hdefault:
    Ok pp_error_loc (remove_binding_lvals table1 xs) = ok table2 ->
      wf_table_vars table2 rmap2 /\ Sv.Subset table1.(vars) table2.(vars).
  + move=> [<-].
    rewrite /wf_table_vars remove_binding_lvals_vars.
    do 2!split=> //.
    by apply wft_VARS_remove_binding_lvals.
  case: xs hdefault hallocs htable2 => [//|r [|//]] hdefault hallocs.
  case: o hallocs => // o hallocs.
  case: es => [//|e [|//]].
  case: ifP => // _.
  t_xrbindP=> ote hsym.
  case hote: (match ote with | Some _ => _ | _ => _ end) => [table1' oe].
  move=> [<-].
  have [hvars1' hsubset hread]: [/\
    wft_VARS table1',
    Sv.Subset table1.(vars) table1'.(vars) &
    forall e, oe = Some e -> Sv.Subset (read_e e) table1'.(vars)].
  + case: ote hote hsym => [[table e']|] [<- <-] hsym; last by split.
    split.
    + by apply (wft_VARS_symbolic_of_pexpr hsym hvars1).
    + by apply (symbolic_of_pexpr_subset_vars hsym hvars1).
    move=> _ [<-].
    by apply (symbolic_of_pexpr_subset_read hsym hvars1).
  have hvarsz2': wfr_VARS_ZONE table1'.(vars) rmap2.
  + move=> ?? /hvarsz2.
    by apply (subset_vars_wf_vars_zone hsubset).
  have hvarss2': wfr_VARS_STATUS table1'.(vars) rmap2.
  + move=> ??.
    apply (subset_vars_wf_vars_status hsubset).
    by apply hvarss2.
  have [] := update_tableE (remove_binding_lval table1' r) r oe; last first.
  + move=> ->.
    rewrite /wf_table_vars remove_binding_lval_vars.
    do 2!split=> //.
    by apply wft_VARS_remove_binding_lval.
  move=> [x [e' [?? ->]]]; subst r oe.
  do 2!split=> //.
  apply wft_VARS_table_set_var.
  + by apply hread.
  by apply (wft_VARS_remove_binding_lval hvars1').
Qed.

Local Lemma Wsyscall xs o es: Pi_r (Csyscall xs o es).
Proof.
  move=> table1 rmap1 table2 rmap2 ii c2 /=.
  t_xrbindP=> -[{}rmap2 {}c2] halloc [<- <- _].
  move=> [hvars1 hvarsz1 hvarss1].
  rewrite /wf_table_vars remove_binding_lvals_vars.
  do 2!split=> //.
  + by apply wft_VARS_remove_binding_lvals.
  + by apply (wfr_VARS_ZONE_alloc_syscall halloc).
  by apply (wfr_VARS_STATUS_alloc_syscall halloc).
Qed.

(* in practice, vars = Sv.inter var1 vars2, but we don't need it *)
Lemma wfr_VARS_ZONE_merge vars1 vars2 rmap1 rmap2 vars :
  wfr_VARS_ZONE vars1 rmap1 ->
  wfr_VARS_ZONE vars2 rmap2 ->
  wfr_VARS_ZONE (Sv.inter vars1 vars2) (merge vars rmap1 rmap2).
Proof.
  move=> hvarsz1 hvarsz2.
  move=> x sr /=.
  rewrite Mvar.map2P //.
  case hsr1: Mvar.get => [sr1|//].
  case hsr2: Mvar.get => [sr2|//].
  case: eqP => // ? [?]; subst sr1 sr2.
  have := hvarsz1 _ _ hsr1.
  have := hvarsz2 _ _ hsr2.
  by rewrite /wf_vars_zone; clear; SvD.fsetdec.
Qed.

Lemma wf_vars_interval_alt vars i :
  all (fun s => Sv.subset (read_slice s) vars) i ->
  wf_vars_interval vars i.
Proof.
  rewrite /wf_vars_interval.
  elim: i => [|s i ih] /=.
  + move=> _.
    by clear; SvD.fsetdec.
  move=> /andP [/Sv.subset_spec hsubset1 /ih hsubset2].
  by clear -hsubset1 hsubset2; SvD.fsetdec.
Qed.

Lemma wf_vars_status_merge_status vars x status1 status2 :
  wf_vars_status vars (odflt Unknown (merge_status vars x status1 status2)).
Proof.
  case: status1 => [status1|//].
  case: status2 => [status2|//] /=.
  case: status1 status2 => [||i1] [||i2] //=.
  + case: ifP => //= hall.
    apply wf_vars_interval_alt.
    apply: sub_all hall.
    by move=> ? /andP[].
  + case: ifP => //= hall.
    apply wf_vars_interval_alt.
    apply: sub_all hall.
    by move=> ? /andP[].
  case hmerge: merge_interval => [i|//].
  case: ifP => //= hall.
  apply wf_vars_interval_alt.
  apply: sub_all hall.
  by move=> ? /andP[].
Qed.

Lemma wfr_VARS_STATUS_merge vars rmap1 rmap2 :
  wfr_VARS_STATUS vars (merge vars rmap1 rmap2).
Proof.
  move=> r x.
  rewrite /get_var_status /get_status /get_status_map /=.
  rewrite Mr.map2P //.
  case: Mr.get => [sm1|//].
  case: Mr.get => [sm2|//] /=.
  case: ifP => //= _.
  rewrite Mvar.map2P //.
  by apply wf_vars_status_merge_status.
Qed.

Lemma wf_table_vars_merge X table1 rmap1 table2 rmap2 :
  wf_table_vars table1 rmap1 ∧ Sv.Subset X (vars table1) →
  wf_table_vars table2 rmap2 ∧ Sv.Subset X (vars table2) →
  wf_table_vars (merge_table table1 table2) (merge (Sv.inter (vars table1) (vars table2)) rmap1 rmap2)
  ∧ Sv.Subset X (Sv.inter (vars table1) (vars table2)).
Proof.
  move=> [[hvars1' hvarsz1' hvarss1'] hsubset1] [[hvars2  hvarsz2 hvarss2] hsubset2].
  split; last by clear -hsubset1 hsubset2; SvD.fsetdec.
  split=> /=.
  + by apply wft_VARS_merge_table.
  + by apply wfr_VARS_ZONE_merge.
  by apply wfr_VARS_STATUS_merge.
Qed.

Local Lemma Wif e c1 c2: Pc c1 -> Pc c2 -> Pi_r (Cif e c1 c2).
Proof.
  move=> Hc1 Hc2 table1 rmap1 table2 rmap2 ii c /=.
  t_xrbindP=> ? _ [[table1' rmap1']?] /Hc1{}Hc1.
  t_xrbindP=> -[[{}table2 {}rmap2] ?] /Hc2{}Hc2 [<- <- _] /= hvars.
  apply wf_table_vars_merge; auto.
Qed.

Local Lemma Wfor v dir lo hi c: Pc c -> Pi_r (Cfor v (dir,lo,hi) c).
Proof. done. Qed.

Lemma loop2_invariant ii check_c2 n table rmap table' rmap' e' c1' c2':
  (forall table rmap table1 rmap1 table2 rmap2 e' c1' c2',
    check_c2 table rmap = ok ((table1, rmap1), (table2, rmap2), (e', c1', c2')) ->
    wf_table_vars table rmap ->
    (wf_table_vars table1 rmap1 /\ Sv.Subset table.(vars) table1.(vars)) /\
    (wf_table_vars table2 rmap2 /\ Sv.Subset table.(vars) table2.(vars))) ->
  loop2 ii check_c2 n table rmap = ok (table', rmap', (e', c1', c2')) ->
  wf_table_vars table rmap ->
  wf_table_vars table' rmap' /\ Sv.Subset table.(vars) table'.(vars).
Proof.
  move=> hcheck_c2.
  elim: n table rmap => //= n hrec table rmap.
  t_xrbindP=> -[[[table1 rmap1] [table2 rmap2]] [[e1 c11] c12]] hc2.
  move=> + hvarst.
  have [h1 h2] := hcheck_c2 _ _ _ _ _ _ _ _ _ hc2 hvarst.
  case: ifP => _.
  + by move=> [<- <- _ _ _].
  have h : wf_table_vars table rmap /\ Sv.Subset (vars table) (vars table) by split.
  have [hwf hsub]:= wf_table_vars_merge h h2.
  move=> /hrec{} [] // ? /= hsub'; split => //.
  clear -hsub hsub'; SvD.fsetdec.
Qed.

Local Lemma Wwhile a c e ei c': Pc c -> Pc c' -> Pi_r (Cwhile a c e ei c').
Proof.
  move=> Hc Hc' table1 rmap1 table2 rmap2 ii c2 /=.
  t_xrbindP=> -[[{}table2 {}rmap2] [[??]?]] hloop [<- <- _].
  apply: loop2_invariant hloop.
  clear -Hc Hc'.
  move=> table rmap table1 rmap1 table2 rmap2 e' c1' c2'.
  t_xrbindP=> -[[table1' rmap1'] ?] /Hc{}Hc.
  t_xrbindP=> _ _ [[table2' rmap2'] _] /Hc'{}Hc' [<- <- <- <- _ _ _] hvarst1.
  have [hvarst1' hsubset1] := Hc hvarst1.
  have [hvarst2 hsubset2] := Hc' hvarst1'.
  do 2!split=> //.
  by clear -hsubset1 hsubset2; SvD.fsetdec.
Qed.

Local Lemma Wcall xs f es: Pi_r (Ccall xs f es).
Proof.
  move=> table1 rmap1 table2 rmap2 ii c2 /=.
  t_xrbindP=> _ -[{}rmap2 i2] halloc <- <- _.
  move=> [hvars1 hvarsz1 hvarss1].
  move: halloc; rewrite /alloc_call.
  t_xrbindP=> -[rmap1' l] hargs.
  t_xrbindP => -[{}rmap2 ?] hres _ _ _ /= <-.
  have [{}hargs _] := alloc_call_argsE hargs.
  rewrite /wf_table_vars remove_binding_lvals_vars.
  do 2 split=> //.
  + by apply wft_VARS_remove_binding_lvals.
  + have hvarsz1' := wfr_VARS_ZONE_alloc_call_args_aux hargs hvarsz1.
    apply (wfr_VARS_ZONE_alloc_call_res hres) => //.
    by apply (alloc_call_args_aux_wfr_VARS_ZONE_sub_region hargs).
  have hvarss1' := wfr_VARS_STATUS_alloc_call_args_aux hargs hvarsz1 hvarss1.
  by apply (wfr_VARS_STATUS_alloc_call_res hres).
Qed.

Lemma alloc_i_invariant table1 rmap1 i table2 rmap2 c2 :
  alloc_i pmap local_alloc P sao (table1, rmap1) i = ok (table2, rmap2, c2) ->
  wf_table_vars table1 rmap1 ->
  wf_table_vars table2 rmap2 /\ Sv.Subset table1.(vars) table2.(vars).
Proof.
  exact: (instr_Rect Wmk Wnil Wcons Wasgn Wopn Wsyscall Wif Wfor Wwhile Wcall).
Qed.

Lemma alloc_is_invariant table1 rmap1 c1 table2 rmap2 c2 :
  fmapM (alloc_i pmap local_alloc P sao) (table1, rmap1) c1 = ok (table2, rmap2, c2) ->
  wf_table_vars table1 rmap1 ->
  wf_table_vars table2 rmap2 /\ Sv.Subset table1.(vars) table2.(vars).
Proof.
  exact: (cmd_rect Wmk Wnil Wcons Wasgn Wopn Wsyscall Wif Wfor Wwhile Wcall).
Qed.

End SYNTACTIC_INVARIANTS.

(* takes into account the padding due to the alignment of the stack of export functions *)
Definition sf_total_stack e :=
  if is_RAnone e.(sf_return_address) then
    e.(sf_stk_max) + wsize_size e.(sf_align) - 1
  else e.(sf_stk_max).

Definition alloc_ok (SP:sprog) fn m2 :=
  forall fd, get_fundef (p_funcs SP) fn = Some fd ->
  allocatable_stack m2 (sf_total_stack fd.(f_extra)) /\
  (~ is_RAnone fd.(f_extra).(sf_return_address) -> is_align (top_stack m2) fd.(f_extra).(sf_align)).

(* [glob_size] and [rip] were section variables in stack_alloc_proof_1.v, they
   are section variables in this file too. Can we put everything in the same
   section? Probably not if the file is split.
*)
Notation wf_args m1 m2 fn vargs1 vargs2 :=
  (wf_args glob_size rip m1 m2
    (map (omap pp_writable) (local_alloc fn).(sao_params))
    (map (oapp pp_align U8) (local_alloc fn).(sao_params))
    vargs1 vargs2).
Notation wf_results vargs1 vargs2 fn vres1 vres2 :=
  (Forall3 (wf_result vargs1 vargs2) (local_alloc fn).(sao_return) vres1 vres2).
Notation value_eq_or_in_mem_args m fn vargs1 vargs2 :=
  (Forall3 (value_eq_or_in_mem m) (local_alloc fn).(sao_params) vargs1 vargs2).
Notation value_eq_or_in_mem_res m fn vres1 vres2 :=
  (Forall3 (value_eq_or_in_mem m) (local_alloc fn).(sao_return) vres1 vres2).

Definition mem_unchanged_params ms m0 m wptrs vargs1 vargs2 :=
  forall p, validw m0 Aligned p U8 -> ~ validw ms Aligned p U8 ->
  Forall3 (disjoint_from_writable_param p) wptrs vargs1 vargs2 ->
  read m0 Aligned p U8 = read m Aligned p U8.

Notation mem_unchanged_params_fn ms m0 m fn vargs1 vargs2 :=
  (mem_unchanged_params ms m0 m
    (map (omap pp_writable) (local_alloc fn).(sao_params)) vargs1 vargs2).

Lemma wf_table_table_set_var table x e vm vme :
  Sv.Subset (read_e e) table.(vars) ->
  (forall v1,
    get_var true vm x = ok v1 ->
    exists2 v2,
      sem_sexpr vme e = ok v2 & value_uincl v1 v2) ->
  wf_table table vme vm ->
  wf_table (table_set_var table x e) vme vm.
Proof.
  move=> hsub hsem [hvars1 hundef1 hsem1].
  split=> //.
  + move=> y ey /=.
    rewrite Mvar.setP.
    case: eqP => _; last by apply hvars1.
    by move=> [<-].
  move=> y ey vy1 /=.
  rewrite Mvar.setP.
  case: eqP => [<-|_]; last by apply hsem1.
  move=> [<-].
  by apply hsem.
Qed.

(* TODO: write_lvar_ext_eq -> rename into write_lval_ext_eq *)
Lemma wf_table_update_table s1 s2 r e v v' table1 ote table2 oe table3 vme :
  sem_pexpr true gd s1 e = ok v ->
  value_uincl v' v ->
  write_lval true gd r v' s1 = ok s2 ->
  symbolic_of_pexpr (clone fresh_var_ident) table1 e = ok ote ->
  match ote with
  | Some (table, e) => (table, Some e)
  | None => (table1, None)
  end = (table2, oe) ->
  update_table (remove_binding_lval table2 r) r oe = table3 ->
  wf_table table1 vme s1.(evm) ->
  exists vme', [/\
    wf_table table3 vme' s2.(evm),
    vme =[table1.(vars)] vme' &
    Sv.Subset table1.(vars) table3.(vars)].
Proof.
  move=> hv hincl hw hsym hote <- hwft1.
  case: ote hote hsym => [[{}table2 e']|] [<- <-] hsym; last first.
  + move=> /=.
    rewrite remove_binding_lval_vars.
    exists vme; split => //.
    by apply (wf_table_set_lval hw hwft1).
  have [vme' [hwft2 vme_eq hsem]] := wf_table_symbolic_of_pexpr clone_ty hsym hv hwft1.
  have hsubset := symbolic_of_pexpr_subset_vars hsym hwft1.(wft_vars).
  have hsubset' := symbolic_of_pexpr_subset_read hsym hwft1.(wft_vars).
  have hwft2' := wf_table_set_lval hw hwft2.
  exists vme'.
  have [] := update_tableE (remove_binding_lval table2 r) r (Some e');
    last by move=> ->; rewrite remove_binding_lval_vars.
  move=> [x [_ [? [<-] ->]]]; subst r.
  split=> //.
  apply wf_table_table_set_var => //.
  move=> v1.
  move: hw => /= /write_varP [-> _ htr'].
  rewrite /= get_var_eq //; t_xrbindP=> _ <-.
  have [v2 ok_v2 v_uincl] := hsem.
  exists v2 => //.
  apply (value_uincl_trans (vm_truncate_value_uincl htr')).
  by apply (value_uincl_trans hincl v_uincl).
Qed.

Lemma is_swap_arrayP o :
  reflect (exists n,  o = Opseudo_op (pseudo_operator.Oswap (sarr n))) (is_swap_array o).
Proof.
  case: o => /=; try by constructor => -[].
  case => /=; try by constructor => -[].
  move=> s; case: is_sarrP => h; constructor.
  + by case: h => n ->; eauto.
  move=> [n []] heq; apply h; eauto.
Qed.

Lemma subset_vars_wft_DEF vars1 vars2 vme :
  Sv.Subset vars2 vars1 ->
  wft_DEF vars1 vme ->
  wft_DEF vars2 vme.
Proof.
  move=> hsubset hdef1 x x_in; apply hdef1.
  by apply: hsubset x_in.
Qed.

Lemma typecheckP e ty :
  typecheck e = ok ty ->
  forall vme,
    wft_DEF (read_e e) vme ->
    exists2 v, sem_sexpr vme e = ok v & type_of_val v = ty.
Proof.
  elim: e ty => [z|x|ws e ih|sg ws e ih|opk e ih|opk e1 ih1 e2 ih2|opk e1 ih1 e2 ih2|opk e1 ih1 e2 ih2] ty /=.
  + move=> [<-] vme _. eexists; first by reflexivity. done.
  + move=> [<-] vme hdef.
    apply hdef.
    rewrite read_e_var.
    by clear; SvD.fsetdec.
  + t_xrbindP=> -[] // hty [<-] vme /(ih _ hty) [v ok_v ty_v].
    rewrite ok_v /=.
    have [z ->] := is_definedI (sem_sexpr_defined ok_v) ty_v.
    rewrite /sem_sop1 /=. eexists; first by reflexivity.
    done.
  + t_xrbindP=> -[] // ws' hty.
    case: ifP => // hcmp.
    move=> [<-] vme /(ih _ hty) [v ok_v ty_v].
    rewrite ok_v /=.
    have [w ->] := is_definedI (sem_sexpr_defined ok_v) ty_v.
    rewrite /sem_sop1 /= truncate_word_le //=.
    eexists; first by reflexivity.
    simpl. done.
  + t_xrbindP=> ty' hty.
    case: ifP => // hsub [<-].
    move=> vme /(ih _ hty) [v ok_v ty_v].
    rewrite ok_v /=.
    case: opk hsub ty_v => [|ws].
    + move=> /subtypeEl /= -> ty_v.
      have [z ->] := is_definedI (sem_sexpr_defined ok_v) ty_v.
      rewrite /sem_sop1 /=. eexists; first by reflexivity.
      done.
    move=> /subtypeEl /= [ws' [-> hcmp]] ty_v.
    have [w ->] := is_definedI (sem_sexpr_defined ok_v) ty_v.
    rewrite /sem_sop1 /= truncate_word_le //=. eexists; first by reflexivity.
    done.
  + t_xrbindP=> ty1 hty1 ty2 hty2.
    case: ifP => // /andP [hsub1 hsub2].
    move=> [<-] vme hdef.
    have hdef1: wft_DEF (read_e e1) vme.
    + apply: subset_vars_wft_DEF hdef.
      rewrite /read_e /= -/read_e read_eE.
      by clear; SvD.fsetdec.
    have hdef2: wft_DEF (read_e e2) vme.
    + apply: subset_vars_wft_DEF hdef.
      rewrite /read_e /= -/read_e read_eE.
      by clear; SvD.fsetdec.
    have [v1 ok_v1 ty_v1] := ih1 _ hty1 _ hdef1.
    have [v2 ok_v2 ty_v2] := ih2 _ hty2 _ hdef2.
    rewrite ok_v1 ok_v2 /=.
    case: opk hsub1 hsub2 ty_v1 ty_v2 {hdef} => [|ws].
    + move=> /subtypeEl -> /subtypeEl -> /= ty_v1 ty_v2.
      have [z1 ->] := is_definedI (sem_sexpr_defined ok_v1) ty_v1.
      have [z2 ->] := is_definedI (sem_sexpr_defined ok_v2) ty_v2.
      rewrite /sem_sop2 /=.
      eexists; first by reflexivity. done.
    move=> /subtypeEl [ws1 [-> hcmp1]] /subtypeEl [ws2 [-> hcmp2]] ty_v1 ty_v2.
    have [z1 ->] := is_definedI (sem_sexpr_defined ok_v1) ty_v1.
    have [z2 ->] := is_definedI (sem_sexpr_defined ok_v2) ty_v2.
    rewrite /sem_sop2 /= !truncate_word_le //=.
    eexists; first by reflexivity.
    done.
  + t_xrbindP=> ty1 hty1 ty2 hty2.
    case: ifP => // /andP [hsub1 hsub2].
    move=> [<-] vme hdef.
    have hdef1: wft_DEF (read_e e1) vme.
    + apply: subset_vars_wft_DEF hdef.
      rewrite /read_e /= -/read_e read_eE.
      by clear; SvD.fsetdec.
    have hdef2: wft_DEF (read_e e2) vme.
    + apply: subset_vars_wft_DEF hdef.
      rewrite /read_e /= -/read_e read_eE.
      by clear; SvD.fsetdec.
    have [v1 ok_v1 ty_v1] := ih1 _ hty1 _ hdef1.
    have [v2 ok_v2 ty_v2] := ih2 _ hty2 _ hdef2.
    rewrite ok_v1 ok_v2 /=.
    case: opk hsub1 hsub2 ty_v1 ty_v2 {hdef} => [|ws].
    + move=> /subtypeEl -> /subtypeEl -> /= ty_v1 ty_v2.
      have [z1 ->] := is_definedI (sem_sexpr_defined ok_v1) ty_v1.
      have [z2 ->] := is_definedI (sem_sexpr_defined ok_v2) ty_v2.
      rewrite /sem_sop2 /=.
      eexists; first by reflexivity. done.
    move=> /subtypeEl [ws1 [-> hcmp1]] /subtypeEl [ws2 [-> hcmp2]] ty_v1 ty_v2.
    have [z1 ->] := is_definedI (sem_sexpr_defined ok_v1) ty_v1.
    have [z2 ->] := is_definedI (sem_sexpr_defined ok_v2) ty_v2.
    rewrite /sem_sop2 /= !truncate_word_le //=.
    eexists; first by reflexivity.
    done.
  t_xrbindP=> ty1 hty1 ty2 hty2.
  case: ifP => // /andP [hsub1 hsub2].
  move=> [<-] vme hdef.
  have hdef1: wft_DEF (read_e e1) vme.
  + apply: subset_vars_wft_DEF hdef.
    rewrite /read_e /= -/read_e read_eE.
    by clear; SvD.fsetdec.
  have hdef2: wft_DEF (read_e e2) vme.
  + apply: subset_vars_wft_DEF hdef.
    rewrite /read_e /= -/read_e read_eE.
    by clear; SvD.fsetdec.
  have [v1 ok_v1 ty_v1] := ih1 _ hty1 _ hdef1.
  have [v2 ok_v2 ty_v2] := ih2 _ hty2 _ hdef2.
  rewrite ok_v1 ok_v2 /=.
  case: opk hsub1 hsub2 ty_v1 ty_v2 {hdef} => [|ws].
  + move=> /subtypeEl -> /subtypeEl -> /= ty_v1 ty_v2.
    have [z1 ->] := is_definedI (sem_sexpr_defined ok_v1) ty_v1.
    have [z2 ->] := is_definedI (sem_sexpr_defined ok_v2) ty_v2.
    rewrite /sem_sop2 /=.
    eexists; first by reflexivity. done.
  move=> /subtypeEl [ws1 [-> hcmp1]] /subtypeEl [ws2 [-> hcmp2]] ty_v1 ty_v2.
  have [z1 ->] := is_definedI (sem_sexpr_defined ok_v1) ty_v1.
  have [z2 ->] := is_definedI (sem_sexpr_defined ok_v2) ty_v2.
  rewrite /sem_sop2 /= !truncate_word_le //=.
  eexists; first by reflexivity.
  done.
Qed.

Lemma typecheck_sliceP s :
  typecheck_slice s ->
  forall vme,
    wft_DEF (read_slice s) vme ->
    exists cs, sem_slice vme s = ok cs.
Proof.
  rewrite /typecheck_slice.
  case ofs_ty: typecheck => [[]|] //.
  case len_ty: typecheck => [[]|] // _.
  move=> vme hdef.
  have ofs_def: wft_DEF (read_e s.(ss_ofs)) vme.
  + apply: subset_vars_wft_DEF hdef.
    rewrite /read_slice. clear; SvD.fsetdec.
  have len_def: wft_DEF (read_e s.(ss_len)) vme.
  + apply: subset_vars_wft_DEF hdef.
    rewrite /read_slice. clear; SvD.fsetdec.
  have [vofs ok_vofs vofs_ty] := typecheckP ofs_ty ofs_def.
  have [ofsi ?] := is_definedI (sem_sexpr_defined ok_vofs) vofs_ty; subst vofs.
  have [vlen ok_vlen vlen_ty] := typecheckP len_ty len_def.
  have [leni ?] := is_definedI (sem_sexpr_defined ok_vlen) vlen_ty; subst vlen.
  rewrite /sem_slice ok_vofs ok_vlen /=.
  by eexists; reflexivity.
Qed.

Lemma typecheck_intervalP vme i :
  all typecheck_slice i ->
  wft_DEF (read_interval i) vme ->
  wf_interval vme i.
Proof.
  rewrite /wf_interval.
  elim: i => [|s i ih] /=.
  + move=> _ _.
    by exists [::].
  move=> /andP [hty1 hty2] hdef.
  have hdef1: wft_DEF (read_slice s) vme.
  + apply: subset_vars_wft_DEF hdef.
    by clear; SvD.fsetdec.
  have hdef2: wft_DEF (read_interval i) vme.
  + apply: subset_vars_wft_DEF hdef.
    by clear; SvD.fsetdec.
  have [cs ok_cs] := typecheck_sliceP hty1 hdef1.
  have [ci ok_ci] := ih hty2 hdef2.
  rewrite ok_cs ok_ci /=.
  by eexists; reflexivity.
Qed.

Lemma wf_status_merge_status vars vme x status1 status2 :
  wft_DEF vars vme ->
  wf_status vme (odflt Unknown (merge_status vars x status1 status2)).
Proof.
  move=> hdef.
  case: status1 => [status1|//].
  case: status2 => [status2|//] /=.
  case: status1 status2 => [||i1] [||i2] //=.
  + case: ifP => //= hall.
    apply typecheck_intervalP.
    + apply: sub_all hall.
      by move=> ? /andP[].
    apply: subset_vars_wft_DEF hdef.
    apply wf_vars_interval_alt.
    apply: sub_all hall.
    by move=> ? /andP[].
  + case: ifP => //= hall.
    apply typecheck_intervalP.
    + apply: sub_all hall.
      by move=> ? /andP[].
    apply: subset_vars_wft_DEF hdef.
    apply wf_vars_interval_alt.
    apply: sub_all hall.
    by move=> ? /andP[].
  case hmerge: merge_interval => [i|//].
  case: ifP => //= hall.
  apply typecheck_intervalP.
  + apply: sub_all hall.
    by move=> ? /andP[].
  apply: subset_vars_wft_DEF hdef.
  apply wf_vars_interval_alt.
  apply: sub_all hall.
  by move=> ? /andP[].
Qed.

Lemma wfr_STATUS_merge vars vme rmap1 rmap2 :
  wft_DEF vars vme ->
  wfr_STATUS (merge vars rmap1 rmap2) vme.
Proof.
  move=> hdef r x.
  rewrite /get_var_status /get_status /get_status_map /=.
  rewrite Mr.map2P //.
  case: Mr.get => [sm1|//].
  case: Mr.get => [sm2|//] /=.
  case: ifP => //= _.
  rewrite Mvar.map2P //.
  by apply wf_status_merge_status.
Qed.

Lemma incl_table_refl : Reflexive incl_table.
Proof.
  move=> table.
  apply /and3P; split.
  + apply /Mvar.inclP => x.
    by case: Mvar.get.
  + apply /Uint63.lebP.
    by lia.
  by apply /Sv.subset_spec.
Qed.

Lemma incl_table_trans : Transitive incl_table.
Proof.
  move=> table1 table2 table3 /and3P [hincl1 hle1 hsubset1] /and3P [hincl2 hle2 hsubset2].
  apply /and3P; split.
  + apply /Mvar.inclP => x.
    have /Mvar.inclP /(_ x) := hincl2.
    have /Mvar.inclP /(_ x) := hincl1.
    case: Mvar.get => [e1|//].
    case: Mvar.get => [e2|//].
    by move=> /eqP <-.
  + apply /Uint63.lebP.
    have /Uint63.lebP := hle1.
    have /Uint63.lebP := hle2.
    by lia.
  apply /Sv.subset_spec.
  move/Sv.subset_spec : hsubset1.
  move/Sv.subset_spec : hsubset2.
  by clear; SvD.fsetdec.
Qed.

(* We have property
     [forall vme, wft_DEF table1.(vars) vme -> wfr_STATUS rmap1 vme]
   as soon as we call merge.
   But we can also return directly if the inclusion tests succeed. In this case,
   we know that the results are equal to the inputs.
   The two cases are expressed with a disjunction. *)
Lemma loop2P ii check_c2 n table rmap table' rmap' e' c1' c2' :
  (forall table rmap table1 rmap1 table2 rmap2 e' c1' c2',
    check_c2 table rmap = ok ((table1, rmap1), (table2, rmap2), (e', c1', c2')) ->
    wf_table_vars table rmap ->
    (wf_table_vars table1 rmap1 /\ Sv.Subset table.(vars) table1.(vars)) /\
    (wf_table_vars table2 rmap2 /\ Sv.Subset table.(vars) table2.(vars))) ->
  loop2 ii check_c2 n table rmap = ok (table', rmap', (e', c1', c2')) ->
  wf_table_vars table rmap ->
  exists table1 rmap1 table2 rmap2, [/\
    incl_table table1 table, wf_table_vars table1 rmap1 /\ Sv.Subset table.(vars) table1.(vars),
    Incl rmap1 rmap, rmap1 = rmap /\ table1 = table \/ (forall vme, wft_DEF table1.(vars) vme -> wfr_STATUS rmap1 vme),
    check_c2 table1 rmap1 = ok ((table', rmap'), (table2, rmap2), (e', c1', c2')),
    incl_table table1 table2 &
    incl rmap1 rmap2].
Proof.
  move=> hcheck_c2.
  elim: n table rmap => //= n hrec table rmap.
  t_xrbindP=> -[[[table1 rmap1] [table2 rmap2]] [[e1 c11] c12]] hc2.
  move=> + hvarst.
  have [h1 h2] :=
    hcheck_c2 _ _ _ _ _ _ _ _ _ hc2 hvarst.
  case: ifP.
  + move=> /andP [hincl1 hincl2] [<- <- <- <- <-].
    exists table, rmap, table2, rmap2; split=> //.
    + by apply incl_table_refl.
    + by split.
    + by apply Incl_refl.
    by left.
  have h : wf_table_vars table rmap /\ Sv.Subset (vars table) (vars table) by split.
  have [hwf hsub]:= wf_table_vars_merge h h2.
  move=> _ /hrec{} [] //.
  move=> table3 [rmap3 [table4 [rmap4 []]]] hinclt3 [hvarst3 hsubset3] hinclr3 hdef3 {}hc2 hinclt4 hinclr4.
  exists table3, rmap3, table4, rmap4; split=> //.
  + by apply (incl_table_trans hinclt3); apply incl_table_merge_table_l.
  + split => //.
    move: hsub hsubset3 => /=.
    by clear; SvD.fsetdec.
  + by apply (Incl_trans hinclr3); apply incl_Incl; apply incl_merge_l.
  right.
  case: hdef3 => // -[-> ->] vme.
  by apply wfr_STATUS_merge.
Qed.

Lemma sao_frame_size_ge0 sao :
  (0 <= sao.(sao_size))%Z ->
  (0 <= sao.(sao_extra_size))%Z ->
  (0 <= sao_frame_size sao)%Z.
Proof.
  move=> hsz hextra.
  rewrite /sao_frame_size.
  case: is_RAnone; first by lia.
  have := round_ws_range (sao_align sao) (sao_size sao + sao_extra_size sao).
  by lia.
Qed.

Lemma alloc_fd_max_size_ge0 pex fn fd fd' :
  alloc_fd pex mglob local_alloc fn fd = ok fd' ->
  0 <= (local_alloc fn).(sao_max_size).
Proof.
  rewrite /alloc_fd /alloc_fd_aux /=.
  t_xrbindP=> ?? hlayout [[??]?] hlocal_map.
  t_xrbindP=> -[[[??]?]?] hparams.
  t_xrbindP=> /ZleP hextra /ZleP hmax _ _ _ _.
  have hsize := init_stack_layout_size_ge0 hlayout.
  apply: Z.le_trans hmax.
  by apply sao_frame_size_ge0.
Qed.

Lemma wf_rmap_scs pmap Slots Addr Writable Align vars rmap vme s1 s2 scs:
  wf_rmap pmap Slots Addr Writable Align P vars rmap vme s1 s2 ->
  wf_rmap pmap Slots Addr Writable Align P vars rmap vme (with_scs s1 scs) (with_scs s2 scs).
Proof. by case. Qed.

Lemma sub_region_cleared_sub_region_at_ofs Slots Writable Align vme rmap sr ty ofs ofsi ty2 :
  wf_sub_region Slots Writable Align vme sr ty ->
  sem_sexpr vme ofs >>= to_int = ok ofsi ->
  0 <= ofsi /\ ofsi + size_of ty2 <= size_of ty ->
  sub_region_cleared rmap vme sr ->
  sub_region_cleared rmap vme (sub_region_at_ofs sr ofs (Sconst (size_of ty2))).
Proof.
  move=> hwf ok_ofsi hofsi hcleared.
  have [cs ok_cs wf_cs] := hwf.(wfsr_zone).
  have [cs' [ok_cs' _ hsub]] := sub_zone_at_ofsP ok_cs wf_cs ok_ofsi hofsi.
  move=> x off /hcleared [srx [hsrx hdisj]].
  exists srx; split=> //=.
  rewrite ok_cs'.
  move=> _ csx [<-] ok_csx hoff.
  move=> /(zbetween_concrete_sliceP (sub_concrete_slice_incl hsub)).
  by apply hdisj.
Qed.

(* Actually, I think we could have proved something only for arrays, since we
   use this result when the target value is a pointer, in which case the source
   value is an array. But it is not clear whether we know that the source value
   is an array at the point where we need this lemma. And now that we have this
   more general version...
*)
Lemma value_uincl_get_val_byte v1 v2 :
  value_uincl v1 v2 ->
  forall off w,
    get_val_byte v1 off = ok w ->
    get_val_byte v2 off = ok w.
Proof.
  clear.
  move=> /value_uinclE; case: v1 => //= >.
  + by move=> [? -> H] > /=; case: H => _; apply.
  move=> [? [? [-> H]]] >.
  case: ifP => //=; rewrite !zify; move: H => /andP[hle /eqP ->] hoff.
  have hle' := Z.divide_pos_le _ _ (wsize_size_pos _) (wsize_size_le hle).
  move=> <-; rewrite ifT; last by rewrite !zify; lia.
  by f_equal; symmetry; apply zero_extend_wread8.
Qed.

(* We don't need the hypothesis that [varg1] and [varg1'] are arrays, since
   we have the powerful [value_uincl_get_val_byte]. If we had a weaker version,
   we should probably add this hypothesis.
*)
(* This lemma applies both to params and results. *)
Lemma mapM2_truncate_val_value_eq_or_in_mem {A} tys vargs1 vargs1' m2 (l:seq (option A)) vargs2 :
  mapM2 ErrType dc_truncate_val tys vargs1 = ok vargs1' ->
  Forall3 (value_eq_or_in_mem m2) l vargs1 vargs2 ->
  exists vargs2',
    mapM2 ErrType dc_truncate_val
      (map2 (fun o ty =>
        match o with
        | Some _ => spointer
        | None => ty
        end) l tys) vargs2 = ok vargs2' /\
    Forall3 (value_eq_or_in_mem m2) l vargs1' vargs2'.
Proof.
  move=> htr heqinmems.
  elim: {l vargs1 vargs2} heqinmems tys vargs1' htr.
  + move=> [|//] _ /= [<-].
    eexists; split; first by reflexivity.
    by constructor.
  move=> oa varg1 varg2 vargs1 vargs2 l heqinmem _ ih [//|ty tys] /=.
  t_xrbindP=> _ varg1' hvarg1' vargs1' /ih{ih}[vargs2' [htr' heqinmems']] <-.
  rewrite htr' /=.
  case: oa heqinmem => [a|] /=.
  + move=> [p [-> hread]].
    have -> /=: dc_truncate_val (sword Uptr) (Vword p) = ok (Vword p).
    + rewrite /dc_truncate_val.
      case: ifP => //.
      by rewrite /truncate_val /= truncate_word_u.
    eexists; split; first by reflexivity.
    constructor=> //.
    exists p; split=> //.
    move=> off w hget; apply hread.
    apply: value_uincl_get_val_byte hget.
    by apply (dc_truncate_value_uincl hvarg1').
  move=> ->.
  rewrite hvarg1' /=.
  eexists; split; first by reflexivity.
  by constructor.
Qed.

Lemma mapM2_truncate_val_wf_args tyin vargs1 vargs1' vargs2 vargs2' m1 m2 fn :
  mapM2 ErrType dc_truncate_val tyin vargs1 = ok vargs1' ->
  mapM2 ErrType dc_truncate_val
    (map2 (fun o ty =>
      match o with
      | Some _ => spointer
      | None => ty
      end) (sao_params (local_alloc fn)) tyin) vargs2 = ok vargs2' ->
  wf_args m1 m2 fn vargs1 vargs2 ->
  wf_args m1 m2 fn vargs1' vargs2'.
Proof.
  move=> htr1 htr2 hargs.
  move=> i; move: (hargs i); rewrite /wf_arg.
  case ok_w: nth => [writable|//].
  have := nth_not_default ok_w ltac:(discriminate); rewrite size_map => hi.
  have [hsize1 hsize1'] := size_mapM2 htr1.
  have := size_mapM2 htr2; rewrite map2E size_map size_zip => -[hsize2 hsize2'].
  move=> [p [hp hargp]].
  have hi2 := nth_not_default hp ltac:(discriminate).
  exists p; split.
  + have := mapM2_nth htr2 sbool (Vbool true) (Vbool true).
    rewrite map2E size_map size_zip hsize2 => /(_ _ hi2).
    rewrite (nth_map (None, sbool)); last by rewrite size_zip hsize2.
    rewrite nth_zip_cond size_zip hsize2 hi2 /=.
    move: ok_w; rewrite (nth_map None) //; apply: obindP=> _ -> _.
    rewrite hp.
    rewrite /dc_truncate_val.
    case: ifP.
    + by move=> _ [<-].
    by rewrite /truncate_val /= truncate_word_u => _ [<-].
  case: hargp => halign hover hvalid hfresh hwnglob hdisj.
  have hle:
    size_val (nth (Vbool true) vargs1' i) <= size_val (nth (Vbool true) vargs1 i).
  + have hi1': (i < size vargs1')%nat.
    + rewrite -hsize1'; apply (leq_trans hi2).
      by rewrite -hsize2; apply geq_minr.
    have hincl :=
      Forall2_nth (mapM2_dc_truncate_value_uincl htr1)
        (Vbool true) (Vbool true) hi1'.
    by apply (size_of_le (value_uincl_subtype hincl)).
  split=> //.
  + by apply (no_overflow_incl (zbetween_le _ hle)).
  + move=> w hb; apply hvalid.
    apply: zbetween_trans hb.
    by apply zbetween_le.
  + move=> w /hfresh.
    apply disjoint_zrange_incl_l.
    by apply zbetween_le.
  + move=> hw hgsize.
    apply: disjoint_zrange_incl_r (hwnglob hw hgsize).
    by apply zbetween_le.
  move=> hw j vaj pj neq_ij ok_writablej ok_vaj ok_pj.
  have hj2' := nth_not_default ok_pj ltac:(discriminate).
  apply (disjoint_zrange_incl_l (zbetween_le _ hle)).
  have hle':
    size_val (nth (Vbool true) vargs1' j) <= size_val (nth (Vbool true) vargs1 j).
  + have hj1': (j < size vargs1')%nat.
    + rewrite -hsize1'; apply (leq_trans hj2').
      by rewrite -hsize2'; apply geq_minr.
    have hincl :=
      Forall2_nth (mapM2_dc_truncate_value_uincl htr1)
        (Vbool true) (Vbool true) hj1'.
    by apply (size_of_le (value_uincl_subtype hincl)).
  rewrite -ok_vaj.
  apply (disjoint_zrange_incl_r (zbetween_le _ hle')).
  apply (hdisj hw j) => //.
  move /isSomeP: ok_writablej => [writablej ok_writablej].
  have := nth_not_default ok_writablej ltac:(discriminate); rewrite size_map => hj.
  move: (hargs j); rewrite /wf_arg ok_writablej => -[pj' [ok_pj' _]].
  have := mapM2_nth htr2 sbool (Vbool true) (Vbool true).
  rewrite map2E size_map size_zip hsize2' => /(_ _ hj2').
  rewrite (nth_map (None, sbool)); last by rewrite size_zip hsize2'.
  rewrite nth_zip_cond size_zip hsize2' hj2' /=.
  move: ok_writablej; rewrite (nth_map None) //; apply: obindP=> _ -> _.
  rewrite ok_pj ok_pj'.
  rewrite /dc_truncate_val.
  case: ifP.
  + by move=> _ [<-].
  by rewrite /truncate_val /= truncate_word_u => _ [<-].
Qed.

(* If the parameter is a reg ptr, [varg2] is a pointer, and is equal to [varg2']. *)
Lemma mapM2_truncate_val_ptr_eq m fn vargs1 vargs2 :
  value_eq_or_in_mem_args m fn vargs1 vargs2 ->
  forall tyin vargs2',
  mapM2 ErrType dc_truncate_val
    (map2 (fun o ty =>
          match o with
          | Some _ => spointer
          | None => ty
          end) (sao_params (local_alloc fn)) tyin) vargs2 = ok vargs2' ->
  Forall3 (fun opi varg varg' => opi <> None -> varg = varg') (local_alloc fn).(sao_params) vargs2 vargs2'.
Proof.
  elim {vargs1 vargs2}.
  + by move=> _ _ [<-]; constructor.
  move=> opi varg1 varg2 sao_params vargs1 vargs2 heqinmem _ ih [//|ty tyin] /=.
  t_xrbindP=> _ varg2' hvarg2' vargs2' /ih{}ih <-.
  constructor=> //.
  case: opi heqinmem hvarg2' => [pi|//] [p [-> _]].
  rewrite /dc_truncate_val; case:ifP => [_ [] //| _].
  rewrite /truncate_val /= truncate_word_u.
  by move=> [<-].
Qed.

Lemma mapM2_truncate_val_wf_results tyout vres1 vres1' vres2 vres2' m fn vargs1 vargs2 :
  mapM2 ErrType dc_truncate_val tyout vres1 = ok vres1' ->
  mapM2 ErrType dc_truncate_val
    (map2 (fun o ty =>
      match o with
      | Some _ => spointer
      | None => ty
      end) (sao_return (local_alloc fn)) tyout) vres2 = ok vres2' ->
  value_eq_or_in_mem_res m fn vres1 vres2 ->
  wf_results vargs1 vargs2 fn vres1 vres2 ->
  wf_results vargs1 vargs2 fn vres1' vres2'.
Proof.
  move=> htr1 htr2 heqinmems hresults.
  elim: {vres1 vres2} hresults heqinmems tyout vres1' vres2' htr1 htr2.
  + by move=> _ [|//] _ _ /= [<-] [<-]; constructor.
  move=> oi vr1 vr2 sao_returns vres1 vres2 hresult _ ih /List_Forall3_inv /=
    [heqinmem /ih{}ih] [//|ty tyout] /=.
  t_xrbindP=> ?? vr1' hvr1' vres1' /ih{}ih <- vr2' hvr2' vres2' /ih{}ih <-.
  constructor=> //.
  case: oi heqinmem hresult hvr2' => [i|//] /= [p [-> _]] hresultp.
  have ->: dc_truncate_val (sword Uptr) (Vword p) = ok (Vword p).
  + rewrite /dc_truncate_val; case: ifP => // _.
    by rewrite /truncate_val /= truncate_word_u.
  move=> [<-].
  case: hresultp => hsub hargs.
  split=> //.
  apply: subtype_trans hsub.
  by apply (value_uincl_subtype (dc_truncate_value_uincl hvr1')).
Qed.

Hypothesis rip_rsp_neq : P'.(p_extra).(sp_rip) <> P'.(p_extra).(sp_rsp).

(* could probably be written
   Forall2 (fun x v2 => is_sarr x.(vtype) -> size_slot x <= size_val v) l params
   But maybe more complex to use?
*)
Lemma write_vars_subtype A (l:seq (option A)) params :
  List.Forall2 (fun o (x:var_i) => o <> None -> is_sarr x.(vtype)) l params ->
  forall wdb vargs1 s1 s2,
  write_vars wdb params vargs1 s1 = ok s2 ->
  Forall3 (fun o (x:var_i) v => o <> None -> subtype x.(vtype) (type_of_val v)) l params vargs1.
Proof.
  elim {l params}.
  + by move=> ? [|//] _ _ _; constructor.
  move=> o x l params harr _ ih wdb [//|varg1 vargs1] /=.
  t_xrbindP=> s1 s3 s2 hw /ih{}ih.
  constructor=> //.
  move=> /harr /is_sarrP [n hty].
  move/write_varP: hw => [_ _];rewrite hty => /vm_truncate_valEl [> ->] //.
Qed.

Lemma valid_incl_wf_args m1 m2 m3 fn vargs1 vargs2 :
  (forall p, validw m2 Aligned p U8 -> validw m3 Aligned p U8) ->
  wf_args m1 m2 fn vargs1 vargs2 ->
  wf_args m1 m3 fn vargs1 vargs2.
Proof.
  move=> hincl hargs.
  move=> i; move: (hargs i); rewrite /wf_arg.
  case ok_w: nth => [writable|//].
  move=> [p [hp hargp]].
  exists p; split=> //.
  case: hargp => halign hover hvalid hfresh hwnglob hdisj.
  split=> //.
  by move=> w hb; apply (hincl _ (hvalid _ hb)).
Qed.

Corollary alloc_stack_spec_wf_args m1 m2 fn vargs1 vargs2 ws sz ioff sz' m3 :
  wf_args m1 m2 fn vargs1 vargs2 ->
  alloc_stack_spec m2 ws sz ioff sz' m3 ->
  wf_args m1 m3 fn vargs1 vargs2.
Proof.
  move=> hargs hass.
  apply: valid_incl_wf_args hargs.
  by move=> p hp; rewrite hass.(ass_valid) hp.
Qed.

Lemma read_incl_value_eq_or_in_mem {A} m1 m2 (l:seq (option A)) vs1 vs2 :
  (forall p w, read m1 Aligned p U8 = ok w -> read m2 Aligned p U8 = ok w) ->
  Forall3 (value_eq_or_in_mem m1) l vs1 vs2 ->
  Forall3 (value_eq_or_in_mem m2) l vs1 vs2.
Proof.
  move=> hincl.
  apply Forall3_impl.
  move=> [writable|//] /= v1 v2.
  move=> [p [-> hread]].
  eexists; split; first by reflexivity.
  by move=> off w /hread; apply hincl.
Qed.

Corollary alloc_stack_spec_value_eq_or_in_mem m2 fn vargs1 vargs2 ws sz ioff sz' m3 :
  value_eq_or_in_mem_args m2 fn vargs1 vargs2 ->
  alloc_stack_spec m2 ws sz ioff sz' m3 ->
  value_eq_or_in_mem_args m3 fn vargs1 vargs2.
Proof.
  move=> heqinmem hass.
  apply: read_incl_value_eq_or_in_mem heqinmem.
  by move=> p w ok_w; rewrite -(hass.(ass_read_old8) (readV ok_w)).
Qed.

Lemma alloc_stack_spec_extend_mem m1 m2 ws sz ioff sz' m3 :
  extend_mem m1 m2 rip global_data ->
  alloc_stack_spec m2 ws sz ioff sz' m3 ->
  extend_mem m1 m3 rip global_data.
Proof.
  move=> hext hass.
  case:(hext) => hover halign hold hfresh hvalid hnew.
  split=> //.
  + move=> ??; rewrite hold //.
    apply hass.(ass_read_old8).
    by apply hvalid; apply /orP; left.
  + move=> ? /hvalid.
    by rewrite hass.(ass_valid) => ->.
  move=> i hi; rewrite -hnew //.
  symmetry.
  apply hass.(ass_read_old8).
  apply hvalid; apply /orP; right.
  apply: between_byte hi => //.
  by apply zbetween_refl.
Qed.

Lemma free_stack_spec_extend_mem m1 m2 m3 :
  extend_mem m1 m2 rip global_data ->
  free_stack_spec m2 m3 ->
  (forall p, validw m1 Aligned p U8 || between rip (Z.of_nat (size global_data)) p U8 -> validw m3 Aligned p U8) ->
  extend_mem m1 m3 rip global_data.
Proof.
  move=> hext hfss hincl.
  case:(hext) => hover halign hold hfresh hvalid hnew.
  split=> //.
  + move=> p ?.
    rewrite -hfss.(fss_read_old8); first by apply hold.
    apply hincl.
    by apply /orP; left.
  move=> i hi.
  rewrite -hfss.(fss_read_old8); first by apply hnew.
  apply hincl.
  apply /orP; right.
  apply: between_byte hi => //.
  by apply zbetween_refl.
Qed.

Lemma value_uincl_wf_results fn vargs1 vargs2 vargs1' vargs2' vres1 vres2 :
  size vargs1 = size (local_alloc fn).(sao_params) ->
  List.Forall2 value_uincl vargs1' vargs1 ->
  Forall3 (fun opi varg varg' => opi <> None -> varg = varg') (local_alloc fn).(sao_params) vargs2 vargs2' ->
  List.Forall (fun oi => forall i, oi = Some i -> nth None (local_alloc fn).(sao_params) i <> None) (local_alloc fn).(sao_return) ->
  wf_results vargs1' vargs2' fn vres1 vres2 ->
  wf_results vargs1 vargs2 fn vres1 vres2.
Proof.
  move=> hsize hincl hptreq hnnone.
  apply Forall3_impl_in.
  move=> [i|//] /= vr1 vr2 hini _ _ hresultp.
  have /List.Forall_forall -/(_ _ hini _ refl_equal) := hnnone.
  case hpi: nth => [pi|//] _.
  have hi := nth_not_default hpi ltac:(discriminate).
  case: hresultp => hsub hargs.
  split; last first.
  + by rewrite (Forall3_nth hptreq None (Vbool true) (Vbool true)
      hi ltac:(congruence)).
  have := Forall2_nth hincl (Vbool true) (Vbool true).
  rewrite (Forall2_size hincl) hsize => /(_ _ hi) /value_uincl_subtype.
  by apply subtype_trans.
Qed.

Lemma free_stack_spec_value_eq_or_in_mem m1 m2 m3 m3' fn vargs1 vargs2 vres1 vres2 :
  wf_args m1 m3 fn vargs1 vargs2 ->
  validw m3 =3 validw m3' ->
  free_stack_spec m2 m3' ->
  List.Forall (fun oi => forall i, oi = Some i -> nth None (local_alloc fn).(sao_params) i <> None) (local_alloc fn).(sao_return) ->
  wf_results vargs1 vargs2 fn vres1 vres2 ->
  value_eq_or_in_mem_res m2 fn vres1 vres2 ->
  value_eq_or_in_mem_res m3' fn vres1 vres2.
Proof.
  move=> hargs hvalideq hfss hforall hresults heqinmems.
  have [hsize1 hsize2] := Forall3_size heqinmems.
  apply (nth_Forall3 None (Vbool true) (Vbool true) hsize1 hsize2) => i hi.
  have := Forall3_nth hresults None (Vbool true) (Vbool true) hi.
  have := Forall3_nth heqinmems None (Vbool true) (Vbool true) hi.
  have := Forall_nth hforall None hi.
  case: nth => [j|//].
  move=> /(_ _ erefl).
  case hpi: nth => [pi|//] _.
  have hj := nth_not_default hpi ltac:(discriminate).
  move=> /= [p [-> hread]] hresultp.
  exists p; split; first by reflexivity.
  move=> off w /[dup] /get_val_byte_bound hoff.
  rewrite -hfss.(fss_read_old8); first by apply hread.
  move: (hargs j); rewrite /wf_arg (nth_map None) //.
  rewrite hpi /= -hresultp.(wrp_args).
  move=> [_ [[<-] hargp]].
  rewrite -hvalideq.
  apply hargp.(wap_valid).
  have hsub := hresultp.(wrp_subtype).
  apply: between_byte hoff.
  + by apply (no_overflow_incl (zbetween_le _ (size_of_le hsub)) hargp.(wap_no_overflow)).
  by apply: zbetween_le (size_of_le hsub).
Qed.

Lemma value_uincl_disjoint_from_writable_params fn vargs1 vargs1' vargs2 vargs2' p :
  List.Forall2 value_uincl vargs1' vargs1 ->
  Forall3 (fun opi varg varg' => opi <> None -> varg = varg') (local_alloc fn).(sao_params) vargs2 vargs2' ->
  Forall3 (disjoint_from_writable_param p)
    (map (omap pp_writable) (local_alloc fn).(sao_params)) vargs1 vargs2 ->
  Forall3 (disjoint_from_writable_param p)
    (map (omap pp_writable) (local_alloc fn).(sao_params)) vargs1' vargs2'.
Proof.
  move=> hincl hptreq hdisj.
  elim: {vargs2 vargs2'} hptreq vargs1 hdisj vargs1' hincl.
  + move=> [|??] /List_Forall3_inv //= _ _ /List_Forall2_inv_r ->.
    by constructor.
  move=> opi varg2 varg2' sao_params vargs2 vargs2' hptreq _ ih.
  move=> [|varg1 vargs1] /List_Forall3_inv //= [hdisj /ih{}ih].
  move=> _ /List_Forall2_inv_r [varg1' [vargs1' [-> [hincl /ih{}ih]]]].
  constructor=> //.
  move=> p2; apply: obindP => pi ? [hw] ?; subst opi varg2'.
  apply (disjoint_zrange_incl_l (zbetween_le _ (size_of_le (value_uincl_subtype hincl)))).
  apply hdisj.
  + by rewrite /= hw.
  by apply hptreq.
Qed.

Section SEM.

Let ePi_r s1 (i1:instr_r) s2 :=
  forall pmap rsp Slots Addr Writable Align table1 rmap1 table2 rmap2 ii1 c2,
  wf_pmap pmap rsp rip Slots Addr Writable Align ->
  wf_Slots Slots Addr Writable Align ->
  forall sao,
  alloc_i pmap local_alloc P sao (table1, rmap1) (MkI ii1 i1) = ok (table2, rmap2, c2) ->
  forall vme m0 s1', valid_state pmap glob_size rsp rip Slots Addr Writable Align P table1 rmap1 vme m0 s1 s1' ->
  extend_mem (emem s1) (emem s1') rip global_data ->
  wf_sao rsp (emem s1') sao ->
  exists s2' vme', [/\
    esem P' rip c2 s1' = ok s2',
    valid_state pmap glob_size rsp rip Slots Addr Writable Align P table2 rmap2 vme' m0 s2 s2' &
    vme =[table1.(vars)] vme'].

Let Pi_r s1 (i1:instr_r) s2 :=
  forall pmap rsp Slots Addr Writable Align table1 rmap1 table2 rmap2 ii1 c2,
  wf_pmap pmap rsp rip Slots Addr Writable Align ->
  wf_Slots Slots Addr Writable Align ->
  forall sao,
  alloc_i pmap local_alloc P sao (table1, rmap1) (MkI ii1 i1) = ok (table2, rmap2, c2) ->
  forall vme m0 s1', valid_state pmap glob_size rsp rip Slots Addr Writable Align P table1 rmap1 vme m0 s1 s1' ->
  extend_mem (emem s1) (emem s1') rip global_data ->
  wf_sao rsp (emem s1') sao ->
  exists s2' vme', [/\
    sem P' rip s1' c2 s2',
    valid_state pmap glob_size rsp rip Slots Addr Writable Align P table2 rmap2 vme' m0 s2 s2' &
    vme =[table1.(vars)] vme'].

Let Pi s1 (i1:instr) s2 :=
  forall pmap rsp Slots Addr Writable Align table1 rmap1 table2 rmap2 c2,
  wf_pmap pmap rsp rip Slots Addr Writable Align ->
  wf_Slots Slots Addr Writable Align ->
  forall sao,
  alloc_i pmap local_alloc P sao (table1, rmap1) i1 = ok (table2, rmap2, c2) ->
  forall vme m0 s1', valid_state pmap glob_size rsp rip Slots Addr Writable Align P table1 rmap1 vme m0 s1 s1' ->
  extend_mem (emem s1) (emem s1') rip global_data ->
  wf_sao rsp (emem s1') sao ->
  exists s2' vme', [/\
    sem P' rip s1' c2 s2',
    valid_state pmap glob_size rsp rip Slots Addr Writable Align P table2 rmap2 vme' m0 s2 s2' &
    vme =[table1.(vars)] vme'].

Let Pc s1 (c1:cmd) s2 :=
  forall pmap rsp Slots Addr Writable Align table1 rmap1 table2 rmap2 c2,
  wf_pmap pmap rsp rip Slots Addr Writable Align ->
  wf_Slots Slots Addr Writable Align ->
  forall sao,
  fmapM (alloc_i pmap local_alloc P sao) (table1, rmap1) c1 = ok (table2, rmap2, c2) ->
  forall vme m0 s1', valid_state pmap glob_size rsp rip Slots Addr Writable Align P table1 rmap1 vme m0 s1 s1' ->
  extend_mem (emem s1) (emem s1') rip global_data ->
  wf_sao rsp (emem s1') sao ->
  exists s2' vme', [/\
    sem P' rip s1' (flatten c2) s2',
    valid_state pmap glob_size rsp rip Slots Addr Writable Align P table2 rmap2 vme' m0 s2 s2' &
    vme =[table1.(vars)] vme'].

Let Pfor (i1: var_i) (vs: seq Z) (s1: estate) (c: cmd) (s2: estate) := True.

Let Pfun (scs1: syscall_state) (m1: mem) (fn: funname) (vargs: seq value)
         (scs2: syscall_state) (m2: mem) (vres: seq value) :=
  forall m1' vargs',
    extend_mem m1 m1' rip global_data ->
    wf_args m1 m1' fn vargs vargs' ->
    value_eq_or_in_mem_args m1' fn vargs vargs' ->
    alloc_ok P' fn m1' ->
    exists m2' vres',
      sem_call P' rip scs1 m1' fn vargs' scs2 m2' vres' /\
      extend_mem m2 m2' rip global_data /\
      wf_results vargs vargs' fn vres vres' /\
      value_eq_or_in_mem_res m2' fn vres vres' /\
      mem_unchanged_params_fn m1 m1' m2' fn vargs vargs'.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof.
  move=> s pmap rsp Slots Addr Writable Align table1 rmap1 table2 rmap2 /=
    c2 hpmap hwf sao [???] vme m0 s' hv hext hsao; subst table2 rmap2 c2.
  exists s', vme; split => //.
  exact: Eskip.
Qed.

Lemma valid_state_wf_table_vars pmap rsp Slots Addr Writable Align table1 rmap1 vme m0 s1 s1' :
  valid_state pmap glob_size rsp rip Slots Addr Writable Align P table1 rmap1 vme m0 s1 s1' ->
  wf_table_vars table1 rmap1.
Proof.
  move=> hv; split.
  + by apply hv.(vs_wf_table).(wft_vars).
  + by apply hv.(vs_wf_region).(wfr_vars_zone).
  by apply hv.(vs_wf_region).(wfr_vars_status).
Qed.

Local Lemma Hcons : sem_Ind_cons P ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c hhi Hi hhc Hc pmap rsp Slots Addr Writable Align table1 rmap1 table3 rmap3 c1 hpmap hwf sao /=.
  t_xrbindP=> -[[table2 rmap2] i'] hi [[{}table3 {}rmap3] c'] hc /= [<- <-] <- vme m0 s1' hv hext hsao.
  have [s2' [vme2 [si hv2 vme_eq2]]]:= Hi _ _ _ _ _ _ _ _ _ _ _ hpmap hwf _ hi _ _ _ hv hext hsao.
  have hsao2 := stack_stable_wf_sao (sem_stack_stable_sprog si) hsao.
  have hext2 := valid_state_extend_mem hwf hv hext hv2 (sem_I_validw_stable_uprog hhi) (sem_validw_stable_sprog si).
  have [s3' [vme3 [sc hv3 vme_eq3]]]:= Hc _ _ _ _ _ _ _ _ _ _ _ hpmap hwf _ hc _ _ _ hv2 hext2 hsao2.
  exists s3', vme3; split => //.
  + by apply: sem_app; [exact: si|exact: sc].
  apply (eq_onT vme_eq2).
  have [_ hsubset] := alloc_i_invariant hi (valid_state_wf_table_vars hv).
  by apply (eq_onI hsubset vme_eq3).
Qed.

Local Lemma HmkI : sem_Ind_mkI P ev Pi_r Pi.
Proof.
  move=> ii i s1 s2 _ Hi pmap rsp Slots Addr Writable Align table1 rmap1 table2 rmap2 c' hpmap hwf sao ha se m0 s1' hv hext hsao.
  by apply: Hi; eauto.
Qed.

Local Lemma Hassgn_aux : sem_Ind_assgn P ePi_r.
Proof.
  move=> s1 s1' r tag ty e v v' hv htr hw pmap rsp Slots Addr Writable Align table1 rmap1 table2 rmap2 ii1 c2 hpmap hwf sao /=.
  case: ifPn => [/is_sarrP [n ?]| _ ]; t_xrbindP.
  + move=> -[[{}table2 {}rmap2] i2'] halloc /=
      [<- <- <-] {c2} vme m0 s2 hvs hext hsao; subst ty.
    have [s2' [vme' [hs2' hvs' vme_eq]]] :=
      alloc_array_move_initP hwf.(wfsl_no_overflow) hwf.(wfsl_disjoint) hwf.(wfsl_align)
        hpmap P'_globs hsaparams ii1 hvs hv htr hw halloc.
    by exists s2', vme'; split => //; rewrite esem1.
  t_xrbindP=> ote hsym.
  case hote: (match ote with | Some _ => _ | _ => _ end) => [table1' oe].
  t_xrbindP=> e' he1 [{}rmap2 r'] hax /=
    hupdate <- <- {c2} vme m0 s2 hvs hext hsao.
  have [ve' [hve' htr']] := alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hvs he1 hv htr.
  have htyv':= truncate_val_has_type htr.
  have [s2' /= hw' hvs']:= alloc_lvalP hwf.(wfsl_no_overflow) hwf.(wfsl_disjoint) hwf.(wfsl_align) hpmap hax hvs htyv' hw.
  have /vs_wf_table hwft1 := hvs.
  have [vme' [hwft1'' vme_eq hsubset]] :=
    wf_table_update_table hv (truncate_value_uincl htr) hw hsym hote hupdate hwft1.
  exists s2', vme'; split=> //.
  + by rewrite LetK /sem_assgn P'_globs hve' /= htr' /=.
  by apply: (valid_state_eq_on _ _ hwft1'' hvs'); rewrite remove_binding_lval_vars.
Qed.

Lemma ePi_r_Pi_r s1 i s1' : ePi_r s1 i s1' → Pi_r s1 i s1'.
Proof.
  move=> h pmap rsp Slots Addr Writable Align table1 rmap1 table2 rmap2 ii1 c2 hpmap
         hwf sao halloc vme m0 s2 hvalid hext hwfsao.
  have [s2' [vme' [/esem_sem *]]]:= h pmap rsp Slots Addr Writable Align table1 rmap1 table2 rmap2 ii1 c2 hpmap
                                      hwf sao halloc vme m0 s2 hvalid hext hwfsao.
  by exists s2', vme'.
Qed.

Local Lemma Hassgn : sem_Ind_assgn P Pi_r.
Proof.
  move=> s1 s1' r tag ty e v v' hv htr hw; apply ePi_r_Pi_r; apply: Hassgn_aux hv htr hw.
Qed.

Local Lemma Hopn_aux : sem_Ind_opn P ePi_r.
Proof.
  move=> s1 s2 t o xs es.
  rewrite /sem_sopn; t_xrbindP=> vs va hes hop hw pmap rsp Slots Addr Writable Align table1 rmap1 table2 rmap2 ii1 c2 hpmap hwf sao /=.
  case heq : is_protect_ptr_fail => [[[r e] msf] | ].
  + have [[sz ?]?? {heq}]:= is_protect_ptr_failP heq; subst o xs es.
    t_xrbindP=> -[{}rmap2 i] hi /=
      <- <- <- {table2 c2} vme m0 s1' hvs hext hsao.
    move: hes => /=; t_xrbindP => ve hve _ vmsf hvmsf <- ?; subst va.
    move: hop; rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /= /se_protect_ptr_fail_sem.
    t_xrbindP => a1 a ha wmsf /to_wordI [sz' [w']] [? hwmsf] /eqP ???; subst wmsf a1 vs vmsf.
    move: hw => /=; t_xrbindP => s2' hwr ?; subst s2'.
    have := alloc_protect_ptrP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap P'_globs (ii:=ii1) hshparams hvs hve hvmsf _ _ hwr hi.
    move=> /(_ sz); rewrite /truncate_val /= hwmsf /= ha => -[] // s2' [] hsem hvs2.
    by exists s2', vme; split=> //; rewrite LetK.
  case: is_swap_arrayP => {heq} [[n heq] | _]; t_xrbindP.
  + subst o => -[{}rmap2 i] halloc /=
      <- <- <- {table2 c2} vme m0 s1' hvs ??.
    have [s2' [hsem hvs2]] := alloc_array_swapP hpmap P' hsaparams ii1 hvs hes hop hw halloc.
    by exists s2', vme; split=> //; rewrite esem1.
  move=> {}table2 ok_table2 es' he [{}rmap2 xs'] ha /=
    <- <- <- {c2} vme m0 s1' hvs hext hsao.
  have [s2' /= hw' hvs2] := alloc_lvalsP hwf.(wfsl_no_overflow) hwf.(wfsl_disjoint) hwf.(wfsl_align) hpmap ha hvs (sopn_toutP hop) hw.
  have hsem': esem P' rip [:: MkI ii1 (Copn xs' t o es')] s1' = ok s2'.
  + rewrite esem1 /=.
    rewrite /sem_sopn P'_globs.
    have [va' [ok_va' hop']] := exec_sopn_truncate_val hop.
    have [vs3 [ok_vs3 htr']] := alloc_esP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hvs he hes ok_va'.
    by rewrite ok_vs3 /= (truncate_val_exec_sopn htr' hop').
  have: table2 = remove_binding_lvals table1 xs \/
    exists r e op, [/\ xs = [:: r], es = [:: e], o = Oasm op & is_move_op op].
  + move=> {he ha hes hop hw hsem' hvs2}.
    case: xs ok_table2 => [|r xs]; first by move=> [<-]; left.
    case: xs => [|??]; last by move=> [<-]; left.
    case: o => [?|?|op]; [by move=> [<-]; left..|].
    case: es => [|e es]; first by move=> [<-]; left.
    case: es => [|??]; last by move=> [<-]; left.
    case: ifP => hmove; last by move=> [<-]; left.
    move=> _; right.
    by exists r, e, op; split.
  case.
  + move=> ->.
    by exists s2', vme; split.
  move=> [r [e [op [??? hmove]]]]; subst xs es o.
  move: ok_table2; rewrite hmove.
  t_xrbindP=> ote hsym.
  case hote: (match ote with | Some _ => _ | _ => _ end) => [table1' oe].
  move=> [hupdate].
  move: hes => /=; t_xrbindP=> v hv ?; subst va.
  have := is_move_opP hmove hop.
  move=> /List_Forall2_inv_r [v' [vs' [? [v_uincl /List_Forall2_inv_r ?]]]];
    subst vs' vs.
  move: hw => /=; t_xrbindP=> s2'' hw ?; subst s2''.
  have /vs_wf_table hwft1 := hvs.
  have [vme' [hwft2 vme_eq hsubset]] :=
    wf_table_update_table hv v_uincl hw hsym hote hupdate hwft1.
  exists s2', vme'; split=> //.
  by apply: (valid_state_eq_on _ _ hwft2 hvs2); rewrite remove_binding_lval_vars.
Qed.

Local Lemma Hopn : sem_Ind_opn P Pi_r.
Proof.
  move=> s1 s2 t o xs es h; apply ePi_r_Pi_r; apply: Hopn_aux h.
Qed.

Local Lemma Hsyscall_aux : sem_Ind_syscall P ePi_r.
Proof.
  move=> s1 scs m s2 o xs es ves vxs hves hvxs hs2.
  move=> pmap rsp Slots Addr Writable Align table1 rmap1 table2 rmap2 ii1 c2 hpmap hwf sao /=.
  t_xrbindP=> -[{}rmap2 {}c2] hsyscall
    [<- <- <-] {table2} vme m0 s1' hvs hext hsao.
  have [s2' [hsem' hvs2]] :=
    alloc_syscallP hwf.(wfsl_no_overflow) hwf.(wfsl_disjoint) hpmap P' hsaparams hsyscall hvs hves hvxs hs2.
  by exists s2', vme; split.
Qed.

Local Lemma Hsyscall : sem_Ind_syscall P Pi_r.
Proof.
  move=> s1 scs m s2 o xs es ves vxs hves hvxs hs2; apply ePi_r_Pi_r; apply: Hsyscall_aux hves hvxs hs2.
Qed.

Local Lemma Hif_true : sem_Ind_if_true P ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 Hse _ Hc pmap rsp Slots Addr Writable Align table1 rmap1 table2 rmap2 ii1 c hpmap hwf sao /=.
  t_xrbindP=> e' he [[table1' rmap1'] c1'] hc1.
  t_xrbindP=> -[[table1'' rmap1''] c2'] hc2
    [<- <- <-] {table2 rmap2 c} vme m0 s1' hvs hext hsao.
  have := alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hvs he Hse; rewrite -P'_globs.
  move=> /(_ _ erefl) [] b [] he' /= /truncate_valI [_ ?]; subst b.
  have [s2' [vme' [Hsem hvs' vme_eq]]] :=
    Hc _ _ _ _ _ _ _ _ _ _ _ hpmap hwf _ hc1 _ _ _ hvs hext hsao.
  exists s2', vme'; split=> //.
  + by apply sem_seq1; constructor; apply: Eif_true.
  have hvarst1 := valid_state_wf_table_vars hvs.
  have [hvars1 hvarsz1 hvarss1] := hvarst1.
  have hwft1' := hvs'.(vs_wf_table).
  have hvarst1' := valid_state_wf_table_vars hvs'.
  have [hvars1' hvarsz1' hvarss1'] := hvarst1'.
  have [[hvars1'' hvarsz1'' hvarss1''] hsubset] := alloc_is_invariant hc2 hvarst1.
  apply: valid_state_Incl_gen hvs'.
  + apply (wf_table_incl (incl_table_merge_table_l _ _)) => //.
    by apply (wft_VARS_merge_table hvars1' hvars1'').
  + by apply incl_Incl; apply incl_merge_l.
  + apply wfr_STATUS_merge.
    apply: subset_vars_wft_DEF hwft1'.(wft_def).
    by clear; SvD.fsetdec.
  + by apply wfr_VARS_ZONE_merge.
  + by apply wfr_VARS_STATUS_merge.
Qed.

Local Lemma Hif_false : sem_Ind_if_false P ev Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 Hse _ Hc pmap rsp Slots Addr Writable Align table1 rmap1 table2 rmap2 ii1 c hpmap hwf sao /=.
  t_xrbindP=> e' he [[table1' rmap1'] c1'] hc1.
  t_xrbindP=> -[[table1'' rmap1''] c2'] hc2
    [<- <- <-] {table2 rmap2 c} vme m0 s1' hvs hext hsao.
  have := alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hvs he Hse; rewrite -P'_globs.
  move=> /(_ _ erefl) [] b [] he' /= /truncate_valI [_ ?]; subst b.
  have [s2' [vme' [Hsem hvs' vme_eq]]] :=
    Hc _ _ _ _ _ _ _ _ _ _ _ hpmap hwf _ hc2 _ _ _ hvs hext hsao.
  exists s2', vme'; split=> //.
  + by apply sem_seq1; constructor; apply: Eif_false.
  have hvarst1 := valid_state_wf_table_vars hvs.
  have [hvars1 hvarsz1 hvarss1] := hvarst1.
  have hwft1'' := hvs'.(vs_wf_table).
  have hvarst1'' := valid_state_wf_table_vars hvs'.
  have [hvars1'' hvarsz1'' hvarss1''] := hvarst1''.
  have [[hvars1' hvarsz1' hvarss1'] hsubset] := alloc_is_invariant hc1 hvarst1.
  apply: valid_state_Incl_gen hvs'.
  + apply (wf_table_incl (incl_table_merge_table_r _ _)) => //.
    by apply (wft_VARS_merge_table hvars1' hvars1'').
  + by apply incl_Incl; apply incl_merge_r.
  + apply wfr_STATUS_merge.
    apply: subset_vars_wft_DEF hwft1''.(wft_def).
    by clear; SvD.fsetdec.
  + by apply wfr_VARS_ZONE_merge.
  + by apply wfr_VARS_STATUS_merge.
Qed.

(* do we really need to check for incl_table? *)
Local Lemma Hwhile_true : sem_Ind_while_true P ev Pc Pi_r.
Proof.
  move=> s1 s2 s3 s4 a c1 e ei c2 hhi Hc1 Hv hhi2 Hc2 _ Hwhile pmap rsp Slots Addr Writable Align
    table1 rmap1 table3 rmap3 ii c hpmap hwf sao /=.
  set check_c2 := (X in loop2 _ X _ _ _).
  t_xrbindP=> -[[{}table3 {}rmap3] [[e' c1'] c2']] hloop
    [<- <- <-] {c}.
  move=> vme m0 s1' hvs hext hsao.
  have hcheck_c2:
   (forall table rmap table1 rmap1 table2 rmap2 e' c1' c2',
    check_c2 table rmap = ok ((table1, rmap1), (table2, rmap2), (e', c1', c2')) ->
    wf_table_vars table rmap ->
    (wf_table_vars table1 rmap1 /\ Sv.Subset table.(vars) table1.(vars)) /\
    (wf_table_vars table2 rmap2 /\ Sv.Subset table.(vars) table2.(vars))).
  + clear.
    move=> table rmap table1 rmap1 table2 rmap2 e' c1' c2'.
    rewrite /check_c2.
    t_xrbindP=> -[[table1' rmap1'] ?] hc1.
    t_xrbindP=> _ _ [[table2' rmap2'] ?] hc2 [<- <- <- <- _ _ _].
    move=> hvarst.
    have [hvarst1' hsubset1] := alloc_is_invariant hc1 hvarst.
    have [hvarst2 hsubset2] := alloc_is_invariant hc2 hvarst1'.
    do 2!split=> //.
    by clear -hsubset1 hsubset2; SvD.fsetdec.
  have hwft1 := hvs.(vs_wf_table).
  have hvarst1 := valid_state_wf_table_vars hvs.
  have [hvars1 hvarsz1 hvarss1] := hvarst1.
  have
    [table2 [rmap2 [table4 [rmap4
      [hinclt2 [hvarst2 hsubset2] hinclr2 hdef2 hc2 hinclt4 hinclr4]]]]] :=
    loop2P hcheck_c2 hloop hvarst1.

  move: hc2; rewrite /check_c2.
  t_xrbindP=> -[[table2' rmap2'] c1''] hc1.
  t_xrbindP=> e1 he [[table4' rmap4'] c2''] hc2 [???????].
  subst table2' rmap2' table4' rmap4' e' c1'' c2'.
  have [hvars2 hvarsz2 hvarss2] := hvarst2.
  have hwft2 := wf_table_incl hinclt2 hvars2 hwft1.
  have hwfst1 := hvs.(vs_wf_region).(wfr_status).
  have hwfst2: wfr_STATUS rmap2 vme.
  + case: hdef2.
    + by move=> [-> _].
    by apply; apply hwft2.(wft_def).
  have {}hvs := valid_state_Incl_gen hwft2 hinclr2 hwfst2 hvarsz2 hvarss2 hvs.
  have [s2' [vme2 [hs1 hvs2 vme_eq]]] := Hc1 _ _ _ _ _ _ _ _ _ _ _ hpmap hwf _ hc1 _ _ _ hvs hext hsao.
  have := alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hvs2 he Hv; rewrite -P'_globs.
  move=> /(_ _ erefl) [] b [] he' /= /truncate_valI [_ ?]; subst b.
  have hsao2 := stack_stable_wf_sao (sem_stack_stable_sprog hs1) hsao.
  have hext2 := valid_state_extend_mem hwf hvs hext hvs2 (sem_validw_stable_uprog hhi) (sem_validw_stable_sprog hs1).
  have [s3' [vme3 [hs2 hvs3 vme_eq2]]] := Hc2 _ _ _ _ _ _ _ _ _ _ _ hpmap hwf _ hc2 _ _ _ hvs2 hext2 hsao2.
  have hwft2': wf_table table2 vme3 s3.(evm).
  + by apply (wf_table_incl hinclt4 hvars2 hvs3.(vs_wf_table)).
  have hsubset3: Sv.Subset (vars table1) (vars table3).
  + have [_ +] := alloc_is_invariant hc1 hvarst2.
    clear -hsubset2; SvD.fsetdec.
  have hwfst2': wfr_STATUS rmap2 vme3.
  + case: hdef2.
    + move=> [-> _].
      move=> r x.
      apply: (wf_status_eq_on _ (hvarss1 _ _) (hwfst1 _ _)).
      apply: (eq_onT (eq_onI hsubset2 vme_eq)).
      by apply: eq_onI vme_eq2.
    by apply; apply hwft2'.(wft_def).
  have {}hvs3 := valid_state_Incl_gen hwft2' (incl_Incl hinclr4) hwfst2' hvarsz2 hvarss2 hvs3.
  set c := [:: MkI _ _].
  have /= := Hwhile _ _ _ _ _ _ table2 rmap2 table3 rmap3 ii c hpmap hwf sao.
  have hsao3 := stack_stable_wf_sao (sem_stack_stable_sprog hs2) hsao2.
  have hext3 := valid_state_extend_mem hwf hvs2 hext2 hvs3 (sem_validw_stable_uprog hhi2) (sem_validw_stable_sprog hs2).
  rewrite Loop.nbP /= hc1 /= he /= hc2 /= hinclt4 hinclr4 /=.
  move=> /(_ erefl _ _ _ hvs3 hext3 hsao3) [s4' [vme4 [/sem_seq1_iff/sem_IE hs3 hvs4 vme_eq3]]].
  exists s4', vme4; split=> //.
  + by apply sem_seq1; constructor; apply: Ewhile_true; eassumption.
  apply: (eq_onT (eq_onI hsubset2 vme_eq)).
  apply: (eq_onT (eq_onI hsubset3 vme_eq2)).
  by apply: eq_onI vme_eq3.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false P ev Pc Pi_r.
Proof.
  move=> s1 s2 a c1 e ei c2 _ Hc1 Hv pmap rsp Slots Addr Writable Align
    table1 rmap1 table3 rmap3 ii c hpmap hwf sao /=.
  set check_c2 := (X in loop2 _ X _ _ _).
  t_xrbindP=> -[[{}table3 {}rmap3] [[e' c1'] c2']] hloop
    -[<- <- <-] {c}.
  move=> vme m0 s1' hvs hext hsao.
  have hcheck_c2:
   (forall table rmap table1 rmap1 table2 rmap2 e' c1' c2',
    check_c2 table rmap = ok ((table1, rmap1), (table2, rmap2), (e', c1', c2')) ->
    wf_table_vars table rmap ->
    (wf_table_vars table1 rmap1 /\ Sv.Subset table.(vars) table1.(vars)) /\
    (wf_table_vars table2 rmap2 /\ Sv.Subset table.(vars) table2.(vars))).
  + clear.
    move=> table rmap table1 rmap1 table2 rmap2 e' c1' c2'.
    rewrite /check_c2.
    t_xrbindP=> -[[table1' rmap1'] ?] hc1.
    t_xrbindP=> _ _ [[table2' rmap2'] ?] hc2 [<- <- <- <- _ _ _].
    move=> hvarst.
    have [hvarst1' hsubset1] := alloc_is_invariant hc1 hvarst.
    have [hvarst2 hsubset2] := alloc_is_invariant hc2 hvarst1'.
    do 2!split=> //.
    by clear -hsubset1 hsubset2; SvD.fsetdec.
  have hwft1 := hvs.(vs_wf_table).
  have hvarst1 := valid_state_wf_table_vars hvs.
  have [hvars1 hvarsz1 hvarss1] := hvarst1.
  have
    [table2 [rmap2 [table4 [rmap4
      [hinclt2 [hvarst2 hsubset2] hinclr2 hdef2 hc2 hinclt4 hinclr4]]]]] :=
    loop2P hcheck_c2 hloop hvarst1.
  have [hvars2 hvarsz2 hvarss2] := hvarst2.
  move: hc2; rewrite /check_c2.
  t_xrbindP=> -[[table2' rmap2'] c1''] hc1.
  t_xrbindP=> e1 he [[table4' rmap4'] c2''] hc2 [???????].
  subst table2' rmap2' table4' rmap4' e' c1'' c2'.
  have hwft2 := wf_table_incl hinclt2 hvars2 hwft1.
  have hwfst1 := hvs.(vs_wf_region).(wfr_status).
  have hwfst2: wfr_STATUS rmap2 vme.
  + case: hdef2.
    + by move=> [-> _].
    by apply; apply hwft2.(wft_def).
  have {}hvs := valid_state_Incl_gen hwft2 hinclr2 hwfst2 hvarsz2 hvarss2 hvs.
  have [s2' [vme2 [hs1 hvs2 vme_eq]]] := Hc1 _ _ _ _ _ _ _ _ _ _ _ hpmap hwf _ hc1 _ _ _ hvs hext hsao.
  have := alloc_eP hwf.(wfsl_no_overflow) hwf.(wfsl_align) hpmap hvs2 he Hv; rewrite -P'_globs.
  move=> /(_ _ erefl) [] b [] he' /= /truncate_valI [_ ?]; subst b.
  exists s2', vme2; split=> //.
  + by apply sem_seq1; constructor; apply: Ewhile_false; eassumption.
  by apply: eq_onI vme_eq.
Qed.

Local Lemma Hfor : sem_Ind_for P ev Pi_r Pfor.
Proof. by []. Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof. by []. Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons P ev Pc Pfor.
Proof. by []. Qed.

Local Lemma Hcall : sem_Ind_call P ev Pi_r Pfun.
Proof.
  move=> s1 scs2 m1 s1' rs fn args vargs1 vres1 hvargs1 hsem1 Hf hs1'.
  move=> pmap rsp Slots Addr Writable Align table0 rmap0 table2 rmap2 ii1 c hpmap hwfsl sao /=.
  t_xrbindP => _ -[{}rmap2 i2] halloc <- <- <- {c}.
  move=> vme m0 s2 hvs hext hsao.
  move: halloc; rewrite /alloc_call /assert_check.
  t_xrbindP=> -[rmap1 es] hcargs.
  t_xrbindP=> -[{}rmap2 rs2] hcres ra_none /ZleP hsize hle /= <- <-.

  (* evaluation of the arguments *)
  have [vargs2 [hvargs2 hargs heqinmems haddr hvarsz hclear]] :=
    alloc_call_argsP hwfsl.(wfsl_no_overflow) hwfsl.(wfsl_disjoint)
      hwfsl.(wfsl_align) hwfsl.(wfsl_not_glob) hpmap hvs hcargs hvargs1.

  (* function call *)
  have [fd1 hfd1]: exists fd, get_fundef P.(p_funcs) fn = Some fd.
  + have [fd1 [hfd1 _]] := sem_callE hsem1.
    by exists fd1.
  have [fd2 halloc hfd2] := Halloc_fd hfd1.
  have hmax := alloc_fd_max_size_ge0 halloc.
  move: halloc hfd2; rewrite /alloc_fd.
  t_xrbindP=> {}fd2 _ <- hfd2.
  have halloc_ok: alloc_ok P' fn (emem s2).
  + rewrite /alloc_ok hfd2 => _ [<-] /=.
    split.
    + rewrite /allocatable_stack /sf_total_stack /=.
      case: is_RAnone ra_none => [//|_].
      move: hsao.(wf_sao_size); rewrite /enough_size /allocatable_stack.
      by lia.
    move=> _.
    have := hsao.(wf_sao_align).
    have /vs_top_stack -> := hvs.
    by apply is_align_m.
  have [m2 [vres2 [hsem2 [hext' [hresults [heqinmems' hunch]]]]]] :=
    Hf _ _ hext hargs heqinmems halloc_ok.

  (* after function call, we have [valid_state] for [rmap1] where all writable arguments
     have been cleared.
  *)
  have hvs': valid_state pmap glob_size rsp rip Slots Addr Writable Align P table0 rmap1 vme m0 (with_mem s1 m1) (with_mem s2 m2).
  + have [hcargsx _] := alloc_call_argsE hcargs.
    set l :=
      seq.pmap (fun '(bsr, ty) =>
        match bsr with
        | Some (true, sr) => Some (sub_region_at_ofs sr (Sconst 0) (Sconst (size_of ty)), ty)
        | _               => None
        end) (zip (map fst es) (map type_of_val vargs1)).
    have hlin: forall sr ty, (sr, ty) \in l <->
      exists k sr', [/\ ty = type_of_val (nth (Vbool true) vargs1 k),
                        nth None (map fst es) k = Some (true, sr') &
                        sr = sub_region_at_ofs sr' (Sconst 0) (Sconst (size_of ty))].
    + move=> sr ty.
      rewrite /l mem_pmap -(rwP mapP) /=.
      have heqsize: size (map fst es) = size (map type_of_val vargs1).
      + rewrite 2!size_map.
        have [_ <-] := size_fmapM2 hcargsx.
        by have [? _] := Forall3_size heqinmems.
      split.
      + move=> [[[[[|//] sr']|//] ty'] hin [??]]; subst sr ty'.
        move: hin.
        move=> /nthP -/(_ (None, sbool)).
        rewrite size1_zip heqsize // => -[k hk].
        rewrite (nth_zip _ _ _ heqsize) => -[hsr' <-].
        exists k, sr'; split=> //.
        rewrite (nth_map (Vbool true)) //.
        by move: hk; rewrite size_map.
      move=> [k [sr' [-> hsr' ->]]].
      exists (Some (true, sr'), type_of_val (nth (Vbool true) vargs1 k)) => //.
      apply /(nthP (None, sbool)).
      exists k.
      + rewrite size1_zip -?heqsize //.
        apply (nth_not_default hsr' ltac:(discriminate)).
      rewrite (nth_zip _ _ _ heqsize) hsr' (nth_map (Vbool true)) //.
      move: heqsize; rewrite (size_map _ vargs1) => <-.
      apply (nth_not_default hsr' ltac:(discriminate)).

    have hwfsr0 := hvs.(vs_wf_region).(wfr_wf).
    have hwfst0 := hvs.(vs_wf_region).(wfr_status).
    have hwfst1 := alloc_call_args_aux_wfr_STATUS hwfsr0 hwfst0 hcargsx.
    have hvarsz0 := hvs.(vs_wf_region).(wfr_vars_zone).
    have hvarss0 := hvs.(vs_wf_region).(wfr_vars_status).
    have hvarss1 := wfr_VARS_STATUS_alloc_call_args_aux hcargsx hvarsz0 hvarss0.
    have hvs' := valid_state_incl (alloc_call_args_aux_incl hcargsx) hwfst1 hvarss1 hvs.
    have ok_0: sem_sexpr vme (Sconst 0) >>= to_int = ok 0.
    + by [].
    have hbound: forall i, 0 <= 0 /\ 0 + size_val (nth (Vbool true) vargs1 i) <= size_val (nth (Vbool true) vargs1 i).
    + by move=> ?; lia.
    apply (valid_state_holed_rmap hwfsl.(wfsl_no_overflow) hwfsl.(wfsl_disjoint) hpmap hvs'
             (sem_call_validw_stable_uprog hsem1) (sem_call_stack_stable_sprog hsem2)
             (sem_call_validw_stable_sprog hsem2) hext'.(em_read_old8) (l:=l)).
    + apply List.Forall_forall => -[sr ty] /InP.
      rewrite hlin => -[k [sr' [-> hsr' ->]]] /=.
      split.
      + have [hwf' _] := Forall3_nth haddr None (Vbool true) (Vbool true) (nth_not_default hsr' ltac:(discriminate)) _ _ hsr'.
        by apply (sub_region_at_ofs_wf hwf' ok_0 (hbound _)).
      by apply (Forall_nth (alloc_call_args_aux_writable hcargsx) None (nth_not_default hsr' ltac:(discriminate)) _ hsr').
    + move=> p hvalid1 hvalid2 hdisj'.
      symmetry; apply hunch => //.
      apply (nth_Forall3 None (Vbool true) (Vbool true)).
      + by rewrite size_map; have [? _] := Forall3_size heqinmems.
      + by rewrite size_map; have [_ ?] := Forall3_size heqinmems.
      rewrite size_map.
      move=> i hi p2; rewrite (nth_map None) //; apply: obindP => pi hpi [hw] hp2.
      have [sr hsr] := Forall2_nth (alloc_call_args_aux_not_None hcargsx) None None hi _ hpi.
      rewrite hw in hsr.
      have [hwf' haddr'] := Forall3_nth haddr None (Vbool true) (Vbool true) (nth_not_default hsr ltac:(discriminate)) _ _ hsr.
      have [addr ok_addr] := wf_sub_region_sub_region_addr Addr hwf'.
      move: haddr' => /(_ _ ok_addr).
      rewrite hp2 => -[?]; subst p2.
      have {}hw := Forall_nth (alloc_call_args_aux_writable hcargsx) None (nth_not_default hsr ltac:(discriminate)) _ hsr.
      have /List.Forall_forall -/(_ (sub_region_at_ofs sr (Sconst 0) (Sconst (size_val (nth (Vbool true) vargs1 i))), type_of_val (nth (Vbool true) vargs1 i))) := hdisj'.
      apply.
      + apply /InP /hlin.
        by exists i, sr.
      rewrite (sub_region_addr_offset hwf' ok_0 (hbound _) ok_addr).
      by rewrite wrepr0 GRing.addr0.
    apply List.Forall_forall => -[sr ty] /InP /hlin [i [sr' [-> hsr' ->]]].
    have hcleared := Forall2_nth hclear None (Vbool true) (nth_not_default hsr' ltac:(discriminate)) _ hsr'.
    have [hwf' _] := Forall3_nth haddr None (Vbool true) (Vbool true) (nth_not_default hsr' ltac:(discriminate)) _ _ hsr'.
    by apply (sub_region_cleared_sub_region_at_ofs hwf' ok_0 (hbound _) hcleared).
  have {}hvs' :
    valid_state pmap glob_size rsp rip Slots Addr Writable Align P table0 rmap1 vme m0
      (with_scs (with_mem s1 m1) scs2) (with_scs (with_mem s2 m2) scs2).
  + by case: hvs' => *; split => //; apply wf_rmap_scs.
  (* writing of the returned values *)
  have [s2' [hs2' hvs'']] :=
    alloc_call_resP hpmap hvs' hcres haddr hvarsz hresults heqinmems' hs1'.

  exists s2', vme; split=> //.
  apply sem_seq1; constructor; econstructor; rewrite ?P'_globs; eauto.
  by case: hvs => <- *.
Qed.


(* sem_call has 7 steps that are reflected in this proof:
  - truncate_val of args,
  - init_state,
  - write_vars of args,
  - execution of the body,
  - get_var of results,
  - truncate_val of results,
  - finalize.
*)

Local Lemma Hproc : sem_Ind_proc P ev Pc Pfun.
Proof.
  move=> scs1 m1 _ _ fn fd vargs1' vargs1 _ s1 s1' vres1 vres1' hfd hvargs1' /= [<-] hs1 hsem1 Hc hvres1 hvres1' -> ->.
  move=> m2 vargs2 hext hargs heqinmem_args hok.
  have [fd2 halloc hfd2] := Halloc_fd hfd.
  move: halloc; rewrite /alloc_fd /alloc_fd_aux /=.
  t_xrbindP=> fd2' stack hlayout [[locals1 rmap1] vnew1] hlocal_map.
  t_xrbindP=> -[[[vnew2 locals2] rmap2] alloc_params] hparams.
  t_xrbindP=> /ZleP hextra /ZleP hmax.
  move=> [[table3 rmap3] c] halloc.
  t_xrbindP=> res hcresults ??; subst fd2 fd2'.

  (* truncate_val of args *)
  have [vargs2' [hvargs2' heqinmem_args']] :=
    mapM2_truncate_val_value_eq_or_in_mem hvargs1' heqinmem_args.
  have hargs' := mapM2_truncate_val_wf_args hvargs1' hvargs2' hargs.
  have heqinmem_args1 := mapM2_dc_truncate_value_uincl hvargs1'.
  have hptreq := mapM2_truncate_val_ptr_eq heqinmem_args hvargs2'.

  (* init_state *)
  have [m2' halloc_stk]: exists m2',
    alloc_stack m2 (sao_align (local_alloc fn)) (sao_size (local_alloc fn)) (sao_ioff (local_alloc fn))
                   (sao_extra_size (local_alloc fn)) = ok m2'.
  + apply Memory.alloc_stack_complete.
    have [h1 h2 _] := init_stack_layoutP hlayout.
    apply /and4P; split.
    1-3: by apply/ZleP.
    move: hok; rewrite /alloc_ok => /(_ _ hfd2) /=; rewrite /allocatable_stack /sf_total_stack /= => -[hallocatable hal].
    move: hmax; rewrite /sao_frame_size.
    case: is_RAnone hal hallocatable => [_|-> //] hallocatable hmax; last by apply /ZleP; lia.
    case: is_align; last by apply /ZleP; lia.
    apply /ZleP.
    have := round_ws_range (sao_align (local_alloc fn)) (sao_size (local_alloc fn) + sao_extra_size (local_alloc fn)).
    by lia.
  have hass := Memory.alloc_stackP halloc_stk.
  set fex := {| sf_align := _ |} in hfd2.
  set rsp := top_stack m2'.
  set vrsp' := {| vtype := spointer; vname := P'.(p_extra).(sp_rsp); |}.
  set vrip' := {| vtype := spointer; vname := P'.(p_extra).(sp_rip); |}.

  have hinit:
    init_stk_state fex (p_extra P') rip {| escs := scs1; emem := m2; evm := Vm.init |} =
    ok
      {|
        escs := scs1;
        emem := m2';
        evm := Vm.init
          .[ vrsp' <- Vword rsp]
          .[ vrip' <- Vword rip];
      |}.
  + by rewrite /init_stk_state halloc_stk /= write_var_eq_type //= write_var_eq_type.
  have hover := ass_no_overflow hass.
  have hargs'' := alloc_stack_spec_wf_args hargs' hass.
  have heqinmem_args'' := alloc_stack_spec_value_eq_or_in_mem heqinmem_args' hass.
  have hext' := alloc_stack_spec_extend_mem hext hass.

  have hdisj_glob_locals: 0 < glob_size -> 0 < (local_alloc fn).(sao_size) ->
    disjoint_zrange rip glob_size rsp (sao_size (local_alloc fn)).
  + move=> hlt1 hlt2.
    apply disjoint_zrange_sym.
    apply disjoint_zrange_U8 => //.
    move=> k hk.
    have hb: between rip glob_size (rip + wrepr _ k)%R U8.
    + apply: between_byte hk => //.
      by apply zbetween_refl.
    (* TODO: use disjoint_zrange in ass_fresh? *)
    have /hass.(ass_fresh) hfresh: validw m2 Aligned (rip + wrepr _ k)%R U8.
    + apply hext.(em_valid).
      by rewrite hb orbT.
    apply disjoint_zrange_sym.
    split=> //.
    by apply: (no_overflow_incl hb).
  have hdisj_locals_params:
    Forall3 (fun opi varg1 varg2 => forall pi, opi = Some pi ->
      forall (p:pointer), varg2 = Vword p -> 0 < (local_alloc fn).(sao_size) -> disjoint_zrange rsp (local_alloc fn).(sao_size) p (size_val varg1))
    (sao_params (local_alloc fn)) vargs1' vargs2'.
  + apply (nth_Forall3 None (Vbool true) (Vbool true)).
    + by have [? _] := Forall3_size heqinmem_args'.
    + by have [_ ?] := Forall3_size heqinmem_args'.
    move=> i hi pi hpi p hp hlt.
    move: (hargs' i); rewrite /wf_arg.
    rewrite (nth_map None) // hpi /=.
    rewrite hp => -[_ [[<-] hargp]].
    apply disjoint_zrange_U8 => //.
    + by apply size_of_gt0.
    + by apply hargp.(wap_no_overflow).
    move=> k hk.
    have hb: between p (size_val (nth (Vbool true) vargs1' i)) (p + wrepr _ k) U8.
    + apply: between_byte hk.
      + by apply hargp.(wap_no_overflow).
      by apply zbetween_refl.
    have hfresh := hass.(ass_fresh) (hargp.(wap_valid) hb).
    apply disjoint_zrange_sym.
    split=> //.
    by apply: no_overflow_incl hb hargp.(wap_no_overflow).

  have hsub := write_vars_subtype (init_params_sarr hparams) hs1. (* 'backported' from write_vars of args *)
  set vxlen := (fresh_reg _ _ _) in halloc.
  have /= hvs := init_stk_state_valid_state hlayout hover
    scs1 hargs' hsub hlocal_map hparams hext hass refl_equal rip_rsp_neq.
  have hpmap := init_params_wf_pmap hlayout rsp vargs1' vargs2' hlocal_map hparams.
  have hslots := Hwf_Slots hlayout hover hdisj_glob_locals hext.(em_align)
    hass.(ass_align_stk) hargs' hsub hparams hdisj_locals_params.

  (* write_vars of args *)
  have [s2 hs2 hvs'] := valid_state_init_params hlayout heqinmem_args'' hlocal_map hparams hvs hs1.
  have hext'': extend_mem (emem s1) (emem s2) rip global_data.
  + have /= <- := write_vars_memP hs1.
    by have /= <- := write_vars_memP hs2.

  have hsao: wf_sao rsp (emem s2) (local_alloc fn).
  + have /= <- := write_vars_memP hs2.
    split.
    + rewrite /enough_size /allocatable_stack.
      split; first by lia.
      rewrite /top_stack hass.(ass_frames) /= hass.(ass_limit).
      move: hok; rewrite /alloc_ok => /(_ _ hfd2) /= []; rewrite /allocatable_stack /sf_total_stack /=.
      have hsize := init_stack_layout_size_ge0 hlayout.
      assert (hge := wunsigned_range (stack_limit m2)).
      have hpos := wsize_size_pos (sao_align (local_alloc fn)).
      move: hmax; rewrite /sao_frame_size.
      case: is_RAnone.
      + move=> hmax hok _.
        have hbound: 0 <= sao_size (local_alloc fn) + sao_extra_size (local_alloc fn)
                  /\ sao_size (local_alloc fn) + sao_extra_size (local_alloc fn) <= wunsigned (top_stack m2).
        + by lia.
        have := @top_stack_after_alloc_bounded _ _ (local_alloc fn).(sao_align) _ hbound.
        by lia.
      move=> hmax hok1 hok2.
      rewrite (top_stack_after_aligned_alloc _ (hok2 _)) //.
      rewrite wunsigned_add; first by lia.
      split; first by lia.
      assert (hrange := wunsigned_range (top_stack m2)).
      have [? _] := round_ws_range (sao_align (local_alloc fn)) (sao_size (local_alloc fn) + sao_extra_size (local_alloc fn)).
      by lia.
   by apply hass.(ass_align_stk).

  (* execution of the body *)
  have [s2' [vme [hsem2 hvs''' ?]]] := Hc _ _ _ _ _ _ _ _ _ _ _ hpmap hslots _ halloc _ _ _ hvs' hext'' hsao.
  have hext''' := valid_state_extend_mem hslots hvs' hext'' hvs''' (sem_validw_stable_uprog hsem1) (sem_validw_stable_sprog hsem2).

  (* get_var of results *)
  have harr: List.Forall2 (fun osr (x : var_i) => osr <> None -> is_sarr (vtype x)) (map fst alloc_params) (f_params fd).
  + by apply: (Forall2_trans _ (init_params_alloc_params_not_None hparams) (init_params_sarr hparams)); auto.
  have hsub' := write_vars_subtype harr hs1.
  have haddr := init_params_alloc_params rsp hargs'' heqinmem_args'' hparams vme.
  have [vres2 [hvres2 hresults heqinmem_res]] :=
    check_resultsP hpmap hvs''' hsub' haddr hcresults hvres1.

  (* truncate_val of results *)
  have [vres2' [hvres2' heqinmem_res']] :=
    mapM2_truncate_val_value_eq_or_in_mem hvres1' heqinmem_res.
  have hresults' := mapM2_truncate_val_wf_results hvres1' hvres2' heqinmem_res hresults.
  have hnnone: List.Forall (fun oi => forall i, oi = Some i -> nth None (sao_params (local_alloc fn)) i <> None)
                           (sao_return (local_alloc fn)).
  + apply: List.Forall_impl (check_results_alloc_params_not_None hcresults).
    move=> oi hnnone i ?; subst oi.
    move: hnnone => /(_ _ refl_equal).
    case hsr: nth => [sr|//] _.
    apply (Forall2_nth (init_params_alloc_params_not_None hparams) None None (nth_not_default hsr ltac:(discriminate))).
    by rewrite hsr.
  have [/esym hsize _] := Forall3_size heqinmem_args.
  have hresults'' :=
    value_uincl_wf_results hsize heqinmem_args1 hptreq hnnone hresults'.

  (* finalize *)
  have hfss := Memory.free_stackP (emem s2').
  have hvalideq1: validw m1 =3 validw (emem s1').
  + have /= -> := write_vars_memP hs1.
    by apply (sem_validw_stable_uprog hsem1).
  have hvalideq2: validw m2 =3 validw (free_stack (emem s2')).
  + apply: (alloc_free_validw_stable hass _ _ hfss);
      have /= -> := write_vars_memP hs2.
    + by apply (sem_stack_stable_sprog hsem2).
    by apply (sem_validw_stable_sprog hsem2).
  have heqinmem_res'' :=
    free_stack_spec_value_eq_or_in_mem hargs hvalideq2 hfss hnnone hresults'' heqinmem_res'.

  exists (free_stack (emem s2')), vres2'.
  split.
  + by econstructor; eauto; case: hvs'''.
  split.
  + apply (free_stack_spec_extend_mem hext''' hfss).
    move=> p.
    rewrite -hvalideq1 -hvalideq2.
    by apply hext.(em_valid).
  split=> //; split=> //.
  rewrite /mem_unchanged_params.
  move=> p hvalid1 hvalid2 hdisjp.
  rewrite -hfss.(fss_read_old8) -?hvalideq2 //.
  have /vs_unchanged := hvs'''; apply => //.
  + by rewrite -hvalideq1.
  apply (disjoint_from_writable_params_all_slots hlayout hover hargs'' hsub hparams).
  + by apply (value_uincl_disjoint_from_writable_params heqinmem_args1 hptreq hdisjp).
  have ? := hass.(ass_fresh) hvalid1.
  split.
  + by apply hover.
  + apply is_align_no_overflow.
    by apply is_align8.
  by apply or_comm.
Qed.

Lemma check_cP scs1 m1 fn vargs scs2 m2 vres : sem_call P ev scs1 m1 fn vargs scs2 m2 vres ->
   Pfun scs1 m1 fn vargs scs2 m2 vres.
Proof.
  exact:
    (sem_call_Ind
       Hskip
       Hcons
       HmkI
       Hassgn
       Hopn
       Hsyscall
       Hif_true
       Hif_false
       Hwhile_true
       Hwhile_false
       Hfor
       Hfor_nil
       Hfor_cons
       Hcall
       Hproc).
Qed.

End SEM.

Section IT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Definition sa_pre fn1 fn2 fs1 fs2 :=
  [/\ fn1 = fn2
    , fscs fs1 = fscs fs2
    , extend_mem (fmem fs1) (fmem fs2) rip global_data
    , wf_args (fmem fs1) (fmem fs2) fn1 (fvals fs1) (fvals fs2)
    , value_eq_or_in_mem_args (fmem fs2) fn1 (fvals fs1) (fvals fs2)
    & alloc_ok P' fn1 (fmem fs2)
    ].

Definition sa_post (fn1 fn2 : funname) (fs1 fs2 fr1 fr2 : fstate) :=
  [/\ fscs fr1 = fscs fr2
    , extend_mem (fmem fr1) (fmem fr2) rip global_data
    , wf_results (fvals fs1) (fvals fs2) fn1 (fvals fr1) (fvals fr2)
    , value_eq_or_in_mem_res (fmem fr2) fn1 (fvals fr1) (fvals fr2)
    , mem_unchanged_params_fn (fmem fs1) (fmem fs2) (fmem fr2) fn1 (fvals fs1) (fvals fs2)
    , validw (fmem fs1) =3 validw (fmem fr1)
    , validw (fmem fs2) =3 validw (fmem fr2)
    & stack_stable (fmem fs2) (fmem fr2)].

Definition sa_spec := {|
  rpreF_ := sa_pre;
  rpostF_ := sa_post;
 |}.

Section CMD.
Context (pmap : pos_map) (rsp : word Uptr) (Slots : Sv.t) (Addr : slot → word Uptr) (Writable : slot → bool)
              (Align : slot → wsize).

Context (hwf_pmap : wf_pmap pmap rsp rip Slots Addr Writable Align)
        (hwf_Slots : wf_Slots Slots Addr Writable Align).

Context (m0 m0' : mem) (mi mi' : mem)(sao : stk_alloc_oracle_t).
Context (hwf_sao : wf_sao rsp m0' sao).

Definition st_sa_pre table rmap vme s s' :=
  [/\ valid_state pmap glob_size rsp rip Slots Addr Writable Align P table rmap vme m0 s s'
    , stack_stable m0' (emem s')
    , extend_mem (emem s) (emem s') rip global_data
    , validw mi =3 validw (emem s)
    & validw mi' =3 validw (emem s') ].

Definition st_sa_post table1 table2 rmap2 vme s s' :=
  exists2 vme', st_sa_pre table2 rmap2 vme' s s' & vme =[vars table1] vme'.

Let Pi i1 :=
  forall table1 rmap1 table2 rmap2 vme c2,
  alloc_i pmap local_alloc P sao (table1, rmap1) i1 = ok (table2, rmap2, c2) ->
  wf_table_vars table1 rmap1 ->
  wequiv_rec P P' tt rip sa_spec
     (st_sa_pre table1 rmap1 vme) [::i1] c2 (st_sa_post table1 table2 rmap2 vme).

Let Pi_r i := forall ii, Pi (MkI ii i).

Let Pc c1 :=
  forall table1 rmap1 table2 rmap2 vme c2,
  fmapM (alloc_i pmap local_alloc P sao) (table1, rmap1) c1 = ok (table2, rmap2, c2) ->
  wf_table_vars table1 rmap1 ->
  wequiv_rec P P' tt rip sa_spec
     (st_sa_pre table1 rmap1 vme) c1 (flatten c2) (st_sa_post table1 table2 rmap2 vme).

Lemma st_sa_pre_post vme1 table1 table2 rmap2 table3 rmap3 c1 c2:
   Sv.Subset (vars table1) (vars table2) →
   (forall vme2,
      wequiv_rec P P' tt rip sa_spec (st_sa_pre table2 rmap2 vme2) c1 c2 (st_sa_post table2 table3 rmap3 vme2)) →
   wequiv_rec P P' tt rip sa_spec (st_sa_post table1 table2 rmap2 vme1) c1 c2 (st_sa_post table1 table3 rmap3 vme1).
Proof.
  move=> hsub h s t [vme2 hvme2 heq1].
  have : wequiv_rec P P' tt rip sa_spec (st_sa_pre table2 rmap2 vme2) c1 c2 (st_sa_post table1 table3 rmap3 vme1).
  + apply wequiv_weaken with (st_sa_pre table2 rmap2 vme2) (st_sa_post table2 table3 rmap3 vme2) => //; last by apply h.
    move=> s1 s2 [vme hpre heq2]; exists vme => //.
    by apply: (eq_onT heq1); apply:eq_onI heq2.
  by apply.
Qed.

Lemma it_check_cP_concl s1 s1' s2 vme table1 rmap1 table2 rmap2 c2:
 extend_mem (emem s1) (emem s2) rip global_data →
 stack_stable m0' (emem s2) →
 validw mi =3 validw (emem s1) →
 validw mi' =3 validw (emem s2) →
 valid_state pmap glob_size rsp rip Slots Addr Writable Align P table1 rmap1 vme m0 s1 s2 →
 validw (emem s1) =3 validw (emem s1') →
 (∃ (s2' : estate) (vme' : Vm.t),
    [/\ esem P' rip c2 s2 = ok s2'
      , valid_state pmap glob_size rsp rip Slots Addr Writable Align P table2 rmap2 vme' m0 s1' s2'
      & vme =[vars table1] vme']) →
 exists2 s2' : estate, esem P' rip c2 s2 = ok s2' & st_sa_post table1 table2 rmap2 vme s1' s2'.
Proof.
  move=> hext hstable hvalw hvalw' hvalid hvalw1  [s2' [vme' [hsem' hvalid' heq]]]; exists s2' => //.
  have hvalw2 : validw (emem s2) =3 validw (emem s2').
  + by apply: esem_validw_stable_sprog hsem'.
  exists vme' => //; split => //.
  + apply: (stack_stable_trans hstable).
    by apply: esem_stack_stable_sprog hsem'.
  + by apply: (valid_state_extend_mem hwf_Slots hvalid hext hvalid').
  + by move=> ???; rewrite hvalw hvalw1.
  by move=> ???; rewrite hvalw' hvalw2.
Qed.

Lemma st_sa_pre_incl table2 table2' rmap2 rmap2' s1 s2 vme :
  wf_table_vars table2' rmap2' →
  wfr_STATUS rmap2' vme  →
  incl_table table2' table2 →
  Incl rmap2' rmap2 →
  st_sa_pre table2 rmap2 vme s1 s2 →
  st_sa_pre table2' rmap2' vme s1 s2.
Proof.
  move=> [hvars hvarsz hvarss] wfr_status hinclt hincl [hvs' hstable hext hvalw hvalw'].
  split => //.
  apply: valid_state_Incl_gen (hvs') => //.
  apply (wf_table_incl hinclt) => //.
  by apply: vs_wf_table hvs'.
Qed.

Lemma st_sa_post_incl table1 table2 table2' rmap2 rmap2' s1 s2 vme :
  wf_table_vars table2' rmap2' →
  (forall vme, wft_DEF table2'.(vars) vme → wfr_STATUS rmap2' vme) →
  Sv.Subset table2'.(vars) table2.(vars) →
  incl_table table2' table2 →
  Incl rmap2' rmap2 →
  st_sa_post table1 table2 rmap2 vme s1 s2 →
  st_sa_post table1 table2' rmap2' vme s1 s2.
Proof.
  move=> hvarst wfr_status hsub hinclt hincl [vme' hpre heq].
  exists vme' => //.
  apply: st_sa_pre_incl (hpre) => //.
  case: hpre => hvs' _ _ _ _.
  apply wfr_status.
  by apply: subset_vars_wft_DEF hvs'.(vs_wf_table).(wft_def).
Qed.

Lemma it_check_cP_aux :
  (∀ ii1 ii2 fn1 fn2, wequiv_f_rec P P' tt rip sa_spec (rpreF (eS:=sa_spec)) ii1 ii2 fn1 fn2 (rpostF (eS:=sa_spec))) ->
  forall c1, Pc c1.
Proof.
  move=> hrec.
  apply (cmd_rect (Pr:=Pi_r) (Pi:=Pi) (Pc:=Pc)) => //; subst Pi_r Pc Pi => /=.
  + move=> table1 rmap1 table2 rmap2 vme _ [<- <- <-] _.
    by apply wequiv_nil; exists vme.
  + move=> i1 c1 hi1 hc1 table1 rmap1 table3 rmap3 vme c_; t_xrbindP.
    move=> [[table2 rmap2] c2] hi [[tbl rmap]c] /= hc [?? <-] hwftable; subst tbl rmap.
    rewrite /= -cat1s.
    apply wequiv_cat with (st_sa_post table1 table2 rmap2 vme); first by apply hi1.
    have [hwftable' hsub] := alloc_i_invariant hi hwftable.
    apply st_sa_pre_post => // => vme2.
    by apply hc1.
  (* Assgn *)
  + move=> x tg ty e ii table1 rmap1 table2 rmap2 vm2 c2 h [hwf_vars hwf_varsz hwf_status].
    apply wequiv_assgn_esem => s1 s2 s1' [hvalid hstable hext hvalw hvalw'].
    rewrite /sem_assgn; t_xrbindP => v he v' htr hw.
    have := Hassgn_aux he htr hw hwf_pmap hwf_Slots h hvalid hext (stack_stable_wf_sao hstable hwf_sao).
    apply: it_check_cP_concl => //.
    by apply: write_lval_validw hw.
  (* Opn *)
  + move=> xs t o es ii table1 rmap1 table2 rmap2 vm2 c2 h [hwf_vars hwf_varsz hwf_status].
    apply wequiv_opn_esem => s1 s2 s1' [hvalid hstable hext hvalw hvalw'] hopn.
    have := Hopn_aux hopn hwf_pmap hwf_Slots h hvalid hext (stack_stable_wf_sao hstable hwf_sao).
    apply: it_check_cP_concl => //.
    apply: (esem_i_validw_stable_uprog (p:=P) (ev:= tt) (c:= (MkI ii (Copn xs t o es)))).
    by rewrite /= hopn.
  (* Syscall *)
  + move=> xs o es ii table1 rmap1 table2 rmap2 vme c2 h [hwf_vars hwf_varsz hwf_status].
    apply wequiv_syscall_esem => s1 s2 s1' [hvalid hstable hext hvalw hvalw'] /[dup] hsemu.
    rewrite /sem_syscall; t_xrbindP => vs hes [scs mem vs'].
    rewrite /fexec_syscall; t_xrbindP => /= -[[scs' mem'] vs2] /= hex [???] hup; subst scs' mem' vs2.
    have := Hsyscall_aux hes hex hup hwf_pmap hwf_Slots h hvalid hext (stack_stable_wf_sao hstable hwf_sao).
    apply: it_check_cP_concl => //.
    apply: (esem_i_validw_stable_uprog (p:=P) (ev:= tt) (c:= (MkI ii (Csyscall xs o es)))).
    by rewrite /= hsemu.
  (* If *)
  + move=> e c1 c2 ihc1 ihc2 ii table1 rmap1 table2 rmap2 vme c_; t_xrbindP.
    move=> e' he' [[table21 rmap21] c1'] hc1; t_xrbindP.
    move=> [[table22 rmap22] c2'] hc2 [???] hwftable; subst table2 rmap2 c_.
    apply wequiv_if.
    + move=> s1 s2 v [hvalid hstable hext hvalw hvalw'].
      rewrite /sem_cond; t_xrbindP => ve he /to_boolI ?; subst ve.
      have := alloc_eP hwf_Slots.(wfsl_no_overflow) hwf_Slots.(wfsl_align) hwf_pmap hvalid he' he erefl.
      by rewrite -P'_globs => -[v' [->]]; rewrite /truncate_val /=; t_xrbindP => ? -> ->; eauto.
    have hwftablesub1 := alloc_is_invariant hc1 hwftable.
    have hwftablesub2 := alloc_is_invariant hc2 hwftable.
    have [hwftablem hsub] := wf_table_vars_merge hwftablesub1 hwftablesub2.
    case.
    + apply wequiv_weaken with (st_sa_pre table1 rmap1 vme) (st_sa_post table1 table21 rmap21 vme) => //.
      + move=> s1 s2; apply st_sa_post_incl => //.
        + by move=> ?; apply wfr_STATUS_merge.
        + by clear => /=; SvD.fsetdec.
        + by apply incl_table_merge_table_l.
        by apply /incl_Incl/incl_merge_l.
      by apply: ihc1.
    apply wequiv_weaken with (st_sa_pre table1 rmap1 vme) (st_sa_post table1 table22 rmap22 vme) => //.
    + move=> s1 s2; apply st_sa_post_incl => //.
      + by move=> ?; apply wfr_STATUS_merge.
      + by clear => /=; SvD.fsetdec.
      + by apply incl_table_merge_table_r.
      by apply/incl_Incl/incl_merge_r.
    by apply: ihc2.

  (* While *)
  + move=> al c1 e ii' c2 ihc1 ihc2 ii table1 rmap1 table3 rmap3 vme c_.
    set check_c2 := (X in loop2 _ X _ _ _).
    t_xrbindP => -[[{}table3 {}rmap3] [[e' c1'] c2']] hloop -[<- <- <-] {c_} hvarst1.
    have hcheck_c2:
     (forall table rmap table1 rmap1 table2 rmap2 e' c1' c2',
      check_c2 table rmap = ok ((table1, rmap1), (table2, rmap2), (e', c1', c2')) ->
      wf_table_vars table rmap ->
      (wf_table_vars table1 rmap1 /\ Sv.Subset table.(vars) table1.(vars)) /\
      (wf_table_vars table2 rmap2 /\ Sv.Subset table.(vars) table2.(vars))).
    + clear.
      move=> table rmap table1 rmap1 table2 rmap2 e' c1' c2'.
      rewrite /check_c2.
      t_xrbindP=> -[[table1' rmap1'] ?] hc1.
      t_xrbindP=> _ _ [[table2' rmap2'] ?] hc2 [<- <- <- <- _ _ _].
      move=> hvarst.
      have [hvarst1' hsubset1] := alloc_is_invariant hc1 hvarst.
      have [hvarst2 hsubset2] := alloc_is_invariant hc2 hvarst1'.
      do 2!split=> //.
      by clear -hsubset1 hsubset2; SvD.fsetdec.
    have [table2 [rmap2 [table4 [rmap4
      [hinclt2 [hvarst2 hsubset2] hinclr2 hdef2 hc2 hinclt4 hinclr4]]]]] :=
      loop2P hcheck_c2 hloop hvarst1.
    move: hc2; rewrite /check_c2.
    t_xrbindP=> -[[table2' rmap2'] c1''] hc1.
    t_xrbindP=> e1 he' [[table4' rmap4'] c2''] hc2 [???????].
    subst table2' rmap2' table4' rmap4' e' c1'' c2'.
    apply wkequiv_eq_pred => s1_0 s2_0 /[dup] hpre [hvs _ _ _ _].
    have hwft1 := hvs.(vs_wf_table).
    have [hvars2 hvarsz2 hvarss2] := hvarst2.
    have hwft2 := wf_table_incl hinclt2 hvars2 hwft1.
    have hwfst1 := hvs.(vs_wf_region).(wfr_status).
    have hwfst2 : wfr_STATUS rmap2 vme.
    + case: hdef2.
      + by move=> [-> _].
      by apply; apply hwft2.(wft_def).
    apply wequiv_weaken with
         (st_sa_post table1 table2 rmap2 vme) (st_sa_post table1 table3 rmap3 vme) => //.
    + by move=> s1 s2 [-> ->]; exists vme => //; apply: st_sa_pre_incl hpre.
    clear hpre.
    apply wequiv_while.
    + move=> s1 s2 v [vme' [hvalid hstable hext hvalw hvalw'] _].
      rewrite /sem_cond; t_xrbindP => ve he /to_boolI ?; subst ve.
      have := alloc_eP hwf_Slots.(wfsl_no_overflow) hwf_Slots.(wfsl_align) hwf_pmap hvalid he' he erefl.
      by rewrite -P'_globs => -[v' [->]]; rewrite /truncate_val /=; t_xrbindP => ? -> ->; eauto.
    + apply st_sa_pre_post => // vme'.
      by apply: ihc1 hc1 hvarst2.
    have [hvarst3 hsubset3] := alloc_is_invariant hc1 hvarst2.
    move=> s1 s2 [vme' hpre heq].
    have := ihc2 _ _ _ _ _ _ hc2 hvarst3 _ _ hpre.
    apply xrutt_facts.xrutt_weaken => //.
    move=> s1' s2' [vme3 hpre3 heq3].
    have heq1 : vme =[vars table1] vme3.
    + by apply: (eq_onT heq); apply: eq_onI heq3; clear -hsubset2 hsubset3; SvD.fsetdec.
    exists vme3 => //.
    apply: st_sa_pre_incl (hpre3) => //; last by apply incl_Incl.
    case: hdef2.
    + move=> [-> _] r x.
      case: hvarst1 => [hvars1 hvarsz1 hvarss1].
      by apply: (wf_status_eq_on _ (hvarss1 _ _) (hwfst1 _ _)).
    case: hpre3 => hvs3 _ _ _ _.
    have hwft2' := wf_table_incl hinclt4 hvars2 hvs3.(vs_wf_table).
    apply; apply hwft2'.(wft_def).

  (* Call *)
  move=> rs fn args ii1 table0 rmap0 table2 rmap2 vme c.
  case hfd1: get_fundef => [fd1|] //=.
  t_xrbindP=> -[{}rmap2 i2] halloc <- <- <- {c}.
  move: halloc; rewrite /alloc_call /assert_check.
  t_xrbindP=> -[rmap1 es] hcargs.
  t_xrbindP=> -[{}rmap2 rs2] hcres ra_none /ZleP hsize hle /= <- <- hvarst.
  apply wkequiv_eq_pred => s1 s2 /[dup] hpre [hvs hstable hext hvalw hvalw'].
  pose Rv := fun vargs1 vargs2 =>
    [ /\ wf_args (emem s1) (emem s2) fn vargs1 vargs2,
         value_eq_or_in_mem_args (emem s2) fn vargs1 vargs2,
         Forall3
           (λ (bsr : option (bool * sub_region)) (varg1 varg2 : value),
              ∀ (b0 : bool) (sr : sub_region),
                bsr = Some (b0, sr)
                → wf_sub_region Slots Writable Align vme sr (type_of_val varg1)
                  ∧ ∀ addr : word Uptr,
                      sub_region_addr Addr vme sr = ok addr → varg2 = Vword addr)
           [seq i.1 | i <- es] vargs1 vargs2,
         List.Forall
           (λ bsr : option (bool * sub_region),
              ∀ (b0 : bool) (sr : sub_region),
                bsr = Some (b0, sr) → wf_vars_zone (vars table0) (sr_zone sr))
           [seq i.1 | i <- es] &
         List.Forall2
           (λ (bsr : option (bool * sub_region)) (_ : value),
              ∀ sr : sub_region, bsr = Some (true, sr) → sub_region_cleared rmap1 vme sr)
           [seq i.1 | i <- es] vargs1].
  have [fd2 halloc hfd2] := Halloc_fd hfd1.
  have hmax := alloc_fd_max_size_ge0 halloc.
  move: halloc hfd2; rewrite /alloc_fd.
  t_xrbindP=> {}fd2 _ <- hfd2.
  have halloc_ok: alloc_ok P' fn (emem s2).
  + rewrite /alloc_ok hfd2 => _ [<-] /=.
    have hsao := stack_stable_wf_sao hstable hwf_sao.
    split.
    + rewrite /allocatable_stack /sf_total_stack /=.
      case: is_RAnone ra_none => [//|_].
      move: hsao.(wf_sao_size); rewrite /enough_size /allocatable_stack.
      by lia.
    move=> _.
    have := hsao.(wf_sao_align).
    have /vs_top_stack -> := hvs.
    by apply is_align_m.

  apply wequiv_call_core with sa_pre sa_post Rv.
  + move => _ _ vargs1 [-> ->] hvargs1.
    have [vargs2 [*]]:= alloc_call_argsP hwf_Slots.(wfsl_no_overflow) hwf_Slots.(wfsl_disjoint)
      hwf_Slots.(wfsl_align) hwf_Slots.(wfsl_not_glob) hwf_pmap hvs hcargs hvargs1.
    by exists vargs2 => //; rewrite P'_globs.
  + move=> _ _ vargs1 vargs2 [-> ->] [hargs heqinmems haddr hvarsz hclear] {Rv}.
    split => //; first by apply hvs.(vs_scs).
  + by apply hrec.
  (* after function call, we have [valid_state] for [rmap1] where all writable arguments
     have been cleared.
  *)
  move=> fs1 fs2 [scs2 m1 vres1] [scs2' m2 vres2] [] _ _ {}hext _ heqinmems _ []
    /= hscs hext' hresults heqinmems' hunch hvalidws hvalidwt hstablet; subst scs2'.
  move=> _ _ s1' [[-> ->] _ _ hmem1 hmem2 [_ _ haddr hvarsz hclear]]; rewrite /upd_estate => /= hs1'.
  rewrite -hmem1 -hmem2 in hext, heqinmems, hunch, hvalidws,  hvalidwt, hstablet => {hmem1 hmem2 Rv}.
  set vargs1 := fvals fs1.
  have hvs': valid_state pmap glob_size rsp rip Slots Addr Writable Align P table0 rmap1 vme m0 (with_mem s1 m1) (with_mem s2 m2).
  + have [hcargsx _] := alloc_call_argsE hcargs.
    set l :=
      seq.pmap (fun '(bsr, ty) =>
        match bsr with
        | Some (true, sr) => Some (sub_region_at_ofs sr (Sconst 0) (Sconst (size_of ty)), ty)
        | _               => None
        end) (zip (map fst es) (map type_of_val vargs1)).
    have hlin: forall sr ty, (sr, ty) \in l <->
      exists k sr', [/\ ty = type_of_val (nth (Vbool true) vargs1 k),
                        nth None (map fst es) k = Some (true, sr') &
                        sr = sub_region_at_ofs sr' (Sconst 0) (Sconst (size_of ty))].
    + move=> sr ty.
      rewrite /l mem_pmap -(rwP mapP) /=.
      have heqsize: size (map fst es) = size (map type_of_val vargs1).
      + rewrite 2!size_map.
        have [_ <-] := size_fmapM2 hcargsx.
        by have [? _] := Forall3_size heqinmems.
      split.
      + move=> [[[[[|//] sr']|//] ty'] hin [??]]; subst sr ty'.
        move: hin.
        move=> /nthP -/(_ (None, sbool)).
        rewrite size1_zip heqsize // => -[k hk].
        rewrite (nth_zip _ _ _ heqsize) => -[hsr' <-].
        exists k, sr'; split=> //.
        rewrite (nth_map (Vbool true)) //.
        by move: hk; rewrite size_map.
      move=> [k [sr' [-> hsr' ->]]].
      exists (Some (true, sr'), type_of_val (nth (Vbool true) vargs1 k)) => //.
      apply /(nthP (None, sbool)).
      exists k.
      + rewrite size1_zip -?heqsize //.
        apply (nth_not_default hsr' ltac:(discriminate)).
      rewrite (nth_zip _ _ _ heqsize) hsr' (nth_map (Vbool true)) //.
      move: heqsize; rewrite (size_map _ vargs1) => <-.
      apply (nth_not_default hsr' ltac:(discriminate)).

    have hwfsr0 := hvs.(vs_wf_region).(wfr_wf).
    have hwfst0 := hvs.(vs_wf_region).(wfr_status).
    have hwfst1 := alloc_call_args_aux_wfr_STATUS hwfsr0 hwfst0 hcargsx.
    have hvarsz0 := hvs.(vs_wf_region).(wfr_vars_zone).
    have hvarss0 := hvs.(vs_wf_region).(wfr_vars_status).
    have hvarss1 := wfr_VARS_STATUS_alloc_call_args_aux hcargsx hvarsz0 hvarss0.
    have hvs' := valid_state_incl (alloc_call_args_aux_incl hcargsx) hwfst1 hvarss1 hvs.
    have ok_0: sem_sexpr vme (Sconst 0) >>= to_int = ok 0.
    + by [].
    have hbound: forall i, 0 <= 0 /\ 0 + size_val (nth (Vbool true) vargs1 i) <= size_val (nth (Vbool true) vargs1 i).
    + by move=> ?; lia.
    apply (valid_state_holed_rmap hwf_Slots.(wfsl_no_overflow) hwf_Slots.(wfsl_disjoint) hwf_pmap hvs'
              hvalidws hstablet hvalidwt hext'.(em_read_old8) (l:=l)).
    + apply List.Forall_forall => -[sr ty] /InP.
      rewrite hlin => -[k [sr' [-> hsr' ->]]] /=.
      split.
      + have [hwf' _] := Forall3_nth haddr None (Vbool true) (Vbool true) (nth_not_default hsr' ltac:(discriminate)) _ _ hsr'.
        by apply (sub_region_at_ofs_wf hwf' ok_0 (hbound _)).
      by apply (Forall_nth (alloc_call_args_aux_writable hcargsx) None (nth_not_default hsr' ltac:(discriminate)) _ hsr').
    + move=> p hvalid1 hvalid2 hdisj'.
      symmetry; apply hunch => //.
      apply (nth_Forall3 None (Vbool true) (Vbool true)).
      + by rewrite size_map; have [? _] := Forall3_size heqinmems.
      + by rewrite size_map; have [_ ?] := Forall3_size heqinmems.
      rewrite size_map.
      move=> i hi p2; rewrite (nth_map None) //; apply: obindP => pi hpi [hw] hp2.
      have [sr hsr] := Forall2_nth (alloc_call_args_aux_not_None hcargsx) None None hi _ hpi.
      rewrite hw in hsr.
      have [hwf' haddr'] := Forall3_nth haddr None (Vbool true) (Vbool true) (nth_not_default hsr ltac:(discriminate)) _ _ hsr.
      have [addr ok_addr] := wf_sub_region_sub_region_addr Addr hwf'.
      move: haddr' => /(_ _ ok_addr).
      rewrite hp2 => -[?]; subst p2.
      have {}hw := Forall_nth (alloc_call_args_aux_writable hcargsx) None (nth_not_default hsr ltac:(discriminate)) _ hsr.
      have /List.Forall_forall -/(_ (sub_region_at_ofs sr (Sconst 0) (Sconst (size_val (nth (Vbool true) vargs1 i))), type_of_val (nth (Vbool true) vargs1 i))) := hdisj'.
      apply.
      + apply /InP /hlin.
        by exists i, sr.
      rewrite (sub_region_addr_offset hwf' ok_0 (hbound _) ok_addr).
      by rewrite wrepr0 GRing.addr0.
    apply List.Forall_forall => -[sr ty] /InP /hlin [i [sr' [-> hsr' ->]]].
    have hcleared := Forall2_nth hclear None (Vbool true) (nth_not_default hsr' ltac:(discriminate)) _ hsr'.
    have [hwf' _] := Forall3_nth haddr None (Vbool true) (Vbool true) (nth_not_default hsr' ltac:(discriminate)) _ _ hsr'.
    by apply (sub_region_cleared_sub_region_at_ofs hwf' ok_0 (hbound _) hcleared).
  have {}hvs' :
    valid_state pmap glob_size rsp rip Slots Addr Writable Align P table0 rmap1 vme m0
      (with_scs (with_mem s1 m1) scs2) (with_scs (with_mem s2 m2) scs2).
  + by case: hvs' => *; split => //; apply wf_rmap_scs.
  (* writing of the returned values *)
  have [s2' [hs2' hvs'']] :=
    alloc_call_resP hwf_pmap hvs' hcres haddr hvarsz hresults heqinmems' hs1'.

  rewrite P'_globs; exists s2'=> //.
  have hvalw1 : validw m1 =3 validw (emem s1').
  + by apply: write_lvals_validw hs1'.
  have hvalw2 : validw m2 =3 validw (emem s2').
  + by apply: write_lvals_validw hs2'.
  exists vme => //; split => //.
  + case: hpre => _ hstable1 _ _ _.
    apply (stack_stable_trans hstable1).
    apply (stack_stable_trans hstablet).
    by apply (write_lvals_stack_stable hs2').
  apply: (valid_state_extend_mem hwf_Slots hvs' _ hvs'') => //=.
  + by move=> ???; rewrite hvalw hvalidws hvalw1.
  by move=> ???; rewrite hvalw' hvalidwt hvalw2.
Qed.

End CMD.

Lemma it_check_cP fn : wiequiv_f P P' tt rip (rpreF (eS:=sa_spec)) fn fn (rpostF (eS:=sa_spec)).
Proof.
  apply wequiv_fun_ind => hrec {}fn _ [scs1 m1 vargs1] [_ m2 vargs2] [<- /= <-] hext hargs heqinmem_args hok fd hfd.
  have [fd2 halloc hfd2] := Halloc_fd hfd.
  exists fd2 => //.

  move: halloc; rewrite /alloc_fd /alloc_fd_aux /=.
  t_xrbindP=> fd2' stack hlayout [[locals1 rmap1] vnew1] hlocal_map.
  t_xrbindP=> -[[[vnew2 locals2] rmap2] alloc_params] hparams.
  t_xrbindP=> /ZleP hextra /ZleP hmax.
  move=> [[table3 rmap3] c] halloc.
  t_xrbindP=> res hcresults ??; subst fd2 fd2' => /=.
  rewrite /initialize_funcall => s1; t_xrbindP => /=.
  move=> vargs1' hvargs1' _ [<-] hs1.

  (* truncate_val of args *)
  have [vargs2' [hvargs2' heqinmem_args']] :=
    mapM2_truncate_val_value_eq_or_in_mem hvargs1' heqinmem_args.
  have hargs' := mapM2_truncate_val_wf_args hvargs1' hvargs2' hargs.
  have heqinmem_args1 := mapM2_dc_truncate_value_uincl hvargs1'.
  have hptreq := mapM2_truncate_val_ptr_eq heqinmem_args hvargs2'.

  (* init_state *)
  have [m2' halloc_stk]: exists m2',
    alloc_stack m2 (sao_align (local_alloc fn)) (sao_size (local_alloc fn)) (sao_ioff (local_alloc fn))
                   (sao_extra_size (local_alloc fn)) = ok m2'.
  + apply Memory.alloc_stack_complete.
    have [h1 h2 _] := init_stack_layoutP hlayout.
    apply /and4P; split.
    1-3: by apply/ZleP.
    move: hok; rewrite /alloc_ok => /(_ _ hfd2) /=; rewrite /allocatable_stack /sf_total_stack /= => -[hallocatable hal].
    move: hmax; rewrite /sao_frame_size.
    case: is_RAnone hal hallocatable => [_|-> //] hallocatable hmax; last by apply /ZleP; lia.
    case: is_align; last by apply /ZleP; lia.
    apply /ZleP.
    have := round_ws_range (sao_align (local_alloc fn)) (sao_size (local_alloc fn) + sao_extra_size (local_alloc fn)).
    by lia.
  have hass := Memory.alloc_stackP halloc_stk.
  set fex := {| sf_align := _ |} in hfd2.
  set rsp := top_stack m2'.
  set vrsp' := {| vtype := spointer; vname := P'.(p_extra).(sp_rsp); |}.
  set vrip' := {| vtype := spointer; vname := P'.(p_extra).(sp_rip); |}.

  have hinit:
    init_stk_state fex (p_extra P') rip {| escs := scs1; emem := m2; evm := Vm.init |} =
    ok
      {|
        escs := scs1;
        emem := m2';
        evm := Vm.init
          .[ vrsp' <- Vword rsp]
          .[ vrip' <- Vword rip];
      |}.
  + by rewrite /init_stk_state halloc_stk /= write_var_eq_type //= write_var_eq_type.
  have hover := ass_no_overflow hass.
  have hargs'' := alloc_stack_spec_wf_args hargs' hass.
  have heqinmem_args'' := alloc_stack_spec_value_eq_or_in_mem heqinmem_args' hass.
  have hext' := alloc_stack_spec_extend_mem hext hass.

  have hdisj_glob_locals: 0 < glob_size -> 0 < (local_alloc fn).(sao_size) ->
    disjoint_zrange rip glob_size rsp (sao_size (local_alloc fn)).
  + move=> hlt1 hlt2.
    apply disjoint_zrange_sym.
    apply disjoint_zrange_U8 => //.
    move=> k hk.
    have hb: between rip glob_size (rip + wrepr _ k)%R U8.
    + apply: between_byte hk => //.
      by apply zbetween_refl.
    (* TODO: use disjoint_zrange in ass_fresh? *)
    have /hass.(ass_fresh) hfresh: validw m2 Aligned (rip + wrepr _ k)%R U8.
    + apply hext.(em_valid).
      by rewrite hb orbT.
    apply disjoint_zrange_sym.
    split=> //.
    by apply: (no_overflow_incl hb).
  have hdisj_locals_params:
    Forall3 (fun opi varg1 varg2 => forall pi, opi = Some pi ->
      forall (p:pointer), varg2 = Vword p -> 0 < (local_alloc fn).(sao_size) -> disjoint_zrange rsp (local_alloc fn).(sao_size) p (size_val varg1))
    (sao_params (local_alloc fn)) vargs1' vargs2'.
  + apply (nth_Forall3 None (Vbool true) (Vbool true)).
    + by have [? _] := Forall3_size heqinmem_args'.
    + by have [_ ?] := Forall3_size heqinmem_args'.
    move=> i hi pi hpi p hp hlt.
    move: (hargs' i); rewrite /wf_arg.
    rewrite (nth_map None) // hpi /=.
    rewrite hp => -[_ [[<-] hargp]].
    apply disjoint_zrange_U8 => //.
    + by apply size_of_gt0.
    + by apply hargp.(wap_no_overflow).
    move=> k hk.
    have hb: between p (size_val (nth (Vbool true) vargs1' i)) (p + wrepr _ k) U8.
    + apply: between_byte hk.
      + by apply hargp.(wap_no_overflow).
      by apply zbetween_refl.
    have hfresh := hass.(ass_fresh) (hargp.(wap_valid) hb).
    apply disjoint_zrange_sym.
    split=> //.
    by apply: no_overflow_incl hb hargp.(wap_no_overflow).

  have hsub := write_vars_subtype (init_params_sarr hparams) hs1. (* 'backported' from write_vars of args *)
  set vxlen := (fresh_reg _ _ _) in halloc.
  have /= hvs := init_stk_state_valid_state hlayout hover
    scs1 hargs' hsub hlocal_map hparams hext hass refl_equal rip_rsp_neq.
  have hpmap := init_params_wf_pmap hlayout rsp vargs1' vargs2' hlocal_map hparams.
  have hslots := Hwf_Slots hlayout hover hdisj_glob_locals hext.(em_align)
    hass.(ass_align_stk) hargs' hsub hparams hdisj_locals_params.

  (* write_vars of args *)
  have [s2 hs2 hvs'] := valid_state_init_params hlayout heqinmem_args'' hlocal_map hparams hvs hs1.
  have hext'': extend_mem (emem s1) (emem s2) rip global_data.
  + have /= <- := write_vars_memP hs1.
    by have /= <- := write_vars_memP hs2.

  have hsao: wf_sao rsp (emem s2) (local_alloc fn).
  + have /= <- := write_vars_memP hs2.
    split.
    + rewrite /enough_size /allocatable_stack.
      split; first by lia.
      rewrite /top_stack hass.(ass_frames) /= hass.(ass_limit).
      move: hok; rewrite /alloc_ok => /(_ _ hfd2) /= []; rewrite /allocatable_stack /sf_total_stack /=.
      have hsize := init_stack_layout_size_ge0 hlayout.
      assert (hge := wunsigned_range (stack_limit m2)).
      have hpos := wsize_size_pos (sao_align (local_alloc fn)).
      move: hmax; rewrite /sao_frame_size.
      case: is_RAnone.
      + move=> hmax hok _.
        have hbound: 0 <= sao_size (local_alloc fn) + sao_extra_size (local_alloc fn)
                  /\ sao_size (local_alloc fn) + sao_extra_size (local_alloc fn) <= wunsigned (top_stack m2).
        + by lia.
        have := @top_stack_after_alloc_bounded _ _ (local_alloc fn).(sao_align) _ hbound.
        by lia.
      move=> hmax hok1 hok2.
      rewrite (top_stack_after_aligned_alloc _ (hok2 _)) //.
      rewrite wunsigned_add; first by lia.
      split; first by lia.
      assert (hrange := wunsigned_range (top_stack m2)).
      have [? _] := round_ws_range (sao_align (local_alloc fn)) (sao_size (local_alloc fn) + sao_extra_size (local_alloc fn)).
      by lia.
   by apply hass.(ass_align_stk).
  exists s2; first by rewrite hvargs2' /= hinit.
  move: hvs'.
  set pmap := (X in valid_state X).
  set rsp1 := (X in valid_state _ _ X).
  set Slots1 := (X in valid_state _ _ _ _ X).
  set Addr1 := (X in valid_state _ _ _ _ _ X).
  set Writ1 := (X in valid_state _ _ _ _ _ _ X).
  set Alig1 := (X in valid_state _ _ _ _ _ _ _ X).
  exists (st_sa_pre pmap rsp1 Slots1 Addr1 Writ1 Alig1 m2 (emem s2) (emem s1) (emem s2) empty_table rmap2 Vm.init).
  exists (st_sa_post pmap rsp1 Slots1 Addr1 Writ1 Alig1 m2 (emem s2) (emem s1) (emem s2) empty_table table3 rmap3 Vm.init).
  split => //.
  (* execution of the body *)
  + apply: it_check_cP_aux => //.
    + exact hsao.
    + exact halloc.
    by apply: valid_state_wf_table_vars hvs'.
  move=> s1' s2' fr1 [vme] [hvs''' hstable hext''' hvalw hvalw'] _.
  rewrite /finalize_funcall; t_xrbindP => vres1 hvres1 vres1' hvres1' <- {fr1} /=.
  (* get_var of results *)
  have harr: List.Forall2 (fun osr (x : var_i) => osr <> None -> is_sarr (vtype x)) (map fst alloc_params) (f_params fd).
  + by apply: (Forall2_trans _ (init_params_alloc_params_not_None hparams) (init_params_sarr hparams)); auto.
  have hsub' := write_vars_subtype harr hs1.
  have haddr := init_params_alloc_params rsp hargs'' heqinmem_args'' hparams vme.
  have [vres2 [hvres2 hresults heqinmem_res]] :=
    check_resultsP hpmap hvs''' hsub' haddr hcresults hvres1.
  rewrite hvres2 /=.
  (* truncate_val of results *)
  have [vres2' [hvres2' heqinmem_res']] :=
    mapM2_truncate_val_value_eq_or_in_mem hvres1' heqinmem_res.
  have hresults' := mapM2_truncate_val_wf_results hvres1' hvres2' heqinmem_res hresults.
  have hnnone: List.Forall (fun oi => forall i, oi = Some i -> nth None (sao_params (local_alloc fn)) i <> None)
                           (sao_return (local_alloc fn)).
  + apply: List.Forall_impl (check_results_alloc_params_not_None hcresults).
    move=> oi hnnone i ?; subst oi.
    move: hnnone => /(_ _ refl_equal).
    case hsr: nth => [sr|//] _.
    apply (Forall2_nth (init_params_alloc_params_not_None hparams) None None (nth_not_default hsr ltac:(discriminate))).
    by rewrite hsr.
  have [/esym hsize _] := Forall3_size heqinmem_args.
  have hresults'' :=
    value_uincl_wf_results hsize heqinmem_args1 hptreq hnnone hresults'.
  rewrite hvres2' /=.
  (* finalize *)
  have hfss := Memory.free_stackP (emem s2').
  have hvalideq1: validw m1 =3 validw (emem s1').
  + by have /= -> := write_vars_memP hs1.
  have hvalideq2: validw m2 =3 validw (free_stack (emem s2')).
  + apply: (alloc_free_validw_stable hass _ _ hfss);
    by have /= -> := write_vars_memP hs2.
  have heqinmem_res'' :=
    free_stack_spec_value_eq_or_in_mem hargs hvalideq2 hfss hnnone hresults'' heqinmem_res'.
  eexists; first reflexivity.
  split => //=.
  + by case: hvs'''.
  + apply (free_stack_spec_extend_mem hext''' hfss).
    move=> p.
    rewrite -hvalideq1 -hvalideq2.
    by apply hext.(em_valid).
  + rewrite /mem_unchanged_params.
    move=> p hvalid1 hvalid2 hdisjp.
    rewrite -hfss.(fss_read_old8) -?hvalideq2 //.
    have /vs_unchanged := hvs'''; apply => //.
    + by rewrite -hvalideq1.
    apply (disjoint_from_writable_params_all_slots hlayout hover hargs'' hsub hparams).
    + by apply (value_uincl_disjoint_from_writable_params heqinmem_args1 hptreq hdisjp).
    have ? := hass.(ass_fresh) hvalid1.
    split.
    + by apply hover.
    + apply is_align_no_overflow.
      by apply is_align8.
    by apply or_comm.
  rewrite /finalize_stk_mem.
  apply: (alloc_free_stack_stable hass _ hfss).
  apply: stack_stable_trans hstable.
  rewrite (@write_vars_lvals _ _ _ _ _ [::]) in hs2.
  apply: write_lvals_stack_stable hs2.
Qed.

End IT.

End PROC.

End INIT.

Section HSAPARAMS.

Context
  {wsw : WithSubWord}
  {dc : DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  (shparams : slh_lowering.sh_params)
  (hshparams : slh_lowering_proof.h_sh_params shparams)
  (saparams : stack_alloc_params)
  (hsaparams : h_stack_alloc_params saparams).

Context
  (is_move_op : asm_op_t -> bool)
  (fresh_var_ident  : v_kind -> Uint63.int -> string -> stype -> Ident.ident)
  (pp_sr : sub_region -> pp_error).

Context
  (is_move_opP :
    forall op vx v,
      is_move_op op ->
      exec_sopn (Oasm op) [:: vx ] = ok v ->
      List.Forall2 value_uincl v [:: vx ]).

Lemma get_alloc_fd p p_extra mglob oracle fds1 fds2 :
  map_cfprog_name (alloc_fd shparams saparams is_move_op fresh_var_ident pp_sr p p_extra mglob oracle) fds1 = ok fds2 ->
  forall fn fd1,
  get_fundef fds1 fn = Some fd1 ->
  exists2 fd2, alloc_fd shparams saparams is_move_op fresh_var_ident pp_sr p p_extra mglob oracle fn fd1 = ok fd2 &
               get_fundef fds2 fn = Some fd2.
Proof.
  move=> hmap fn fd1.
  by apply: get_map_cfprog_name_gen hmap.
Qed.

(* Here are informal descriptions of the predicates used in the theorem.

   - extend_mem m1 m2 rip data: [m2] is a memory that contains at least [m1]
       and (disjointly) data [data] at address [rip];

   - wf_args: [m2] also contains (disjointly) memory slots for reg ptr
       arguments; writable reg ptr arguments point to memory zones disjoint
       from any zone pointed to by another reg ptr;

   - value_eq_or_in_mem: link between the values taken as arguments in the source
       and the target (if the argument is not a reg ptr, it is just equality;
       if the argument is a reg ptr, the array in the source can be read in
       memory in the target);

   - alloc_ok: the call is possible in the target (there is enough space in the
       stack, and the top of the stack is aligned if the callee is not an export function);

   - wf_results: a returned reg ptr in the target corresponds to one of the
       arguments (as specified in [sao_return]);

   - value_eq_or_in_mem: link between the values returned in the source
       and the target (if the result is not a reg ptr, it is just equality;
       if the result is a reg ptr, the array in the source can be read in
       memory in the target);

   - mem_unchanged_params: the function call does not modify the stack region,
      except for the regions pointed to by the writable [reg ptr]s given as arguments.
*)
Theorem alloc_progP nrip nrsp data oracle_g oracle (P: uprog) (SP: sprog) fn:
  alloc_prog shparams saparams is_move_op fresh_var_ident pp_sr nrip nrsp data oracle_g oracle P = ok SP ->
  forall ev scs1 m1 vargs1 scs1' m1' vres1,
    sem_call P ev scs1 m1 fn vargs1 scs1' m1' vres1 ->
    forall rip m2 vargs2,
      extend_mem m1 m2 rip data ->
      wf_args (Z.of_nat (size data)) rip m1 m2
        (map (omap pp_writable) (oracle fn).(sao_params))
        (map (oapp pp_align U8) (oracle fn).(sao_params)) vargs1 vargs2 ->
      Forall3 (value_eq_or_in_mem m2) (oracle fn).(sao_params) vargs1 vargs2 ->
      alloc_ok SP fn m2 ->
      exists m2' vres2, [/\
        sem_call SP rip scs1 m2 fn vargs2 scs1' m2' vres2,
        extend_mem m1' m2' rip data,
        Forall3 (wf_result vargs1 vargs2) (oracle fn).(sao_return) vres1 vres2,
        Forall3 (value_eq_or_in_mem m2') (oracle fn).(sao_return) vres1 vres2 &
        mem_unchanged_params m1 m2 m2'
          (map (omap pp_writable) (oracle fn).(sao_params)) vargs1 vargs2].
Proof.
  move=> hprog ev scs1 m1 vargs1 scs1' m1' vres1 hsem1 rip m2 vargs2 hext hargs heqinmems halloc.
  move: hprog; rewrite /alloc_prog.
  t_xrbindP=> mglob hmap /eqP hneq.
  t_xrbindP=> fds hfds.
  set P' := {| p_funcs := _ |} => ?; subst SP.

  have [fd1 hfd1]: exists fd, get_fundef (p_funcs P) fn = Some fd.
  + have [fd1 [hfd1 _]] := sem_callE hsem1.
    by exists fd1.
  have [m2' [vres' [hcall [hext' [hresults [heqinmems' hunchanged]]]]]] :=
    (check_cP
      hext.(em_no_overflow)
      hmap
      (P':=P')
      refl_equal
      hshparams
      hsaparams
      is_move_opP
      (get_alloc_fd hfds)
      hneq
      hsem1
      hext
      hargs
      heqinmems
      halloc).
  by exists m2', vres'; split.
Qed.
Section IT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Theorem it_alloc_progP nrip nrsp data oracle_g oracle (P: uprog) (SP: sprog) fn :
  alloc_prog shparams saparams is_move_op fresh_var_ident pp_sr nrip nrsp data oracle_g oracle P = ok SP ->
  forall ev rip,
  wiequiv_f P SP ev rip
    (fun fn1 fn2 fs1 fs2 =>
      [/\ fscs fs1 = fscs fs2
        , extend_mem (fmem fs1) (fmem fs2) rip data
        , wf_args (Z.of_nat (size data)) rip (fmem fs1) (fmem fs2)
                  (map (omap pp_writable) (oracle fn).(sao_params))
                  (map (oapp pp_align U8) (oracle fn).(sao_params))
                  (fvals fs1) (fvals fs2)
        , Forall3 (value_eq_or_in_mem (fmem fs2)) (oracle fn).(sao_params) (fvals fs1) (fvals fs2)
        & alloc_ok SP fn (fmem fs2) ])
     fn fn
    (fun fn _ fs1 fs2 fr1 fr2 =>
        [/\ fscs fr1 = fscs fr2
          , extend_mem (fmem fr1) (fmem fr2) rip data
          , Forall3 (wf_result (fvals fs1) (fvals fs2)) (oracle fn).(sao_return) (fvals fr1) (fvals fr2)
          , Forall3 (value_eq_or_in_mem (fmem fr2)) (oracle fn).(sao_return) (fvals fr1) (fvals fr2)
          & mem_unchanged_params (fmem fs1) (fmem fs2) (fmem fr2)
              (map (omap pp_writable) (oracle fn).(sao_params)) (fvals fs1) (fvals fs2)]).
Proof.
  move=> hprog ev rip fs1 fs2 [hscs hext hargs heqinmems halloc].
  move: hprog; rewrite /alloc_prog.
  t_xrbindP=> mglob hmap /eqP hneq.
  t_xrbindP=> fds hfds.
  set P' := {| p_funcs := _ |} => ?; subst SP.
  have hpre : sa_pre data rip P' oracle fn fn fs1 fs2 by done.
  have := [elaborate
   it_check_cP
      hext.(em_no_overflow)
      hmap
      (P':=P')
      refl_equal
      hshparams
      hsaparams
      is_move_opP
      (get_alloc_fd hfds)
      hneq
      (fn := fn)
      hpre].
  case: ev.
  by apply xrutt_facts.xrutt_weaken => // ?? [].
Qed.

End IT.

Lemma alloc_prog_get_fundef nrip nrsp data oracle_g oracle (P: uprog) (SP: sprog) :
  alloc_prog shparams saparams is_move_op fresh_var_ident pp_sr nrip nrsp data oracle_g oracle P = ok SP →
  exists2 mglob,
    init_map oracle_g data (p_globs P) = ok mglob &
    ∀ fn fd,
    get_fundef (p_funcs P) fn = Some fd →
    exists2 fd',
      alloc_fd shparams saparams is_move_op fresh_var_ident pp_sr P
        {| sp_rsp := nrsp ; sp_rip := nrip ; sp_globs := data ; sp_glob_names := oracle_g |} mglob oracle fn fd = ok fd' &
      get_fundef (p_funcs SP) fn = Some fd'.
Proof.
  rewrite /alloc_prog; t_xrbindP => mglob -> _ fds ok_fds <- {SP} /=.
  exists mglob; first reflexivity.
  exact: get_alloc_fd.
Qed.

Lemma alloc_fd_checked_sao P p_extra mglob oracle fn fd fd' :
  alloc_fd shparams saparams is_move_op fresh_var_ident pp_sr P p_extra mglob oracle fn fd = ok fd' →
  [/\ size (sao_params (oracle fn)) = size (f_params fd) & size (sao_return (oracle fn)) = size (f_res fd) ].
Proof.
  rewrite /alloc_fd/alloc_fd_aux/check_results.
  t_xrbindP => ?? _ [[? ?] ?] _.
  t_xrbindP => -[[[? ?] ?] ?] ok_params.
  t_xrbindP => _ _ [[? ?] ?] _.
  t_xrbindP => ? _ ok_results _ _.
  split.
  - by case: (size_fmapM2 ok_params).
  by case: (size_mapM2 ok_results).
Qed.

Remark alloc_prog_sp_globs nrip nrsp data oracle_g oracle (P: uprog) (SP: sprog) :
  alloc_prog shparams saparams is_move_op fresh_var_ident pp_sr nrip nrsp data oracle_g oracle P = ok SP →
  sp_globs (p_extra SP) = data.
Proof.
  by rewrite /alloc_prog; t_xrbindP => ???? _ <-.
Qed.

End HSAPARAMS.
