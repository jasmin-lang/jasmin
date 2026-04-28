
(* ** Imports and settings *)
From Coq
Require Import Setoid Morphisms Lia.

Require Import Paco.paco.

From ITree Require Import
  ITree
  ITreeFacts
  Basics.HeterogeneousRelations
  Interp.Recursion
  Eq.Rutt
  Eq.RuttFacts.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From Coq Require Import ZArith Utf8.
Import Relations.

Require it_sems_one_varmap label.
Import word_ssrZ.
Import ssrring.
Import psem it_sems_one_varmap compiler_util label low_memory.
Require Import seq_extra psem_facts.
Require Import constant_prop (*constant_prop_proof*).
Require Import fexpr fexpr_sem fexpr_facts.
Require Export linearization linear_sem linear_facts core_logics relational_logic.
Require Import xrutt xrutt_facts.

Import Memory.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

#[local] Existing Instance withsubword.
#[local] Opaque eval_jump.

Section WITH_PARAMS.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}.

(* TODO: move and also move low_memory.wunsigned_sub_small *)
Lemma wunsigned_sub_small (p: pointer) (n: Z) :
  (0 <= n < wbase Uptr →
   wunsigned (p - wrepr Uptr n) <= wunsigned p →
   wunsigned (p - wrepr Uptr n) = wunsigned p - n)%Z.
Proof.
  move=> n_range.
  rewrite wunsigned_sub_if wunsigned_repr_small //.
  case: ZleP => //.
  by lia.
Qed.

Lemma wunsigned_top_stack_after_aligned_alloc m e m' :
  (0 <= sf_stk_sz e →
   0 <= sf_stk_extra_sz e →
   stack_frame_allocation_size e < wbase Uptr →
   is_align (top_stack m) (sf_align e) →
   alloc_stack m (sf_align e) (sf_stk_sz e) (sf_stk_ioff e) (sf_stk_extra_sz e) = ok m' →
  wunsigned (top_stack m) = wunsigned (top_stack m') + stack_frame_allocation_size e)%Z.
Proof.
  move => sz_pos extra_pos sf_noovf sp_align ok_m'.
  rewrite (alloc_stack_top_stack ok_m') (top_stack_after_aligned_alloc _ sp_align) -/(stack_frame_allocation_size _) wrepr_opp wunsigned_sub.
  - lia.
  have sf_pos : (0 <= stack_frame_allocation_size e)%Z.
  - rewrite /stack_frame_allocation_size.
    have := round_ws_range (sf_align e) (sf_stk_sz e + sf_stk_extra_sz e).
    lia.
  assert (top_stack_range := wunsigned_range (top_stack m)).
  split; last lia.
  rewrite Z.le_0_sub.
  exact: (aligned_alloc_no_overflow sz_pos extra_pos sf_noovf sp_align ok_m').
Qed.

Local Open Scope seq_scope.

Lemma map_li_of_fopn_args_label_in_lcmd ii args :
  label_in_lcmd (map (li_of_fopn_args ii) args) = [::].
Proof. by elim: args => [|[]]. Qed.

Lemma set_up_sp_register_label_in_lcmd liparams ii x sf_sz al y tmp:
  label_in_lcmd (set_up_sp_register liparams ii x sf_sz al y tmp) = [::].
Proof. apply map_li_of_fopn_args_label_in_lcmd. Qed.

Lemma map_li_of_fopn_args_has_label lbl ii args :
  has (is_label lbl) (map (li_of_fopn_args ii) args) = false.
Proof. by elim: args => [|[]]. Qed.

Lemma set_up_sp_register_has_label lbl liparams ii x sf_sz al y tmp:
  has (is_label lbl) (set_up_sp_register liparams ii x sf_sz al y tmp) = false.
Proof. apply map_li_of_fopn_args_has_label. Qed.

Lemma align_bind ii a p1 l :
  (let: (lbl, lc) := align ii a p1 in (lbl, lc ++ l)) =
  align ii a (let: (lbl, lc) := p1 in (lbl, lc ++ l)).
Proof. by case: p1 a => lbl lc []. Qed.

Section CAT.

  Context
    (liparams : linearization_params)
    (p : sprog).

  Let linear_i := linear_i liparams p.

  Let Pi (i:instr) :=
    forall fn lbl tail,
     linear_i fn i lbl tail =
     let: (lbl, lc) := linear_i fn i lbl [::] in (lbl, lc ++ tail).

  Let Pr (i:instr_r) :=
    forall ii, Pi (MkI ii i).

  Let Pc (c:cmd) :=
    forall fn lbl tail,
     linear_c (linear_i fn) c lbl tail =
     let: (lbl, lc) := linear_c (linear_i fn) c lbl [::] in (lbl, lc ++ tail).

  Let Pf (fd:sfundef) := True.

  #[ local ]
  Lemma cat_mkI: forall i ii, Pr i -> Pi (MkI ii i).
  Proof. by []. Qed.

  #[ local ]
  Lemma cat_skip : Pc [::].
  Proof. by []. Qed.

  #[ local ]
  Lemma cat_seq : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc fn lbl l /=.
    by rewrite Hc; case: linear_c => lbl1 lc1; rewrite Hi (Hi _ lbl1 lc1); case: linear_i => ??; rewrite catA.
  Qed.

  #[ local ]
  Lemma cat_assgn : forall x tg ty e, Pr (Cassgn x tg ty e).
  Proof. by move => x tg [] // sz e ii lbl c /=; case: assert. Qed.

  #[ local ]
  Lemma cat_opn : forall xs t o es, Pr (Copn xs t o es).
  Proof.
    move => xs tg op es ii fn lbl tl /=.
    by do 2 (case: oseq.omap => // ?).
  Qed.

  #[ local ]
  Lemma cat_syscall : forall xs o es, Pr (Csyscall xs o es).
  Proof. by []. Qed.

  #[ local ]
  Lemma cat_assert : forall a, Pr (Cassert a).
  Proof. by []. Qed.

  #[ local ]
  Lemma cat_if   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 ii fn lbl l /=.
    case Heq1: (c1)=> [|i1 l1].
    + by rewrite Hc2 (Hc2 _ _ [:: _]); case: linear_c => lbl1 lc1; rewrite cats1 /= cat_rcons.
    rewrite -Heq1=> {Heq1 i1 l1};case Heq2: (c2)=> [|i2 l2].
    + by rewrite Hc1 (Hc1 _ _ [::_]); case: linear_c => lbl1 lc1; rewrite cats1 /= cat_rcons.
    rewrite -Heq2=> {Heq2 i2 l2}.
    rewrite Hc1 (Hc1 _ _ [::_]); case: linear_c => lbl1 lc1.
    rewrite Hc2 (Hc2 _ _ [::_ & _]); case: linear_c => lbl2 lc2.
    by rewrite /= !cats1 /= -!cat_rcons catA.
  Qed.

  #[ local ]
  Lemma cat_for : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir, lo, hi) c).
  Proof. by []. Qed.

  #[ local ]
  Lemma cat_while : forall a c e ei c', Pc c -> Pc c' -> Pr (Cwhile a c e ei c').
  Proof.
    move=> a c e ei c' Hc Hc' ii fn lbl l /=.
    case: is_bool => [ [] | ].
    + rewrite Hc' (Hc' _ _ [:: _]) align_bind; f_equal; case: linear_c => lbl1 lc1.
      by rewrite Hc (Hc _ _ (_ ++ _)); case: linear_c => lbl2 lc2; rewrite !catA cats1 -cat_rcons.
    + by apply Hc.
    case: c' Hc' => [ _ | i c' ].
    + by rewrite Hc (Hc _ _ [:: _]) align_bind; case: linear_c => lbl1 lc1; rewrite /= cats1 cat_rcons.
    move: (i :: c') => { i }c' Hc'.
    rewrite Hc (Hc _ _ [:: _]); case: linear_c => lbl1 lc1.
    rewrite Hc' (Hc' _ _ (_ :: _)); case: linear_c => lbl2 lc2.
    rewrite /=. f_equal. f_equal.
    by case: a; rewrite /= cats1 -catA /= cat_rcons.
  Qed.

  #[ local ]
  Lemma cat_call : forall xs f es, Pr (Ccall xs f es).
  Proof.
    move=> xs fn es ii fn' lbl tail /=.
    case: get_fundef => // fd; case: is_RAnoneP => //.
    by case: sf_return_address => // [ ra ? | ra_call ra_return ra_ofs ? ] _; rewrite cats0 -catA.
  Qed.

  Lemma linear_i_nil fn i lbl tail :
     linear_i fn i lbl tail =
     let: (lbl, lc) := linear_i fn i lbl [::] in (lbl, lc ++ tail).
  Proof.
    exact:
      (instr_Rect cat_mkI cat_skip cat_seq cat_assgn cat_opn cat_syscall cat_assert cat_if cat_for cat_while cat_call).
  Qed.

  Lemma linear_c_nil fn c lbl tail :
     linear_c (linear_i fn) c lbl tail =
     let: (lbl, lc) := linear_c (linear_i fn) c lbl [::] in (lbl, lc ++ tail).
  Proof.
    exact:
      (cmd_rect cat_mkI cat_skip cat_seq cat_assgn cat_opn cat_syscall cat_assert cat_if cat_for cat_while cat_call).
  Qed.

End CAT.

(* Predicate describing valid labels occurring inside instructions:
    “valid_labels fn lo hi i” expresses that labels in instruction “i” are within the range [lo; hi[
    and that remote labels to a function other than “fn” are always 1.
*)
Definition valid_labels (fn: funname) (lo hi: label) (i: linstr) : bool :=
  match li_i i with
  | Lopn _ _ _
  | Lsyscall _
  | Lalign
  | Ligoto _
  | Lret
    => true
  | Llabel _ lbl
  | LstoreLabel _ lbl
  | Lcond _ lbl
    => (lo <=? lbl) && (lbl <? hi)
  | Lgoto (fn', lbl) | Lcall _ (fn', lbl) =>
    if fn' == fn then (lo <=? lbl) && (lbl <? hi) else lbl == 1
  end%positive.

Definition valid (fn: funname) (lo hi: label) (lc: lcmd) : bool :=
  all (valid_labels fn lo hi) lc.

Lemma valid_cat fn min max lc1 lc2 :
  valid fn min max (lc1 ++ lc2) = valid fn min max lc1 && valid fn min max lc2.
Proof. exact: all_cat. Qed.

Lemma valid_add_align fn lbl1 lbl2 ii a c :
  valid fn lbl1 lbl2 (add_align ii a c) = valid fn lbl1 lbl2 c.
Proof. by case: a. Qed.

Lemma valid_le_min min2 fn min1 max lc :
  (min1 <=? min2)%positive ->
  valid fn min2 max lc ->
  valid fn min1 max lc.
Proof.
  move => /Pos_leb_trans h; apply: sub_all; rewrite /valid_labels => -[_/=] [] // => [ _ [fn' lbl] | k lbl | [ fn' lbl ] | _ lbl | _ lbl ].
  1,3: case: ifP => // _.
  all: by case/andP => /h ->.
Qed.

Lemma valid_le_max max1 fn max2 min lc :
  (max1 <=? max2)%positive ->
  valid fn min max1 lc ->
  valid fn min max2 lc.
Proof.
  move => /Pos_lt_leb_trans h; apply: sub_all; rewrite /valid_labels => -[_/=] [] // => [ _ [fn' lbl] | k lbl | [ fn' lbl ] | _ lbl | _ lbl ].
  1,3: case: ifP => // _.
  all: by case/andP => -> /h.
Qed.

(** Disjoint labels: all labels in “c” are below “lo” or above “hi”. *)
Definition disjoint_labels (lo hi: label) (c: lcmd) : Prop :=
  ∀ lbl, (lo <= lbl < hi)%positive → ~~ has (is_label lbl) c.

Arguments disjoint_labels _%_positive _%_positive _.

Lemma disjoint_labels_cat lo hi P Q :
  disjoint_labels lo hi P →
  disjoint_labels lo hi Q →
  disjoint_labels lo hi (P ++ Q).
Proof.
  by move => p q lbl r; rewrite has_cat negb_or (p _ r) (q _ r).
Qed.

Lemma disjoint_labels_w lo' hi' lo hi P :
  (lo' <= lo)%positive →
  (hi <= hi')%positive →
  disjoint_labels lo' hi' P →
  disjoint_labels lo hi P.
Proof. move => L H k lbl ?; apply: k; lia. Qed.

Lemma disjoint_labels_wL lo' lo hi P :
  (lo' <= lo)%positive →
  disjoint_labels lo' hi P →
  disjoint_labels lo hi P.
Proof. move => L; apply: (disjoint_labels_w L); lia. Qed.

Lemma disjoint_labels_wH hi' lo hi P :
  (hi <= hi')%positive →
  disjoint_labels lo hi' P →
  disjoint_labels lo hi P.
Proof. move => H; apply: (disjoint_labels_w _ H); lia. Qed.

Lemma valid_disjoint_labels fn A B C D P :
  valid fn A B P →
  (D <= A)%positive ∨ (B <= C)%positive →
  disjoint_labels C D P.
Proof.
  move => V U lbl [L H]; apply/negP => K.
  have {V K} [i _ /andP[] ] := all_has V K.
  case: i => ii [] // k lbl' /andP[] /Pos.leb_le a /Pos.ltb_lt b /eqP ?; subst lbl'.
  lia.
Qed.

Lemma valid_has_not_label fn A B P lbl :
  valid fn A B P →
  (lbl < A ∨ B <= lbl)%positive →
  ~~ has (is_label lbl) P.
Proof.
  move => /(valid_disjoint_labels) - /(_ lbl (lbl + 1)%positive) V R; apply: V; lia.
Qed.

Lemma snot_spec gd s e b :
  sem_pexpr true gd s e = ok (Vbool b) →
  sem_pexpr true gd s (snot e) = sem_pexpr true gd s (Papp1 Onot e).
Proof.
elim: e b => //.
- by case => // e _ b; rewrite /= /sem_sop1 /=; t_xrbindP => z -> b' /to_boolI -> _ /=;
  rewrite negbK.
- by case => // e1 He1 e2 He2 b /=; t_xrbindP => v1 h1 v2 h2 /sem_sop2I [b1 [b2 [b3]]] []
  /to_boolI hb1 /to_boolI hb2 [?] ?; subst v1 v2 b3;
  rewrite /= (He1 _ h1) (He2 _ h2) /= h1 h2;
  apply: (f_equal (@Ok _ _)); rewrite /= ?negb_and ?negb_or.
move => st p hp e1 he1 e2 he2 b /=.
t_xrbindP => bp vp -> /= -> trv1 v1 h1 htr1 trv2 v2 h2 htr2 /= h.
have : exists (b1 b2:bool), eval_atype st = cbool /\ sem_pexpr true gd s e1 = ok (Vbool b1) /\ sem_pexpr true gd s e2 = ok (Vbool b2).
+ rewrite h1 h2;case: bp h => ?;subst.
  + move: htr2.
    have [-> ->]:= truncate_valI htr1.
    by rewrite /truncate_val; t_xrbindP => /= b2 /to_boolI -> ?; eauto.
  move: htr1.
  have [-> ->]:= truncate_valI htr2.
  by rewrite /truncate_val; t_xrbindP => /= b1 /to_boolI -> ?;eauto.
move=> [b1 [b2 [-> []/[dup]hb1 /he1 -> /[dup]hb2 /he2 ->]]] /=.
by rewrite hb1 hb2 /=; case bp.
Qed.

Lemma add_align_nil ii a c : add_align ii a c = add_align ii a [::] ++ c.
Proof. by case: a. Qed.


Section LINEARIZATION_PARAMS.

Context
  (liparams : linearization_params).

Notation itmp := (lip_tmp liparams).
Notation not_saved := (lip_not_saved_stack liparams).
Notation allocate_stack_frame := (lip_allocate_stack_frame liparams).
Notation free_stack_frame := (lip_free_stack_frame liparams).
Notation setup_register := (lip_set_up_sp_register liparams).

Let sf_correct f (op : word Uptr -> word Uptr -> word Uptr) :=
 forall sp_rsp tmp s ts sz,
    let: rspi := vid sp_rsp in
    let: lcmd := f rspi tmp sz in
    let: ts' := Vword (op ts (wrepr Uptr sz)) in
    let: X  := if tmp is Some x then Sv.singleton (v_var x) else Sv.empty in
    (if tmp is Some x then (v_var rspi) <> (v_var x) /\ convertible (vtype x) (aword Uptr) else True)
    -> get_var true (evm s) rspi = ok (Vword ts)
    -> exists vm',
       [/\ sem_fopns_args s lcmd = ok (with_vm s vm'),
           evm s =[\ Sv.add rspi X ] vm'
           & vm'.[rspi] = ts' ].

Let sf_correct1 f (op : word Uptr -> word Uptr -> word Uptr) :=
 forall P Q lp sp_rsp tmp fn s ii ts sz,
    let: rspi := vid sp_rsp in
    let: lcmd := map (li_of_fopn_args ii) (f rspi tmp sz) in
    let: ts' := Vword (op ts (wrepr Uptr sz)) in
    let: X  := if tmp is Some x then Sv.singleton (v_var x) else Sv.empty in
    is_linear_of lp fn (P ++ lcmd ++ Q)
    -> (if tmp is Some x then (v_var rspi) <> (v_var x) /\ convertible (vtype x) (aword Uptr) else True)
    -> get_var true (evm s) rspi = ok (Vword ts)
    -> exists vm',
     let: ls := of_estate s fn (size P) in
     let: ls' :=
       {|
         lscs := lscs ls;
         lmem := lmem ls;
         lvm := vm';
         lfn := fn;
         lpc := size P + size lcmd;
       |}
     in
     [/\ lsem_n lp (pc_between fn (lpc ls) (lpc ls')) ls ls'
       , evm s =[\ Sv.add rspi X ] vm'
       & vm'.[rspi] = ts'
     ].

Definition allocate_stack_frame_correct :=
  Eval hnf in sf_correct allocate_stack_frame (fun x y => x - y)%R.

Definition free_stack_frame_correct :=
  Eval hnf in sf_correct free_stack_frame (fun x y => x + y)%R.

Definition lmove_correct :=
  forall (xd xs : var_i) w ws (w':word ws) s,
    vtype xd = aword Uptr -> convertible (vtype xs) (aword Uptr) ->
    get_var true (evm s) xs = ok (Vword w') ->
    truncate_word Uptr w' = ok w ->
    sem_fopn_args (lip_lmove liparams xd xs) s = ok (with_vm s (evm s).[xd <- Vword w]).

Definition lstore_correct_aux lip_check_ws lip_lstore :=
  forall (xd xs : var_i) ofs ws (w: word ws) wp s m,
    convertible (vtype xs) (aword ws) ->
    lip_check_ws ws ->
    (get_var true (evm s) xd >>= to_word Uptr) = ok wp ->
    (get_var true (evm s) xs >>= to_word ws) = ok w ->
    write (emem s) Aligned (wp + wrepr Uptr ofs)%R w = ok m ->
    sem_fopn_args (lip_lstore xd ofs xs) s = ok (with_mem s m).

Definition lstore_correct := lstore_correct_aux (lip_check_ws liparams) (lip_lstore liparams).

Definition lload_correct_aux lip_check_ws lip_lload :=
  forall (xd xs : var_i) ofs ws wp s w vm,
    convertible (vtype xd) (aword ws) ->
    lip_check_ws ws ->
    (get_var true (evm s) xs >>= to_word Uptr) = ok wp ->
    read (emem s) Aligned (wp + wrepr Uptr ofs)%R ws = ok w ->
    set_var true (evm s) xd (Vword w) = ok vm ->
    sem_fopn_args (lip_lload xd xs ofs) s = ok (with_vm s vm).

Definition lload_correct := lload_correct_aux (lip_check_ws liparams) (lip_lload liparams).

Definition set_up_sp_register_correct :=
  forall vrsp r tmp ts al sz s,
    let: ts' := align_word al (ts - wrepr Uptr sz) in
    let: lcmd := lip_set_up_sp_register liparams vrsp sz al r tmp in
    let: k := Sv.add (v_var r) (Sv.add tmp (Sv.add vrsp vflags)) in
    get_var true (evm s) vrsp = ok (Vword ts) ->
    vtype vrsp = aword Uptr -> convertible (vtype r) (aword Uptr) -> vtype tmp = aword Uptr ->
    v_var tmp <> vrsp ->
    v_var r <> vrsp ->
    v_var r <> tmp ->
    exists vm,
      [/\ sem_fopns_args s lcmd = ok (with_vm s vm)
        , vm =[\ k ] evm s
        , get_var true vm vrsp = ok (Vword ts')
        , get_var true vm r = ok (Vword ts)
        & forall x,
            Sv.In x vflags ->
            ~ is_defined vm.[x] ->
            (evm s).[x] = vm.[x]
      ].

Definition lstores_correct_aux lip_check_ws lip_tmp2 lip_lstores :=
  forall rspi to_save s top m2,
  let tmp2 := vid lip_tmp2  in
  let m1 := emem s in
  let vm1 := evm s in
  let lcmd := lip_lstores rspi to_save in
  ~~ Sv.mem tmp2 (sv_of_list fst to_save) ->
  v_var tmp2 <> v_var rspi ->
  get_var true vm1 rspi >>= to_word Uptr = ok top ->
  foldM (λ '(x, ofs) m,
     Let: ws := if vtype x is aword ws then ok ws else Error ErrType in
     Let _ := assert (lip_check_ws ws) ErrType in
     Let: v := get_var true vm1 x >>= to_word ws in
     write m Aligned (top + wrepr Uptr ofs)%R v) m1 to_save = ok m2 ->
  exists2 vm2,
      sem_fopns_args s lcmd = ok (with_mem (with_vm s vm2) m2)
      & vm1 =[\Sv.singleton tmp2] vm2.

Definition lstores_correct := lstores_correct_aux (lip_check_ws liparams) (lip_tmp2 liparams) (lip_lstores liparams).

Definition lloads_correct_aux lip_check_ws lip_tmp2 lip_lloads :=
  forall rspi to_save ofs s top vm2,
  let tmp2 := vid lip_tmp2 in
  let to_restore := to_save ++ [:: (v_var rspi, ofs)] in
  let m1 := emem s in
  let vm1 := evm s in
  let lcmd := lip_lloads rspi to_save ofs in
  ~~ Sv.mem rspi (sv_of_list fst to_save) ->
  ~~ Sv.mem tmp2 (sv_of_list fst to_save) ->
  v_var tmp2 <> v_var rspi ->
  get_var true vm1 rspi >>= to_word Uptr = ok top ->
  foldM (λ '(x, ofs) vm1,
     Let: ws := if vtype x is aword ws then ok ws else Error ErrType in
     Let _ := assert (lip_check_ws ws) ErrType in
     Let w := read m1 Aligned (top + wrepr Uptr ofs)%R ws in
     set_var true vm1 x (Vword w)) vm1 to_restore = ok vm2 ->
  exists2 vm,
    sem_fopns_args s lcmd = ok (with_vm s vm) &
    vm2 =[\Sv.singleton tmp2] vm.

Definition lloads_correct := lloads_correct_aux (lip_check_ws liparams) (lip_tmp2 liparams) (lip_lloads liparams).

Record h_linearization_params :=
  {
    spec_lip_allocate_stack_frame : allocate_stack_frame_correct;
    spec_lip_free_stack_frame : free_stack_frame_correct;
    spec_lip_set_up_sp_register : set_up_sp_register_correct;
    spec_lip_lmove   : lmove_correct;
    spec_lip_lstore  : lstore_correct;
    spec_lip_lload   : lload_correct;
    spec_lip_lstores : lstores_correct;
    spec_lip_lloads  : lloads_correct;
    spec_lip_tmp     : lip_tmp liparams <> lip_tmp2 liparams;
    spec_lip_check_ws: lip_check_ws liparams Uptr;
  }.

(* FIXME: move this *)
Lemma lset_estate_same ls : lset_estate' ls (to_estate ls) = ls.
Proof. by case: ls. Qed.

Section DEFAULT.

Context (lip_tmp2 : Ident.ident).
Context (lip_check_ws : wsize -> bool)
        (lip_lstore  : var_i -> Z -> var_i -> fopn_args)
        (lip_lload   : var_i -> var_i -> Z -> fopn_args)
        (lip_add_imm : var_i -> var_i -> Z -> seq fopn_args)
        (lip_imm_small : Z -> bool).

Context (lstore_correct : lstore_correct_aux lip_check_ws lip_lstore).

Context (lload_correct : lload_correct_aux lip_check_ws lip_lload).

Definition ladd_imm_correct_aux :=
  forall (x1 x2:var_i) s (w: word Uptr) ofs,
    vtype x1 = aword Uptr -> v_var x1 <> v_var x2 ->
    get_var true (evm s) x2 >>= to_word Uptr = ok w ->
    exists vm,
       [/\ sem_fopns_args s (lip_add_imm x1 x2 ofs) = ok (with_vm s vm)
         , vm =[\ Sv.singleton x1 ] evm s
         & get_var true vm x1 = ok (Vword (w + wrepr Uptr ofs)%R)
       ].

Context (ladd_imm_correct : ladd_imm_correct_aux).

Lemma lstores_dfl_correct1 rspi to_save s top m2:
  let m1 := emem s in
  let vm1 := evm s in
  let lcmd := lstores_dfl lip_lstore rspi to_save in
  Let x := get_var true vm1 rspi in to_pointer x = ok top
  → foldM (λ '(x, ofs) (m : low_memory.mem),
      Let ws := if vtype x is aword ws then ok ws else Error ErrType in
      Let _ := assert (lip_check_ws ws) ErrType in
      Let v := Let x := get_var true vm1 x in to_word ws x in write m Aligned (top + wrepr Uptr ofs)%R v) m1 to_save =
    ok m2
  → sem_fopns_args s lcmd = ok (with_mem s m2) .
Proof.
  elim: to_save s => /= [ | [x ofs] to_save ih] s hget.
  + by move=> [<-]; rewrite with_mem_same.
  t_xrbindP; case heq: vtype => [|||ws]// m' _ [<-] hchk w v hgetx htow hw hf.
  have := lstore_correct (xd:= rspi) (xs:= VarI x dummy_var_info) _ hchk hget _ hw.
  rewrite heq => /(_ (convertible_refl _)) ->.
  + by have /= -> := ih (with_mem s m') hget hf.
  by rewrite hgetx /= htow.
Qed.

Lemma lstores_dfl_correct : lstores_correct_aux lip_check_ws lip_tmp2 (lstores_dfl lip_lstore).
Proof.
  move=> rspi to_save s top m2 /= _ _ hget hf.
  have -> := lstores_dfl_correct1 hget hf.
  by exists (evm s) => //; rewrite with_vm_same.
Qed.

Lemma lstores_imm_dfl_correct :
  lstores_correct_aux lip_check_ws lip_tmp2 (lstores_imm_dfl lip_tmp2 lip_lstore lip_add_imm lip_imm_small).
Proof.
  move=> rspi to_save s top m2 /= hnin hne hget hf.
  rewrite /lstores_imm_dfl.
  case: ifP => _; first by apply: lstores_dfl_correct hget hf.
  move/Sv_memP/sv_of_listP:hnin => hnin.
  set tmp2 := (VarI {| vtype := aword Uptr; vname := lip_tmp2 |} dummy_var_info).
  move: (head _ _).2 => ofs0.
  rewrite sem_fopns_args_cat.
  have [vm2 [-> heq hget' /=]]:= ladd_imm_correct (x1:=tmp2) ofs0 erefl hne hget.
  exists vm2; last by apply eq_exS.
  have hget1 : get_var true (evm (with_vm s vm2)) tmp2 >>= to_word Uptr = ok (top + wrepr Uptr ofs0)%R.
  + by rewrite hget' /= truncate_word_u.
  apply: (lstores_dfl_correct1 hget1) => {hget1}.
  elim: to_save s hnin heq hget hget' hf => //= -[x ofs] to_save ih s hnin heq hget hget'.
  case heqt: vtype => [|||ws] //=; t_xrbindP.
  move=> m -> w v hgetx hwx hw hf /=.
  rewrite (get_var_eq_ex _ _ heq); last first.
  + by move=> /Sv.singleton_spec ?; subst x; rewrite mem_head in hnin.
  rewrite hgetx /= hwx /= -GRing.addrA -wrepr_add.
  have -> : (ofs0 + (ofs - ofs0))%Z =ofs%Z by ring.
  rewrite hw /=; apply: (ih (with_mem s m)) => //.
  by move: hnin; rewrite in_cons negb_or => /andP [].
Qed.

Lemma lloads_aux_correct rspi to_restore s top vm2 :
    let m1 := emem s in
    let vm1 := evm s in
    let lcmd := lloads_aux lip_lload rspi to_restore in
    ~~ Sv.mem rspi (sv_of_list fst to_restore) ->
    get_var true vm1 rspi >>= to_word Uptr = ok top ->
    foldM (λ '(x, ofs) vm1,
       Let: ws := if vtype x is aword ws then ok ws else Error ErrType in
       Let _ := assert (lip_check_ws ws) ErrType in
       Let w := read m1 Aligned (top + wrepr Uptr ofs)%R ws in
       set_var true vm1 x (Vword w)) vm1 to_restore = ok vm2 ->
     sem_fopns_args s lcmd = ok (with_vm s vm2) /\ get_var true vm2 rspi >>= to_word Uptr = ok top.
Proof.
  rewrite /= => /Sv_memP/sv_of_listP.
  elim: to_restore s => /=.
  + by move=> s _ ? [<-]; rewrite with_vm_same.
  move=> [x ofs] to_restore ih s /= hnin hget.
  case heqt: vtype => [|||ws] //=; t_xrbindP.
  move=> vm1 hchk w hread hset hf.
  rewrite (lload_correct (xd := VarI x dummy_var_info) _ hchk hget hread hset);
    last by rewrite heqt; apply convertible_refl.
  apply: ih => //.
  + by move: hnin; rewrite in_cons negb_or => /andP [].
  rewrite -(get_var_eq_ex _ _ (set_var_eq_ex hset)) //.
  by move=> /Sv.singleton_spec ?; subst x; rewrite mem_head in hnin.
Qed.

Lemma lloads_dfl_correct :
  lloads_correct_aux lip_check_ws lip_tmp2 (lloads_dfl lip_lload).
Proof.
  move=> rspi to_rest ofs s top vm2 /= hnin hnin2 hne hget.
  rewrite /lloads_dfl foldM_cat; t_xrbindP => vm1 hf.
  rewrite /=; case heqt: vtype => [|||ws] //=; t_xrbindP.
  move=> vm2' hchk w hread hset ?; subst vm2'.
  have [+ hget2]:= lloads_aux_correct hnin hget hf.
  rewrite /lloads_aux map_cat sem_fopns_args_cat => -> /=.
  rewrite
    (lload_correct
      (xd := VarI rspi dummy_var_info) (s:= with_vm s vm1)
      _ hchk hget2 hread hset);
    last by rewrite heqt; apply convertible_refl.
  by exists vm2.
Qed.

Lemma lloads_imm_dfl_correct :
  lloads_correct_aux lip_check_ws lip_tmp2 (lloads_imm_dfl lip_tmp2 lip_lload lip_add_imm lip_imm_small).
Proof.
  move=> rspi to_rest ofs s top vm2 /= hnin hnin2 hne hget hf.
  rewrite /lloads_imm_dfl; case: ifP => _.
  + by apply: lloads_dfl_correct hnin hnin2 hne hget hf.
  rewrite sem_fopns_args_cat; move: _.2 => ofs0.
  set tmp2 := (VarI {| vtype := aword Uptr; vname := lip_tmp2 |} dummy_var_info).
  have [vm1 [-> heq hget' /=]]:= ladd_imm_correct (x1:=tmp2) ofs0 erefl hne hget.
  set to_restore := map _ _.
  have hnin2': v_var tmp2 \notin (map fst to_restore).
  + rewrite /to_restore !map_cat mem_cat in_cons in_nil /=.
    move/eqP/negbTE: hne => ->; rewrite !orbF -map_comp.
    move/Sv_memP/sv_of_listP: hnin2 => /mapP hnin2.
    by apply /negP => /mapP [x hin heqx]; apply hnin2; exists x => //; rewrite heqx; case: (x).
  have [vm2' {}hf heqx]: exists2 vm2',
      foldM
         (λ '(x, ofs) (vm1 : Vm.t),
            Let ws := match vtype x with
                      | aword ws => ok ws
                      | _ => Error ErrType
                      end
            in (assert (lip_check_ws ws) ErrType >>
                Let w := read (emem s) Aligned ((top + wrepr Uptr ofs0) + wrepr Uptr ofs)%R ws in set_var true vm1 x (Vword w)))
         vm1 to_restore = ok vm2' & vm2 =[\Sv.singleton tmp2] vm2'.
  + move: hnin2'; rewrite /to_restore => {to_restore hget hnin hne hget' hnin2}.
    elim: (to_rest ++ [:: (v_var rspi, ofs)]) s vm1 heq hf => /=.
    + by move=> s vm1 heqx [<-] _; exists vm1 => //; apply eq_exS.
    move=> [x {}ofs] to_restore ih s vm1 heqx.
    case heqt: vtype => [|||ws] //=; t_xrbindP.
    move=> vm1' -> /= w hread hset hf hnin2.
    rewrite -GRing.addrA -wrepr_add.
    have -> : (ofs0 + (ofs - ofs0))%Z =ofs%Z by ring.
    rewrite hread /= set_var_eq_type //=; last by rewrite heqt.
    apply: (ih (with_vm s vm1')) => //=.
    + move=> z hz; move/set_varP: hset => [] _ _ ->.
      by rewrite !Vm.setP heqt vm_truncate_val_eq //; case: eqP => // _; apply heqx.
    by move: hnin2; rewrite negb_or => /andP [].
  have /(_ tmp2) []:= lloads_aux_correct (s:= with_vm s vm1) _ _ hf.
  + by apply/Sv_memP/sv_of_listP.
  + by rewrite hget' /= truncate_word_u.
  by move=> -> _; exists vm2'.
Qed.

End DEFAULT.

Section HLIPARAMS.
  Context
    (hliparams : h_linearization_params).

  Lemma spec_lmove {lp ii ls} {x y:var_i} (w : word Uptr) :
    vtype x = aword Uptr ->
    convertible (vtype y) (aword Uptr) ->
    get_var true (lvm ls) (v_var y) = ok (Vword w) ->
    let li := lmove liparams ii x y in
    let s := to_estate ls in
    eval_instr lp li ls = ok (lnext_pc (lset_estate' ls (with_vm s (evm s).[x <- Vword w]))).
  Proof.
    move=> htx hty hget /=; rewrite -(lset_estate_same ls).
    apply sem_fopn_args_eval_instr.
    by rewrite (spec_lip_lmove hliparams (s:= to_estate ls) htx hty hget (truncate_word_u w)).
  Qed.

  Lemma spec_lstore {lp ii ls m ofs} {x y:var_i} {wx ws' wy'} {wy : word ws'} :
    convertible (vtype y) (aword Uptr) ->
    get_var true (lvm ls) y = ok (Vword wy) ->
    truncate_word Uptr wy = ok wy' ->
    get_var true (lvm ls) x = ok (Vword wx) ->
    write (lmem ls) Aligned (wx + wrepr Uptr ofs)%R wy' = ok m ->
    let: li := lstore liparams ii x ofs y in
    eval_instr lp li ls = ok (lnext_pc (lset_mem ls m)).
  Proof.
    move=> hty hgy htr hgx hw /=.
    apply sem_fopn_args_eval_instr => /=.
    apply: (spec_lip_lstore hliparams (s:= to_estate ls) hty (spec_lip_check_ws hliparams) _ _ hw).
    + by rewrite hgx /= truncate_word_u.
    by rewrite hgy /= htr.
  Qed.

  Lemma spec_lload {lp ii ls ofs} {x y:var_i} {wx wy} :
    convertible (vtype x) (aword Uptr) ->
    get_var true (lvm ls) y = ok (Vword wy) ->
    read (lmem ls) Aligned (wy + wrepr Uptr ofs)%R Uptr = ok wx ->
    let: li := lload liparams ii x y ofs in
    eval_instr lp li ls = ok (lnext_pc (lset_vm ls ls.(lvm).[x <- Vword wx])).
  Proof.
    move=> hty hgy hread /=.
    apply sem_fopn_args_eval_instr => /=.
    apply: (spec_lip_lload hliparams (s:= to_estate ls) hty (spec_lip_check_ws hliparams) _ hread).
    + by rewrite hgy /= truncate_word_u.
    by apply set_var_eq_type => //; rewrite (convertible_eval_atype hty).
  Qed.

  Lemma set_up_sp_register_ok {E E0: Type -> Type} {wE: with_Error E E0}
    {rndE0 : RndEvent syscall_state -< E0}
    ii lp sp_rsp ls r tmp ts al sz P Q :
    let: vrspi := vid sp_rsp in
    let: vrsp := v_var vrspi in
    let: ts' := align_word al (ts - wrepr Uptr sz) in
    let: lcmd := set_up_sp_register liparams ii vrspi sz al r tmp in
    is_linear_of lp (lfn ls) (P ++ lcmd ++ Q) ->
    lpc ls = size P ->
    get_var true (lvm ls) vrsp = ok (Vword ts) ->
    convertible (vtype r) (aword Uptr) -> vtype tmp = aword Uptr ->
    v_var tmp ≠ vrsp ->
    v_var r ≠ vrsp ->
    v_var r ≠ tmp ->
    exists vm',
      let: ls' := setpc (lset_vm ls vm') (size P + size lcmd) in
      let: k := Sv.add (v_var r) (Sv.add tmp (Sv.add vrsp vflags)) in
      [/\ mix_ilsteps lp (pc_between (lfn ls) (lpc ls) (lpc ls')) ls ≈ Ret ls'
        , vm' =[\ k ] lvm ls
        , get_var true vm' vrsp = ok (Vword ts')
        , get_var true vm' r = ok (Vword ts)
        & forall x,
            Sv.In x vflags ->
            ~ is_defined vm'.[x] ->
            (lvm ls).[x] = vm'.[x]
      ].
  Proof.
    move=> hlin hsize hget htyr htytmp hne hne1 hne2.
    have [vm [hsem heq hgrsp hgr hf]] :=
      spec_lip_set_up_sp_register hliparams al sz (s:= to_estate ls) hget erefl htyr htytmp hne hne1 hne2.
    exists vm; split => //.
    rewrite (sem_fopns_args_mix_ilsteps hlin) //=.
    + rewrite hsem; reflexivity.
    by rewrite /set_up_sp_register size_map.
  Qed.

End HLIPARAMS.

End LINEARIZATION_PARAMS.

(** Technical lemma about the compilation: monotony and unicity of labels. *)
Section VALIDITY.
  Context
    (p : sprog)
    (lp : lprog)
    (liparams : linearization_params)
    (hliparams : h_linearization_params liparams).

  Let Pr (i: instr_r) : Prop :=
    ∀ ii fn lbl,
      let: (lbli, li) :=
         linear_i liparams p fn (MkI ii i) lbl [::] in
      (lbl <= lbli)%positive ∧ valid fn lbl lbli li.

  Let Pi (i: instr) : Prop :=
    ∀ fn lbl,
      let: (lbli, li) :=
         linear_i liparams p fn i lbl [::] in
      (lbl <= lbli)%positive ∧ valid fn lbl lbli li.

  Let Pc (c: cmd) : Prop :=
    ∀ fn lbl,
      let: (lblc, lc) :=
         linear_c (linear_i liparams p fn) c lbl [::] in
      (lbl <= lblc)%positive ∧ valid fn lbl lblc lc.

  #[ local ]
  Lemma valid_labels_MkI i ii : Pr i → Pi (MkI ii i).
  Proof. exact. Qed.

  #[ local ]
  Lemma default fn lbl :
    (lbl <= lbl)%positive ∧ valid fn lbl lbl [::].
  Proof. split; reflexivity. Qed.

  #[ local ]
  Lemma valid_labels_nil : Pc [::].
  Proof. exact: default. Qed.

  #[ local ]
  Lemma valid_labels_cons (i : instr) (c : cmd) : Pi i → Pc c → Pc (i :: c).
  Proof.
    move => hi hc fn lbl /=.
    case: linear_c (hc fn lbl) => lblc lc [Lc Vc]; rewrite linear_i_nil.
    case: linear_i (hi fn lblc) => lbli li [Li Vi]; split; first lia.
    rewrite valid_cat; apply/andP; split.
    - apply: valid_le_min _ Vi; apply/Pos.leb_le; lia.
    apply: valid_le_max _ Vc; apply/Pos.leb_le; lia.
  Qed.

  #[ local ]
  Lemma valid_labels_assign (x : lval) (tg : assgn_tag) (ty : atype) (e : pexpr) : Pr (Cassgn x tg ty e).
  Proof. move => ???; exact: default. Qed.

  #[ local ]
  Lemma valid_labels_opn (xs : lvals) (t : assgn_tag) (o : sopn) (es : pexprs) : Pr (Copn xs t o es).
  Proof.
    move => ii fn lbl /=.
    case: oseq.omap => [ ls | ]; last exact: default.
    case: oseq.omap => [ rs | ] ; exact: default.
  Qed.

  #[ local ]
  Lemma valid_labels_syscall (xs : lvals) (o : syscall_t) (es : pexprs) : Pr (Csyscall xs o es).
  Proof. move => ?; exact: default. Qed.

  #[ local ]
  Lemma valid_labels_assert (a : assertion) : Pr (Cassert a).
  Proof. move=> ?; exact: default. Qed.

  #[ local ]
  Lemma valid_labels_if (e : pexpr) (c1 c2 : cmd) : Pc c1 → Pc c2 → Pr (Cif e c1 c2).
  Proof.
    move => hc1 hc2 ii fn lbl /=.
    case: c1 hc1 => [ | i1 c1 ] hc1.
    - rewrite linear_c_nil.
      case: linear_c (hc2 fn (next_lbl lbl)); rewrite /next_lbl => lblc2 lc2 [L2 V2]; split; first lia.
      have lbl_lt_lblc2 : (lbl <? lblc2)%positive by apply/Pos.ltb_lt; lia.
      rewrite /= valid_cat /= /valid_labels /= Pos.leb_refl /= lbl_lt_lblc2 /= andbT.
      apply: valid_le_min _ V2; apply/Pos.leb_le; lia.
    case: c2 hc2 => [ | i2 c2 ] hc2.
    - rewrite linear_c_nil.
      case: linear_c (hc1 fn (next_lbl lbl)); rewrite /next_lbl => lblc1 lc1 [L1 V1]; split; first lia.
      have lbl_lt_lblc1 : (lbl <? lblc1)%positive by apply/Pos.ltb_lt; lia.
      rewrite /= valid_cat /= /valid_labels /= Pos.leb_refl /= lbl_lt_lblc1 /= andbT.
      apply: valid_le_min _ V1; apply/Pos.leb_le; lia.
    rewrite linear_c_nil.
    case: linear_c (hc1 fn (next_lbl (next_lbl lbl))); rewrite /next_lbl => lblc1 lc1 [L1 V1].
    rewrite linear_c_nil.
    case: linear_c (hc2 fn lblc1) => lblc2 lc2 [L2 V2]; split; first lia.
    have lbl_lt_lblc2 : (lbl <? lblc2)%positive by apply/Pos.ltb_lt; lia.
    have lblp1_lt_lblc2 : (lbl + 1 <? lblc2)%positive by apply/Pos.ltb_lt; lia.
    have lbl_le_lblp1 : (lbl <=? lbl + 1)%positive by apply/Pos.leb_le; lia.
    rewrite /= valid_cat /= valid_cat /= /valid_labels /= Pos.leb_refl /= eqxx lbl_lt_lblc2 lblp1_lt_lblc2 lbl_le_lblp1 /= andbT.
    apply/andP; split.
    - apply: valid_le_min _ V2; apply/Pos.leb_le; lia.
    apply: valid_le_min; last apply: valid_le_max _ V1.
    all: apply/Pos.leb_le; lia.
  Qed.

  #[ local ]
  Lemma valid_labels_for (v : var_i) (d: dir) (lo hi : pexpr) (c : cmd) : Pc c → Pr (Cfor v (d, lo, hi) c).
  Proof. move => ? ?; exact: default. Qed.

  #[ local ]
  Lemma valid_labels_while (a : expr.align) (c : cmd) (e : pexpr) (ei : instr_info) (c' : cmd) : Pc c → Pc c' → Pr (Cwhile a c e ei c').
  Proof.
    move => hc hc' ii fn lbl /=.
    case: is_boolP => [ [] | {}e ].
    - rewrite linear_c_nil.
      case: linear_c (hc' fn (next_lbl lbl)); rewrite /next_lbl => lblc' lc' [Lc' Vc'].
      rewrite linear_c_nil.
      case: linear_c (hc fn lblc') => lblc lc [Lc Vc] /=; split; first lia.
      have lbl_lt_lblc : (lbl <? lblc)%positive by apply/Pos.ltb_lt; lia.
      rewrite valid_add_align /= !valid_cat /= /valid_labels /= Pos.leb_refl eqxx lbl_lt_lblc /= andbT.
      apply/andP; split.
      - apply: valid_le_min _ Vc; apply/Pos.leb_le; lia.
      apply: valid_le_max; last apply: valid_le_min _ Vc'; apply/Pos.leb_le; lia.
    - by case: linear_c (hc fn lbl).
    case: c' hc' => [ | i' c' ] hc'.
    - rewrite linear_c_nil.
      case: linear_c (hc fn (next_lbl lbl)); rewrite /next_lbl => lblc lc [Lc Vc] /=; split; first lia.
      have lbl_lt_lblc : (lbl <? lblc)%positive by apply/Pos.ltb_lt; lia.
      rewrite valid_add_align /= valid_cat /= /valid_labels /= Pos.leb_refl lbl_lt_lblc /= andbT.
      apply: valid_le_min _ Vc; apply/Pos.leb_le; lia.
    rewrite linear_c_nil.
    case: linear_c (hc fn (next_lbl (next_lbl lbl))); rewrite /next_lbl => lblc lc [Lc Vc].
    rewrite linear_c_nil.
    case: linear_c (hc' fn lblc) => lblc' lc' [Lc' Vc'] /=; split; first lia.
    have lbl_lt_lblc' : (lbl <? lblc')%positive by apply/Pos.ltb_lt; lia.
    have lbl_le_lblp1 : (lbl <=? lbl + 1)%positive by apply/Pos.leb_le; lia.
    have lblp1_lt_lblc' : (lbl + 1 <? lblc')%positive by apply/Pos.ltb_lt; lia.
    rewrite valid_add_align /= valid_cat /= valid_cat /= /valid_labels /= eqxx Pos.leb_refl lbl_lt_lblc' lbl_le_lblp1 lblp1_lt_lblc' /= andbT.
    apply/andP; split.
    - apply: valid_le_min _ Vc'; apply/Pos.leb_le; lia.
    apply: valid_le_min; last apply: valid_le_max _ Vc.
    all: apply/Pos.leb_le; lia.
  Qed.

  #[ local ]
  Lemma valid_li_of_fopn_args fn lbl1 lbl2 ii l:
    valid fn lbl1 lbl2 [seq li_of_fopn_args ii i | i <- l].
  Proof. by elim l. Qed.

  Remark valid_allocate_stack_frame fn lbl b ii z tmp rastack :
    valid fn lbl (lbl + 1)%positive (allocate_stack_frame liparams p b ii z tmp rastack).
  Proof. by rewrite /allocate_stack_frame; case: ifP => // _; apply: valid_li_of_fopn_args. Qed.

  #[ local ]
  Lemma valid_labels_call (xs : lvals) (f : funname) (es : pexprs) : Pr (Ccall xs f es).
  Proof.
    move => ii fn lbl /=.
    case: get_fundef => [ fd | ]; last by split => //; lia.
    case: is_RAnone; first by split => //; lia.
    have lbl_lt_lblp1 : (lbl <? lbl + 1)%positive by apply/Pos.ltb_lt; lia.
    rewrite /next_lbl; split; first lia.
    rewrite valid_cat /= valid_cat !valid_allocate_stack_frame /= /valid_labels /= Pos.leb_refl lbl_lt_lblp1 /= andbT.
    case: eqP => _ //.
    by rewrite Pos.leb_refl lbl_lt_lblp1.
  Qed.

  Definition linear_has_valid_labels : ∀ c, Pc c :=
    cmd_rect valid_labels_MkI valid_labels_nil valid_labels_cons valid_labels_assign valid_labels_opn valid_labels_syscall valid_labels_assert valid_labels_if valid_labels_for valid_labels_while valid_labels_call.

  Definition linear_has_valid_labels_instr : ∀ i, Pi i :=
    instr_Rect valid_labels_MkI valid_labels_nil valid_labels_cons valid_labels_assign valid_labels_opn valid_labels_syscall valid_labels_assert valid_labels_if valid_labels_for valid_labels_while valid_labels_call.

End VALIDITY.

Section NUMBER_OF_LABELS.
  Context
    (p : sprog)
    (lp : lprog)
    (liparams : linearization_params)
    (hliparams : h_linearization_params liparams).

  Let Pr (i: instr_r) : Prop :=
    ∀ ii fn lbl,
      let: (lbli, li) :=
         linear_i liparams p fn (MkI ii i) lbl [::] in
      (Z.of_nat (size (label_in_lcmd li)) + lbl <= lbli)%Z.

  Let Pi (i: instr) : Prop :=
    ∀ fn lbl,
      let: (lbli, li) :=
         linear_i liparams p fn i lbl [::] in
      (Z.of_nat (size (label_in_lcmd li)) + lbl <= lbli)%Z.

  Let Pc (c: cmd) : Prop :=
    ∀ fn lbl,
      let: (lblc, lc) :=
         linear_c (linear_i liparams p fn) c lbl [::] in
      (Z.of_nat (size (label_in_lcmd lc)) + lbl <= lblc)%Z.

  #[ local ]
  Lemma nb_labels_MkI i ii : Pr i → Pi (MkI ii i).
  Proof. exact. Qed.

  #[ local ]
  Lemma nb_labels_nil : Pc [::].
  Proof. by move => fn lbl; apply Z.le_refl. Qed.

  #[ local ]
  Lemma nb_labels_cons (i : instr) (c : cmd) : Pi i → Pc c → Pc (i :: c).
  Proof.
    move => hi hc fn lbl /=.
    case: linear_c (hc fn lbl) => lblc lc Lc; rewrite linear_i_nil.
    case: linear_i (hi fn lblc) => lbli li Li.
    rewrite label_in_lcmd_cat size_cat Nat2Z.inj_add.
    lia.
  Qed.

  #[ local ]
  Lemma nb_labels_assign (x : lval) (tg : assgn_tag) (ty : atype) (e : pexpr) : Pr (Cassgn x tg ty e).
  Proof. move => ???; exact: Z.le_refl. Qed.

  #[ local ]
  Lemma nb_labels_opn (xs : lvals) (t : assgn_tag) (o : sopn) (es : pexprs) : Pr (Copn xs t o es).
  Proof.
    move=> ii fn lbl /=.
    case: oseq.omap => [ ? | /= ].
    - case: oseq.omap => [ ? | /= ].
    all: apply Z.le_refl.
  Qed.

  #[ local ]
  Lemma nb_labels_syscall (xs : lvals) (o : syscall_t) (es : pexprs) : Pr (Csyscall xs o es).
  Proof. by move=> ii fn lbl /=; apply Z.le_refl. Qed.

  #[ local ]
  Lemma nb_labels_assert (a : assertion) : Pr (Cassert a).
  Proof. by move => ii fn lbl /=; apply Z.le_refl. Qed.

  #[ local ]
  Lemma nb_labels_if (e : pexpr) (c1 c2 : cmd) : Pc c1 → Pc c2 → Pr (Cif e c1 c2).
  Proof.
    move=> hc1 hc2 ii fn lbl /=.
    case: c1 hc1 => [ | i1 c1 ] hc1.
    - rewrite linear_c_nil.
      case: linear_c (hc2 fn (next_lbl lbl)); rewrite /next_lbl => lblc2 lc2 L2.
      rewrite /= label_in_lcmd_cat /= cats0.
      lia.
    case: c2 hc2 => [ | i2 c2 ] hc2.
    - rewrite linear_c_nil.
      case: linear_c (hc1 fn (next_lbl lbl)); rewrite /next_lbl => lblc1 lc1 L1.
      rewrite /= label_in_lcmd_cat /= cats0.
      lia.
    rewrite linear_c_nil.
    case: linear_c (hc1 fn (next_lbl (next_lbl lbl))); rewrite /next_lbl => lblc1 lc1 l1.
    rewrite linear_c_nil.
    case: linear_c (hc2 fn lblc1) => lblc2 lc2 L2.
    rewrite /= label_in_lcmd_cat size_cat Nat2Z.inj_add /=.
    rewrite label_in_lcmd_cat /= cats0.
    lia.
  Qed.

  #[ local ]
  Lemma nb_labels_for (v : var_i) (d: dir) (lo hi : pexpr) (c : cmd) : Pc c → Pr (Cfor v (d, lo, hi) c).
  Proof. by move=> hc ii fn lbl /=; apply Z.le_refl. Qed.

  Lemma label_in_lcmd_add_align ii al lc :
    label_in_lcmd (add_align ii al lc) = label_in_lcmd lc.
  Proof. by case: al. Qed.

  #[ local ]
  Lemma nb_labels_while (a : expr.align) (c : cmd) (e : pexpr) (ei: instr_info) (c' : cmd) : Pc c → Pc c' → Pr (Cwhile a c e ei c').
  Proof.
    move => hc hc' ii fn lbl /=.
    case: is_boolP => [ [] | {}e ].
    - rewrite linear_c_nil.
      case: linear_c (hc' fn (next_lbl lbl)); rewrite /next_lbl => lblc' lc' Lc'.
      rewrite linear_c_nil.
      case: linear_c (hc fn lblc') => lblc lc Lc /=.
      rewrite label_in_lcmd_add_align /=.
      rewrite label_in_lcmd_cat size_cat Nat2Z.inj_add /=.
      rewrite label_in_lcmd_cat /= cats0.
      lia.
    - by case: linear_c (hc fn lbl).
    case: c' hc' => [ | i' c' ] hc'.
    - rewrite linear_c_nil.
      case: linear_c (hc fn (next_lbl lbl)); rewrite /next_lbl => lblc lc Lc /=.
      rewrite label_in_lcmd_add_align /=.
      rewrite label_in_lcmd_cat /= cats0.
      lia.
    rewrite linear_c_nil.
    case: linear_c (hc fn (next_lbl (next_lbl lbl))); rewrite /next_lbl => lblc lc Lc.
    rewrite linear_c_nil.
    case: linear_c (hc' fn lblc) => lblc' lc' Lc'.
    rewrite /= label_in_lcmd_add_align /=.
    rewrite label_in_lcmd_cat size_cat Nat2Z.inj_add /=.
    rewrite label_in_lcmd_cat /= cats0.
    lia.
  Qed.

  Remark label_in_lcmd_li_of_fopn_args ii l :
    label_in_lcmd [seq li_of_fopn_args ii i | i <- l] = [::].
  Proof. by elim l. Qed.

  Remark label_in_lcmd_allocate_stack_frame b ii z tmp rastack :
    label_in_lcmd (allocate_stack_frame liparams p b ii z tmp rastack) = [::].
  Proof. rewrite /allocate_stack_frame; case: ifP => // _; apply label_in_lcmd_li_of_fopn_args. Qed.

  Remark label_in_lcmd_push_to_save ii to_save sp:
    label_in_lcmd (push_to_save liparams p ii to_save sp) = [::].
  Proof. apply label_in_lcmd_li_of_fopn_args. Qed.

  Remark label_in_lcmd_pop_to_save ii to_save sp :
    label_in_lcmd (pop_to_save liparams p ii to_save sp) = [::].
  Proof. apply label_in_lcmd_li_of_fopn_args. Qed.

  #[ local ]
  Lemma nb_labels_call (xs : lvals) (f : funname) (es : pexprs) : Pr (Ccall xs f es).
  Proof.
    move => ii fn lbl /=.
    case: get_fundef => [ fd | ]; last by apply Z.le_refl.
    case: is_RAnone => /=; first by lia.
    rewrite /next_lbl label_in_lcmd_cat label_in_lcmd_allocate_stack_frame.
    rewrite [size _]/= Nat2Z.inj_succ.
    rewrite label_in_lcmd_cat label_in_lcmd_allocate_stack_frame.
    rewrite [Z.of_nat _]/=; lia.
  Qed.

  Definition linear_c_nb_labels : ∀ c, Pc c :=
    cmd_rect nb_labels_MkI nb_labels_nil nb_labels_cons nb_labels_assign nb_labels_opn nb_labels_syscall nb_labels_assert nb_labels_if nb_labels_for nb_labels_while nb_labels_call.

  Definition linear_i_nb_labels : ∀ i, Pi i :=
    instr_Rect nb_labels_MkI nb_labels_nil nb_labels_cons nb_labels_assign nb_labels_opn nb_labels_syscall nb_labels_assert nb_labels_if nb_labels_for nb_labels_while nb_labels_call.

  Lemma linear_body_nb_labels fn fi e body :
    let: (lbl, lc) := linear_body liparams p fn fi e body in
    (Z.of_nat (size (label_in_lcmd lc)) <= lbl)%Z.
  Proof.
    rewrite /linear_body.
    case h: match _ with | RAnone => _ | _ => _ end => [[tail head] lbl0].
    rewrite linear_c_nil.
    have := linear_c_nb_labels body fn lbl0.
    case: linear_c => [lbl lc] /=.
    rewrite !label_in_lcmd_cat !size_cat !Nat2Z.inj_add.
    suff: (Z.of_nat (size (label_in_lcmd head)) + Z.of_nat (size (label_in_lcmd tail)) <= lbl0)%Z
      by lia.
    move: h.
    case: sf_return_address => [|x _| ra_call ra_return z _].
    + case: sf_save_stack => [|x|z] [<- <- <-] //=.
      + by rewrite set_up_sp_register_label_in_lcmd.

      rewrite !label_in_lcmd_cat.
      rewrite set_up_sp_register_label_in_lcmd /=.
      by rewrite label_in_lcmd_push_to_save label_in_lcmd_pop_to_save /=.

    + by move=> [<- <- <-] /=.

    move=> [<- <- <-] /=.
    by case: ra_call ra_return => [?|] [?|] //.
  Qed.

End NUMBER_OF_LABELS.

Section CHECK_SOME.

  Lemma check_SomeP E e A B c m a u :
    @check_Some E e A B c m a = ok u →
    ∃ b, c a = Some b.
  Proof. by move=> /assertP /isSomeP. Qed.

  Lemma check_fexprP ii e u :
    check_fexpr ii e = ok u →
    ∃ f, fexpr_of_pexpr e = Some f.
    Proof. exact: check_SomeP. Qed.

  Lemma check_rexprP ii e u :
    check_rexpr ii e = ok u →
    ∃ r, rexpr_of_pexpr e = Some r.
    Proof. exact: check_SomeP. Qed.

  Lemma check_lexprP ii x u :
    check_lexpr ii x = ok u →
    ∃ l, lexpr_of_lval x = Some l.
    Proof. exact: check_SomeP. Qed.

End CHECK_SOME.

Lemma to_fexpr_snot e f :
  fexpr_of_pexpr e = Some f →
  ∃ nf, fexpr_of_pexpr (snot e) = Some nf.
Proof.
  elim: e f => //=.
  - by move => > _; eexists.
  - by case => x [] // > _; eexists.
  - move => op ? _ ? /oseq.obindI[] b [] hb.
    by case: op => *; rewrite /= hb /=; eauto.
  - move => op ? ih1 ? ih2 ? /oseq.obindI[] a [] ha /oseq.obindI[] b [] hb _.
    case: (ih1 _ ha) => ? {} ih1.
    case: (ih2 _ hb) => ? {} ih2.
    by case: op => *; rewrite /= ?(ha, hb, ih2, ih1) /=; eauto.
  case => // ? A ? B ? C ? /oseq.obindI[] a [] {}A /oseq.obindI[] b [] /B[] ? {}B /oseq.obindI[] c [] /C[] ? {}C _.
  by rewrite A B C /=; eauto.
Qed.

Section PROOF.

  Context
    (liparams : linearization_params)
    (hliparams : h_linearization_params liparams)
    (p : sprog)
    (p' : lprog).

  Let vgd : var := Var (aword Uptr) (sp_rip (p_extra p)).
  Let vrsp : var := Var (aword Uptr) (sp_rsp (p_extra p)).
  Let vrspi : var_i := mk_var_i vrsp.
  Let vrspg : gvar := {| gv := vrspi; gs := Slocal; |}.

  Let var_tmp  : var_i := vid (lip_tmp liparams).
  Let var_tmp2 : var_i := vid (lip_tmp2 liparams).
  Let var_tmps : Sv.t  := Sv.add var_tmp2 (Sv.singleton var_tmp).

  Hypothesis var_tmps_not_magic : disjoint var_tmps (magic_variables p).

  Lemma var_tmp_not_magic : ~~ Sv.mem var_tmp (magic_variables p).
  Proof.
    move/Sv.is_empty_spec: var_tmps_not_magic; rewrite /var_tmps => ?.
    apply/Sv_memP; SvD.fsetdec.
  Qed.

  Lemma var_tmp2_not_magic : ~~ Sv.mem var_tmp2 (magic_variables p).
  Proof.
    move/Sv.is_empty_spec: var_tmps_not_magic; rewrite /var_tmps => ?.
    apply/Sv_memP; SvD.fsetdec.
  Qed.

  Hypothesis linear_ok : linear_prog liparams p = ok p'.

  Notation is_linear_of := (is_linear_of p').
  Notation check_i := (check_i p).
  Notation check_fd := (check_fd liparams p).
  Notation linear_i := (linear_i liparams p).
  Notation linear_c fn := (linear_c (linear_i fn)).
  Notation linear_fd := (linear_fd liparams p).

(*  Notation sem_I := (sem_one_varmap.sem_I p var_tmp).
  Notation sem_i := (sem_one_varmap.sem_i p var_tmp).
  Notation sem := (sem_one_varmap.sem p var_tmp). *)

  Notation valid_c fn c :=
    (linear_has_valid_labels p liparams c fn).
  Notation valid_i fn i :=
    (linear_has_valid_labels_instr p liparams i fn).

  Notation set_up_sp_register := (set_up_sp_register liparams).

  Lemma hneq_vtmp_vrsp :
    v_var var_tmp <> vrsp.
  Proof.
    move: var_tmp_not_magic.
    move=> /Sv_memP.
    t_notin_add.
    by move=> /Sv.singleton_spec.
  Qed.

  Lemma hneq_vtmp2_vrsp :
    v_var var_tmp2 <> vrsp.
  Proof.
    move: var_tmp2_not_magic.
    move=> /Sv_memP.
    t_notin_add.
    by move=> /Sv.singleton_spec.
  Qed.

  Lemma hneq_vtmp_vtmp2 :
    v_var var_tmp <> v_var var_tmp2.
  Proof. move=> []; apply: spec_lip_tmp hliparams. Qed.

  Definition checked_i fn i : bool :=
    if get_fundef (p_funcs p) fn is Some fd
    then
      if check_i fn fd.(f_extra) i is Ok tt
      then true
      else false
    else false.

  Lemma checked_iE fn i :
    checked_i fn i →
    exists2 fd, get_fundef (p_funcs p) fn = Some fd & check_i fn fd.(f_extra) i = ok tt.
  Proof.
    rewrite /checked_i; case: get_fundef => // fd h; exists fd; first by [].
    by case: check_i h => // - [].
  Qed.

  Definition checked_c fn c : bool :=
    if get_fundef (p_funcs p) fn is Some fd
    then
      if check_c (check_i fn fd.(f_extra)) c is Ok tt
      then true
      else false
    else false.

  Lemma checked_cE fn c :
    checked_c fn c →
    exists2 fd, get_fundef (p_funcs p) fn = Some fd & check_c (check_i fn fd.(f_extra)) c = ok tt.
  Proof.
    rewrite /checked_c; case: get_fundef => // fd h; exists fd; first by [].
    by case: check_c h => // - [].
  Qed.

  Lemma checked_cI fn i c :
    checked_c fn (i :: c) →
    checked_i fn i ∧ checked_c fn c.
  Proof.
    by case/checked_cE => fd ok_fd; rewrite /checked_c /checked_i ok_fd /= ; t_xrbindP => -> ->.
  Qed.

  Local Lemma p_globs_nil : p_globs p = [::].
  Proof.
    by move: linear_ok; rewrite /linear_prog; t_xrbindP => _ /eqP /size0nil.
  Qed.

  Local Lemma checked_prog fn fd :
    get_fundef (p_funcs p) fn = Some fd →
    check_fd fn fd = ok tt.
  Proof.
    move: linear_ok; rewrite /linear_prog; t_xrbindP => ok_p _ _ _.
    move: ok_p; rewrite /check_prog; t_xrbindP => r C _ M.
    by have [[]]:= get_map_cfprog_name_gen C M.
  Qed.

  Lemma get_fundef_p' f fd :
    get_fundef (p_funcs p) f = Some fd →
    get_fundef (lp_funcs p') f
    = Some (linear_fd f fd).2.
  Proof.
    move: linear_ok; rewrite /linear_prog; t_xrbindP => _ _ _ <- /=.
    elim: (p_funcs p) 1%positive => [|[f' fd'] funcs ih] nb_lbl //=.
    set nb_lbl' := (nb_lbl + _)%positive.
    move: (ih nb_lbl').
    case hfmap: fmap => [nb_lbl'' funcs''] /= {}ih.
    case: eqP => [|_ //].
    by move=> <- [->].
  Qed.

  Lemma lp_ripE : lp_rip p' = sp_rip p.(p_extra).
  Proof. by move: linear_ok; rewrite /linear_prog; t_xrbindP => _ _ _ <-. Qed.

  Lemma lp_rspE : lp_rsp p' = sp_rsp p.(p_extra).
  Proof. by move: linear_ok; rewrite /linear_prog; t_xrbindP => _ _ _ <-. Qed.

  Lemma lp_globsE : lp_globs p' = sp_globs p.(p_extra).
  Proof. by move: linear_ok; rewrite /linear_prog; t_xrbindP => _ _ _ <-. Qed.

  Lemma fmap_linear_fd_acc lbl funcs :
    let (nb_lbl, funcs') :=
      fmap (fun nb_lbl '(f,fd) =>
        let fd := linear_fd f fd in
        ((nb_lbl + fd.1)%positive, (f, fd.2))) 1%positive funcs
    in
    fmap (fun nb_lbl '(f,fd) =>
      let fd := linear_fd f fd in
      ((nb_lbl + fd.1)%positive, (f, fd.2))) (1+lbl)%positive funcs = ((nb_lbl + lbl)%positive, funcs').
  Proof.
    elim: funcs lbl => [|[f fd] funcs ih] lbl //=.
    set linear_f := (fun _ => _).
    have := ih ((linear_body liparams p f (f_info fd) (f_extra fd) (f_body fd)).1)%positive.
    have := ih (lbl + (linear_body liparams p f (f_info fd) (f_extra fd) (f_body fd)).1)%positive.
    case: fmap => [nb_lbl' funcs'].
    rewrite Pos.add_assoc => -> ->.
    by rewrite (Pos.add_comm lbl) Pos.add_assoc.
  Qed.

  Lemma small_dom_p' : small_dom (label_in_lprog p').
  Proof.
    move: linear_ok; rewrite /linear_prog.
    t_xrbindP=> _ _ /ZleP hle <-.
    rewrite /small_dom /label_in_lprog; apply /ZleP.
    apply: Z.le_trans hle.

    elim: (p_funcs p) => [|[fn f'] funcs ih] //=.
    have := fmap_linear_fd_acc ((linear_fd fn f').1)%positive funcs.
    case: fmap ih => [nb_lbl funcs'] /= ih -> /=.
    rewrite size_cat size_map Nat2Z.inj_add.
    have := linear_body_nb_labels p liparams fn (f_info f') (f_extra f') (f_body f').
    case: linear_body => [nb_lbl' lc] /=.
    lia.
  Qed.

  Local Coercion emem : estate >-> mem.
  Local Coercion evm : estate >-> Vm.t.

  (** Relation between source and target memories
      - There is a well-aligned valid block in the target
   *)
  Record match_mem_gen (sp:word Uptr) (m m': mem) : Prop :=
    MM {
       read_incl_mem : ∀ p,
         ~ (wunsigned (stack_limit m) <= wunsigned p < wunsigned sp)%Z ->
         validw m Aligned p U8 -> read m Aligned p U8 = read m' Aligned p U8
     ; read_incl_stk : ∀ p w,
         (wunsigned (stack_limit m) <= wunsigned p < wunsigned sp)%Z ->
         read m Aligned p U8 = ok w -> read m' Aligned p U8 = ok w
     ; valid_incl : ∀ p, validw m Aligned p U8 → validw m' Aligned p U8
     ; valid_stk  : ∀ p,
         (wunsigned (stack_limit m) <= wunsigned p < wunsigned(stack_root m))%Z
       → validw m' Aligned p U8
      }.

  Definition match_mem m m' := match_mem_gen (top_stack m) m m'.

  (* We can give a simpler read_incl_mem for match_mem. *)
  Lemma match_mem_read_incl_mem m m' :
    match_mem m m' ->
    forall p, validw m Aligned p U8 ->
    read m Aligned p U8 = read m' Aligned p U8.
  Proof.
    move=> hmm pr hvalid.
    apply hmm.(read_incl_mem) => // hb.
    by have /negP := stack_region_is_free hb.
  Qed.

  Lemma mm_free sp m1 m1' :
    match_mem_gen sp m1 m1' →
    match_mem_gen sp (free_stack m1) m1'.
  Proof.
    case => Hrm Hrstk Hvm Hsm; split.
    (* read mem *)
    + move=> p1 hb Hv.
      rewrite -(free_stackP _).(fss_read_old8) //.
      apply Hrm.
      + by move: hb; rewrite (free_stackP _).(fss_limit).
      by move: Hv; rewrite (free_stackP _).(fss_valid) => /andP [+ _].
    (* read stk *)
    + move=> p1 w1 hb Hr.
      apply Hrstk.
      + by move: hb; rewrite (free_stackP _).(fss_limit).
      rewrite -Hr. apply: fss_read_old; [ exact: free_stackP | exact: readV Hr ].
    (* valid *)
    + move=> p1 Hv.
      assert (Hs := free_stackP). move: (Hs m1)=> Hm1. move: (Hs m1')=> Hm1'.
      have Heq := (fss_valid Hm1). have Heq' := (fss_valid Hm1').
      apply Hvm. rewrite Heq in Hv. move: Hv. move=>/andP [] Hv1 Hv2.
      apply Hv1.
    (* stack *)
    assert (Hs := free_stackP). move: (Hs m1)=> Hm1. move: (Hs m1')=> Hm1'.
    have Heq := (fss_valid Hm1).
    move=> p1 Hs'. apply Hsm. have <- := fss_root Hm1. by have <- := fss_limit Hm1.
  Qed.

  Lemma mm_read_ok : ∀ sp m m' al a s v,
    match_mem_gen sp m m' →
    read m al a s = ok v →
    read m' al a s = ok v.
  Proof.
    move=> sp m m' al p'' s v [] Hrm Hrstk Hvm Hsm Hr.
    have [_ Hread] := read_read8 Hr.
    rewrite -Hr; apply eq_read => al' i Hi.
    rewrite !(read8_alignment Aligned) {al'}.
    have := Hread i Hi; rewrite (read8_alignment Aligned) => {}Hread.
    case:
      (boolP
        ((wunsigned (stack_limit m) <=? wunsigned (add p'' i))
        && (wunsigned (add p'' i) <? wunsigned sp))%Z);
      rewrite !zify => hb.
    + by rewrite Hread; apply Hrstk.
    by symmetry; apply (Hrm _ hb (readV Hread)).
  Qed.

  Lemma mm_write : ∀ sp m1 m1' al p s (w:word s) m2,
    match_mem_gen sp m1 m1' →
    write m1 al p w = ok m2 →
    exists2 m2', write m1' al p w = ok m2' & match_mem_gen sp m2 m2'.
  Proof.
    move=> sp m1 m1' al p'' sz w m2 Hm Hw.
    case: Hm=> Hrm Hrstk Hvm Hsm.
    have /(writeV w) [m2' Hw']: validw m1' al p'' sz.
    + have /validwP [Ha Hvalid] := (write_validw Hw).
      apply /validwP; split=> // i Hi.
      rewrite (validw8_alignment Aligned); apply Hvm.
      by rewrite (validw8_alignment al); apply Hvalid.
    exists m2' => //.
    constructor.
    (* read mem *)
    + move=> p1 hb Hv.
      apply: (read_write_any_mem _ Hw Hw').
      apply Hrm.
      + by move: hb; rewrite (write_mem_stable Hw).(ss_limit).
      by rewrite -(write_validw_eq Hw).
    (* read stk *)
    + move=> p1 w1 hb.
      have -> := write_read8 Hw Aligned p1.
      have -> /= := write_read8 Hw' Aligned p1.
      case: ifP=> // _.
      apply Hrstk.
      by move: hb; rewrite (write_mem_stable Hw).(ss_limit).
    (* valid *)
    + move=> p1 Hv.
      rewrite (write_validw_eq Hw').
      apply Hvm.
      by rewrite -(write_validw_eq Hw).
    (* stack *)
    move=> p1 H.
    rewrite (write_validw_eq Hw').
    apply Hsm.
    by have [-> -> _] := (write_mem_stable Hw).
  Qed.

  Lemma mm_alloc sp m1 m1' al sz ioff es' m2 :
    (wunsigned (top_stack m1) <= wunsigned sp)%Z ->
    match_mem_gen sp m1 m1' →
    alloc_stack m1 al sz ioff es' = ok m2 →
    match_mem_gen sp m2 m1'.
  Proof.
    move=> hle.
    case => Hrm Hrstk Hvm Hs /alloc_stackP ass.
    have heq := ass_add_ioff ass; case: ass => Hvr Hve Hveq Ha Hs' hioff Hs'' Hsr Hsl Hf.
    constructor.
    (* read mem *)
    + move=> p1 hb.
      rewrite Hveq => /orP [Hv|hb'].
      + rewrite -(Hvr p1 Hv).
        apply: Hrm Hv.
        by rewrite -Hsl.
      exfalso; apply hb; move: hb'; rewrite /between /zbetween !zify wsize8.
      rewrite heq Hsl.
      have := [elaborate top_stack_below_root _ m1]; rewrite -/(top_stack _).
      by lia.
    (* read stk *)
    + move=> p1 w1 hb /[dup] Hr1.
      move: (Hve p1) (Hvr p1).
      have -> := readV Hr1.
      case: validw.
      * move => _ <- //; apply Hrstk.
        by rewrite -Hsl.
      by move => ->.
    (* valid *)
    + move => p1; rewrite Hveq => /orP[]; first exact: Hvm.
      move => range; apply: Hs; move: range; rewrite !zify => - [] lo.
      change (wsize_size U8) with 1%Z.
      generalize (top_stack_below_root _ m1); rewrite -/(top_stack m1).
      lia.
    (* stack *)
    move=> p1 Hs'''. apply Hs. by rewrite -Hsr -Hsl.
  Qed.

  Lemma mm_write_invalid sp m m1' a s (w: word s) :
    (wunsigned (top_stack m) <= wunsigned sp)%Z ->
    match_mem_gen sp m m1' →
    (wunsigned (stack_limit m) <= wunsigned a ∧ wunsigned a + wsize_size s <= wunsigned (top_stack m))%Z →
    is_align a s →
    exists2 m2', write m1' Aligned a w = ok m2' & match_mem_gen sp m m2'.
  Proof.
    move=> hle.
    case => Hrm Hrstk Hvm Hs Hs' al.
    have /(writeV w) [m' ok_m']: validw m1' Aligned a s.
    - apply/validwP; split; first exact: al.
      move => k [] klo khi; apply: Hs.
      have a_range := wunsigned_range a.
      assert (r_range := wunsigned_range (stack_root m)).
      generalize (top_stack_below_root _ m); rewrite -/(top_stack m) => R.
      by rewrite wunsigned_add; lia.
    exists m'; first exact: ok_m'.
    split.
    (* read mem *)
    - move => p1 hb Hv.
      rewrite (CoreMem.writeP_neq _ ok_m'); first exact: Hrm.
      move => i j [] i_low i_hi; change (wsize_size U8) with 1%Z => j_range.
      have ? : j = 0%Z by lia.
      subst j => { j_range }.
      rewrite add_0 => ?; subst p1.
      apply hb.
      have a_range := wunsigned_range a.
      assert (r_range := wunsigned_range (stack_root m)).
      generalize (top_stack_below_root _ m); rewrite -/(top_stack m) => R.
      by rewrite wunsigned_add; lia.
    (* read stk *)
    - move => p1 w1 hb Hr.
      rewrite (CoreMem.writeP_neq _ ok_m'); first exact: Hrstk.
      move => i j [] i_low i_hi; change (wsize_size U8) with 1%Z => j_range.
      have ? : j = 0%Z by lia.
      subst j => { j_range }.
      rewrite add_0 => ?; subst p1.
      apply/negP: (readV Hr).
      apply: stack_region_is_free.
      rewrite -/(top_stack m) wunsigned_add; first lia.
      have := wunsigned_range a.
      generalize (wunsigned_range (top_stack m)).
      by lia.
    1-2: move => b; rewrite (CoreMem.write_validw_eq ok_m').
    - exact/Hvm.
    exact/Hs.
  Qed.

  Section MATCH_MEM_SEM_PEXPR.
    Context (scs: syscall_state_t) sp (m m': mem) (vm: Vm.t) (M: match_mem_gen sp m m').
    Let P (e: pexpr) : Prop :=
      ∀ v,
        sem_pexpr true [::] {| escs := scs; emem := m ; evm := vm |} e = ok v →
        sem_pexpr true [::] {| escs := scs; emem := m' ; evm := vm |} e = ok v.

    Let Q (es: pexprs) : Prop :=
      ∀ vs,
        sem_pexprs true [::] {| escs := scs; emem := m ; evm := vm |} es = ok vs →
        sem_pexprs true [::] {| escs := scs; emem := m' ; evm := vm |} es = ok vs.

    Lemma match_mem_gen_sem_pexpr_pair : (∀ e, P e) ∧ (∀ es, Q es).
    Proof.
      apply: pexprs_ind_pair; split.
      - by [].
      - by move => e ihe es ihes vs /=; t_xrbindP => ? /ihe -> /= ? /ihes -> /= ->.
      1-4: by rewrite /P /=.
      - move => al aa sz x e ihe vs /=.
        by apply: on_arr_gvarP => ??? -> /=; t_xrbindP => ?? /ihe -> /= -> /= ? -> /= ->.
      - move => aa sz len x e ihe v /=.
        by apply: on_arr_gvarP => ??? -> /=; t_xrbindP => ?? /ihe -> /= -> /= ? -> /= ->.
      - by move => al sz e ihe v /=; t_xrbindP => ?? /ihe -> /= -> /= ? /(mm_read_ok M) -> /= ->.
      - by move => op e ihe v /=; t_xrbindP => ? /ihe ->.
      - by move => op e1 ih1 e2 ih2 v /=; t_xrbindP => ? /ih1 -> ? /ih2 ->.
      - by move => op es ih vs /=; t_xrbindP => ? /ih; rewrite -/(sem_pexprs _ [::] _ es) => ->.
      by move => ty e ihe e1 ih1 e2 ih2 v /=; t_xrbindP => ?? /ihe -> /= -> ?? /ih1 -> /= -> ?? /ih2 -> /= -> /= ->.
    Qed.

    Lemma match_mem_gen_sem_pexpr e : P e.
    Proof. exact: (proj1 match_mem_gen_sem_pexpr_pair). Qed.

    Lemma match_mem_gen_sem_pexprs es : Q es.
    Proof. exact: (proj2 match_mem_gen_sem_pexpr_pair). Qed.

  End MATCH_MEM_SEM_PEXPR.

  Lemma match_mem_gen_write_lval sp scs1 m1 vm1 m1' scs2 m2 vm2 x v :
    match_mem_gen sp m1 m1' →
    write_lval true [::] x v {| escs := scs1; emem := m1 ; evm := vm1 |} = ok {| escs := scs2; emem := m2 ; evm := vm2 |} →
    exists2 m2',
    write_lval true [::] x v {| escs := scs1; emem := m1' ; evm := vm1 |} = ok {| escs := scs2; emem := m2' ; evm := vm2 |} &
    match_mem_gen sp m2 m2'.
  Proof.
    move => M; case: x => /= [ _ ty | x | al ws vi e | al aa ws x e | aa ws n x e ].
    - by case/write_noneP; rewrite /write_none => -[-> -> ->] -> ->; exists m1'.
    - rewrite /write_var /=; t_xrbindP =>_ -> -> <- -> /=.
      by exists m1'.
    - t_xrbindP => ?? /(match_mem_gen_sem_pexpr M) -> /= -> /= ? -> /= ? /(mm_write M)[] ? -> /= M' <- <- <-.
      eexists; first reflexivity; exact: M'.
    all: apply: on_arr_varP; rewrite /write_var; t_xrbindP => ??? -> /= ?? /(match_mem_gen_sem_pexpr M) -> /= -> /= ? -> /= ? -> /= ? -> /= <- <- <-.
    all: by exists m1'.
  Qed.

  Lemma match_mem_gen_write_lvals sp scs1 m1 vm1 m1' scs2 m2 vm2 xs vs :
    match_mem_gen sp m1 m1' →
    write_lvals true [::] {| escs := scs1; emem := m1 ; evm := vm1 |} xs vs = ok {| escs := scs2; emem := m2 ; evm := vm2 |} →
    exists2 m2',
    write_lvals true [::] {| escs := scs1; emem := m1' ; evm := vm1 |} xs vs = ok {| escs := scs2; emem := m2' ; evm := vm2 |} &
    match_mem_gen sp m2 m2'.
  Proof.
    elim: xs vs scs1 vm1 m1 m1'.
    - by case => // scs1 vm1 m1 m1' M [] <- <- <-; exists m1'.
    by move => x xs ih [] // v vs scs1 vm1 m1 m1' M /=; t_xrbindP => - [] ??? /(match_mem_gen_write_lval M)[] m2' -> M2 /ih - /(_ _ M2).
  Qed.

  Definition is_ra_of (fn: funname) (ra: return_address_location) : Prop :=
    exists2 fd, get_fundef (p_funcs p) fn = Some fd & fd.(f_extra).(sf_return_address) = ra.

  (** Export functions allocate their own stack frames
  * whereas internal functions have their frame allocated by the caller *)
  Definition is_sp_for_call (fn: funname) (m: mem) (ptr: pointer) : Prop :=
    exists2 fd,
    get_fundef (p_funcs p) fn = Some fd &
    let e := fd.(f_extra) in
    if is_RAnone e.(sf_return_address)
    then ptr = top_stack m
    else
      is_align (top_stack m) e.(sf_align) ∧
      let sz := stack_frame_allocation_size e in ptr = (top_stack m - wrepr Uptr sz)%R.

  (* Define where/how the return address is passed by the caller to the callee *)
  Definition value_of_ra
    (m: mem)
    (vm: Vm.t)
    (ra: return_address_location)
    (target: option (remote_label * lcmd * nat))
    : Prop :=
    match ra, target with
    | RAnone, None => True
    | RAreg ra _, Some ((caller, lbl), cbody, pc) =>
      [/\ is_linear_of caller cbody,
          find_label lbl cbody = ok pc,
          (caller, lbl) \in label_in_lprog p' &
          exists2 ptr,
            encode_label (label_in_lprog p') (caller, lbl) = Some ptr &
            vm.[ra] = Vword ptr
      ]

   | RAstack (Some ra) _ _ _ , Some ((caller, lbl), cbody, pc) =>
      [/\ is_linear_of caller cbody,
          find_label lbl cbody = ok pc,
          (caller, lbl) \in label_in_lprog p' &
          exists2 ptr,
            encode_label (label_in_lprog p') (caller, lbl) = Some ptr &
            vm.[ra] = Vword ptr
      ]

    | RAstack None _ ofs _, Some ((caller, lbl), cbody, pc) =>
      [/\ is_linear_of caller cbody,
          find_label lbl cbody = ok pc,
          (caller, lbl) \in label_in_lprog p' &
          exists2 ptr, encode_label (label_in_lprog p') (caller, lbl) = Some ptr &
          exists2 sp, vm.[ vrsp ] = Vword sp & read m Aligned (sp + wrepr Uptr ofs)%R Uptr = ok ptr
      ]

    | _, _ => False
    end.

  (* Export functions save and restore the contents of “to-save” registers. *)
  Definition is_callee_saved_of (fn: funname) (s: seq var) : Prop :=
    exists2 fd,
    get_fundef (p_funcs p) fn = Some fd &
    let e := f_extra fd in
    if is_RAnone (sf_return_address e) then
      s = map fst (sf_to_save e)
    else s = [::].

  (* Execution of linear programs preserve meta-data stored in the stack memory *)
  Definition preserved_metadata (m m1 m2: mem) : Prop :=
    ∀ p : pointer,
      (wunsigned (top_stack m) <= wunsigned p < wunsigned (stack_root m))%Z →
      ~~ validw m Aligned p U8 →
      read m1 Aligned p U8 = read m2 Aligned p U8.

  Instance preserved_metadata_equiv m : Equivalence (preserved_metadata m).
  Proof.
    split; first by [].
    - by move => x y xy ptr r nv; rewrite xy.
    move => x y z xy yz ptr r nv.
    by rewrite xy; first exact: yz.
  Qed.

  Lemma preserved_metadataE (m m' m1 m2: mem) :
    stack_stable m m' →
    validw m =3 validw m' →
    preserved_metadata m' m1 m2 →
    preserved_metadata m m1 m2.
  Proof.
    move => ss e h ptr r nv.
    apply: h.
    - by rewrite -(ss_top_stack ss) -(ss_root ss).
    by rewrite -e.
  Qed.

  Lemma write_mem_unchanged m1 m2 m1' m2' al ptr sz (w w' : word sz) :
    write m1 al ptr w = ok m1' ->
    write m2 al ptr w' = ok m2' ->
    forall p, ~~ validw m1 Aligned p U8 -> read m2 Aligned p U8 = read m2' Aligned p U8.
  Proof.
    move=> hw1 hw2 pr hnv.
    symmetry; apply (writeP_neq _ hw2).
    apply: disjoint_range_valid_not_valid_U8; first by apply (write_validw hw1).
    by apply /negP; apply hnv.
  Qed.

  Lemma write_lval_mem_unchanged x v v' s s' t t' sp :
    write_lval true [::] x v s = ok s' →
    write_lval true [::] x v' t = ok t' →
    escs s = escs t →
    s <=1 t →
    match_mem_gen sp s t →
    ∀ p, ~~ validw (emem s) Aligned p U8 → read (emem t) Aligned p U8 = read (emem t') Aligned p U8.
  Proof.
    case: x.
    - move => /= _ ty /write_noneP[] <- _ _ /write_noneP[] -> _ _; reflexivity.
    - move => x /write_var_memP -> /write_var_memP ->; reflexivity.
    - case: s t => scs m vm [] tscs tv tvm /=.
      move => al sz vi e ok_s' ok_t' E X M; subst tscs.
      move: ok_s' => /=; t_xrbindP => ofs ev ok_ev ok_ofs w ok_w m' ok_m' _{s'}.
      move: ok_t' => /=.
      have /= ok_ev' := match_mem_gen_sem_pexpr M ok_ev.
      have /(_ _ X) := sem_pexpr_uincl _ ok_ev'.
      case => ev' -> /of_value_uincl_te h /=.
      have {h} /= -> /= := (h (cword _) _ ok_ofs).
      t_xrbindP => w' ok_w' tm' ok_tm' <-{t'} /=.
      by apply (write_mem_unchanged ok_m' ok_tm').
    - move => al aa sz x e; apply: on_arr_varP; rewrite /write_var; t_xrbindP => ???????????????.
      apply: on_arr_varP; rewrite /write_var; t_xrbindP => ???????????????.
      subst; reflexivity.
    move => aa sz k x e; apply: on_arr_varP; rewrite /write_var; t_xrbindP => ???????????????.
    apply: on_arr_varP; rewrite /write_var; t_xrbindP => ???????????????.
    subst; reflexivity.
  Qed.

  Lemma write_lvals_mem_unchanged xs vs vs' s s' t t' sp :
    List.Forall2 value_uincl vs vs' →
    write_lvals true [::] s xs vs = ok s' →
    write_lvals true [::] t xs vs' = ok t' →
    escs s = escs t →
    s <=1 t →
    match_mem_gen sp s t →
    ∀ p, ~~ validw (emem s) Aligned p U8 → read (emem t) Aligned p U8 = read (emem t') Aligned p U8.
  Proof.
    move => h; elim: h xs s t => {vs vs'}.
    - case => // ?? [] -> [] -> _ _; reflexivity.
    move => v v' vs vs' v_v' vs_vs' ih [] // x xs s t /=.
    apply: rbindP => s1 ok_s1 ok_s' ok_t' E X M.
    have [ vm ok_vm X' ] := write_uincl X v_v' ok_s1.
    have [ m' ok_t1 M' ] := match_mem_gen_write_lval M ok_vm.
    move: ok_t'.
    rewrite (surj_estate t) -E ok_t1 /= => ok_t'.
    move=> pr hnvalid.
    rewrite (write_lval_mem_unchanged ok_s1 ok_t1 erefl X M) //=.
    apply (ih _ _ _ ok_s' ok_t' erefl X' M').
    by rewrite -(write_lval_validw ok_vm).
  Qed.

  Lemma preserved_metadata_write_lvals xs vs vs' s s' t t' sp :
    List.Forall2 value_uincl vs vs' →
    write_lvals true [::] s xs vs = ok s' →
    write_lvals true [::] t xs vs' = ok t' →
    escs s = escs t →
    vm_uincl s t →
    match_mem_gen sp s t →
    preserved_metadata (emem s) (emem t) (emem t').
  Proof.
    move=> U ok_s' ok_t' E X M pr _.
    exact: (write_lvals_mem_unchanged U ok_s' ok_t' E X M).
  Qed.

  Lemma preserved_metadata_alloc m al sz ioff sz' m' m1 m2 :
    alloc_stack m al sz ioff sz' = ok m' →
    preserved_metadata m' m1 m2 →
    preserved_metadata m m1 m2.
  Proof.
    move => ok_m' h a [] a_lo a_hi /negbTE a_not_valid.
    have A := alloc_stackP ok_m'.
    have ? := ass_add_ioff A.
    have [_ top_goes_down ] := ass_above_limit A.
    apply: h.
    - split; last by rewrite A.(ass_root).
      apply: Z.le_trans a_lo.
      etransitivity; last apply: top_goes_down.
      by have := A.(ass_ioff); lia.
    rewrite A.(ass_valid) a_not_valid /= !zify.
    change (wsize_size U8) with 1%Z.
    lia.
  Qed.

  Section STACK.

  Context
    (m0 : mem) (* the *initial* source memory, including glob *)
    (sp0 : pointer) (* the end of the stack frame of the export function *)
    (max0 : Z). (* the max size of the stack of the export function
                   (including the frames of the callees) *)
    Context (sp0_le : (wunsigned sp0 <= wunsigned (top_stack m0))%Z).

  (* We have at least [max0] space on the stack. *)
  Hypothesis enough_space : (0 <= max0 <= wunsigned sp0)%Z.

  Lemma no_overflow_max0 : no_overflow (sp0 - wrepr _ max0) max0.
  Proof.
    have ? := wunsigned_range sp0.
    by rewrite /no_overflow zify wunsigned_sub; lia.
  Qed.

  (* Valid memory is either valid in the source or on the stack *)
  Definition source_mem_split m sp :=
    forall p, validw m Aligned p U8 -> validw m0 Aligned p U8 || pointer_range sp sp0 p.

  (* The end of the stack frame after allocating + aligning *)
  Definition align_top sp ws sz :=
    (top_stack_after_alloc sp ws sz + wrepr _ sz)%R.

  Definition align_top_stack top e :=
    align_top top e.(sf_align) (e.(sf_stk_sz) + e.(sf_stk_extra_sz)).

  (* One interesting property of [align_top] is that, if [sz] is [ws]-aligned,
     it is the same as just performing a [ws]-alignment. *)
  Lemma align_top_aligned top ws sz :
    (0 <= sz)%Z ->
    (0 <= wunsigned top - sz < wbase Uptr)%Z ->
    is_align sz ws ->
    align_top top ws sz = align_word ws top.
  Proof.
    move=> hpos hb hal.
    rewrite /align_top /top_stack_after_alloc.
    apply wunsigned_inj.
    rewrite wunsigned_add; last first.
    + have := align_word_range ws (top + wrepr Uptr (- sz)).
      rewrite wrepr_opp wunsigned_sub //.
      have := wunsigned_range top.
      have := wunsigned_range (align_word ws (top - wrepr Uptr sz)).
      by lia.
    rewrite !align_wordE wrepr_opp wunsigned_sub //.
    rewrite Zminus_mod.
    move/eqP: hal; rewrite WArray.p_to_zE => ->.
    rewrite Z.sub_0_r Zmod_mod.
    by lia.
  Qed.

  (* If [fn] is the export function, [sp0] is [sp] after allocating + aligning.
     Otherwise, we know only that [sp] is smaller than [sp0]. *)
  Definition max_bound fn (sp:pointer) :=
    forall fd, get_fundef p.(p_funcs) fn = Some fd ->
    let max := fd.(f_extra).(sf_stk_max) in
    (max <= max0)%Z /\
    (if is_RAnone fd.(f_extra).(sf_return_address) then
      sp0 = align_top_stack sp fd.(f_extra)
    else (0 <= wunsigned sp0 - wunsigned sp)%Z) /\
    (wunsigned sp0 - wunsigned sp <= max0 - max)%Z.

  Definition max_bound_sub fn (sp:pointer) :=
    forall fd, get_fundef p.(p_funcs) fn = Some fd ->
    let max := (fd.(f_extra).(sf_stk_max) - frame_size fd.(f_extra))%Z in
    (0 <= wunsigned sp0 - wunsigned sp <= max0 - max)%Z.

  (* The memory that is both not valid in the source and not in the stack
      is unmodified. This is needed to prove the pass zeroing the stack. *)
  Definition target_mem_unchanged m m' :=
    forall p, ~ validw m0 Aligned p U8 -> ~ pointer_range (sp0 - wrepr _ max0) sp0 p ->
    read m Aligned p U8 = read m' Aligned p U8.

  Instance target_mem_unchanged_equiv : Equivalence target_mem_unchanged.
  Proof.
    split; first by [].
    - by move => x y xy ptr hnv hnpr; rewrite xy.
    move => x y z xy yz ptr hnv pr.
    by rewrite xy; first exact: yz.
  Qed.


Context {E E0: Type -> Type} {wE: with_Error E E0} {rndE0 : RndEvent syscall_state -< E0}.

Section ILSTEPS_END.

Context (fn:funname).

Notation post P lc :=
  (fun ls1 ls2 => [/\ ls1 = ls2, lfn ls1 = fn & lpc ls1 = size (P:lcmd) + size (lc:lcmd)]).

Definition pre_i i lbl lbli P li Q :=
  [/\ checked_i fn i
    , linear_i fn i lbl [::] = (lbli, li)
    , disjoint_labels lbl lbli P
    & is_linear_of fn (P ++ li ++ Q) ].

Definition pre_c c lbl lblc P lc Q :=
  [/\ checked_c fn c
    , linear_c fn c lbl [::] = (lblc, lc)
    , disjoint_labels lbl lblc P
    & is_linear_of fn (P ++ lc ++ Q) ].

Let Pi (i:instr) :=
  ∀ lbl lbli li P Q ls,
    pre_i i lbl lbli P li Q →
    lfn ls = fn → lpc ls = size P →
    eutt (post P li)
       (mix_ilsteps p' (pc_between_c fn P li) ls)
       (mix_ilsteps p' (pc_between_c fn P li) ls).

Let Pi_r (i:instr_r) := forall ii, Pi (MkI ii i).

Let Pc (c:cmd) :=
  ∀ lbl lblc lc P Q ls,
    pre_c c lbl lblc P lc Q →
    lfn ls = fn → lpc ls = size P →
    eutt (post P lc)
       (mix_ilsteps p' (pc_between_c fn P lc) ls)
       (mix_ilsteps p' (pc_between_c fn P lc) ls).
Import ITreeNotations.

Lemma linear_c_end_dfl ls (P:lcmd) :
  lfn ls = fn →
  lpc ls = size P →
  eutt (post P [::]) (mix_ilsteps p' (pc_between_c fn P [::]) ls) (mix_ilsteps p' (pc_between_c fn P [::]) ls).
Proof.
  move=> hfn hpc;  rewrite mix_ilsteps_b0 //; last by rewrite addn0.
  by apply eutt_Ret; rewrite addn0.
Qed.

Lemma linear_c_end_nil : Pc nil.
Proof. by move=> > [/= _ [? <-]] *; apply linear_c_end_dfl. Qed.

Lemma pre_c_cons_aux i c :
  Pi i → Pc c →
  ∀ lbl lblic lic P Q ls,
  pre_c (i :: c) lbl lblic P lic Q →
  lfn ls = fn → lpc ls = size P →
  exists lbli lblc li lc,
    [/\ lblic = lbli
      , lic = li ++ lc
      , pre_i i lblc lbli P li (lc ++ Q)
      , pre_c c lbl lblc (P ++ li) lc Q
      & mix_ilsteps p' (pc_between_c fn P lic) ls ≈
         ls' <- mix_ilsteps p' (pc_between_c fn P li) ls ;;
         mix_ilsteps p' (pc_between_c fn (P ++ li) lc) ls'].
Proof.
  move=> hi hc lbl lblic lic P Q ls [] /=.
  case heqc: (linear_c fn) (valid_c fn c lbl) => [lblc lc] [Lc Vc].
  rewrite linear_i_nil.
  case heqi: linear_i (valid_i fn i lblc) => [lbli li] [Li Vi] /= /checked_cI [??] [??] D. subst lblic lic.
  rewrite -!catA => C hfn hpc.
  exists lbli, lblc, li, lc.
  have [pi pc] : pre_i i lblc lbli P li (lc ++ Q) /\ pre_c c lbl lblc (P ++ li) lc Q.
  + rewrite /pre_i /pre_c -!catA; split => //; split => //.
    + apply: (disjoint_labels_wL _ D); exact: Lc.
    apply: disjoint_labels_cat.
    * apply: (disjoint_labels_wH _ D); exact: Li.
    apply: (valid_disjoint_labels Vi); lia.
  split => //.
  rewrite (mix_ilsteps_split_c p' (P' := P) (Q' := li)) //; last by simpl_size; lia.
  apply eqit_bind' with (post P li) => //.
  + by apply: hi pi hfn hpc.
  move=> ls' _ [<- hfn' hpc'].
  rewrite (mix_ilsteps_split_c p' (P' := P ++ li) (Q' := lc)) //; [| by simpl_size; lia ..].
  rewrite -{2} (bind_ret_r (mix_ilsteps _ _ _)).
  apply eqit_bind' with (post (P ++ li) lc) => //.
  + by have := hc _ _ _ _ _ _ pc hfn'; rewrite size_cat => /(_ hpc'); apply.
  move=> ls'' _ [<- ? hpc''].
  rewrite mix_ilsteps_b0 => //; last by rewrite hpc''; simpl_size; lia.
  by apply eqit_Ret.
Qed.

Lemma linear_c_end_cons : ∀ (i : instr) (c : cmd), Pi i → Pc c → Pc (i :: c).
Proof.
  move=> i c hi hc lbl lblic lic P Q ls hpre hfn hpc.
  have := pre_c_cons_aux hi hc hpre hfn hpc.
  move=> [lbli] [lblc] [li] [lc] [?? pi pc ->]; subst lblic lic.
  apply eqit_bind' with (post P li).
  + by apply: hi pi hfn hpc.
  move=> ls' _ [<- hfn' hpc'].
  have := hc _ _ _ _ _ _ pc hfn'; rewrite !size_cat addnA => /(_ hpc'); apply.
Qed.

Lemma linear_c_end_assgn : ∀ (x : lval) (tg : assgn_tag) (ty : atype) (e : pexpr), Pi_r (Cassgn x tg ty e).
Proof. by move=> > [] /checked_iE []. Qed.

Lemma linear_c_end_opn : ∀ (xs : lvals) (t : assgn_tag) (o : sopn) (es : pexprs), Pi_r (Copn xs t o es).
Proof.
  move=> xs t o es ii lbl lbli li P Q ls [_] /=.
  case: oseq.omap; last by move=> [? <-] *; apply linear_c_end_dfl.
  move=> lxs; case: oseq.omap; last by move=> [? <-] *; apply linear_c_end_dfl.
  move=> les [<- <-] D C hfn hpc.
  rewrite (step_mix_ilsteps C) //; last by simpl_size; lia.
  rewrite /eval_instr /=.
  case: sem_rexprs => [vs /= | ?]; last by apply eqit_Vis => -[].
  case: exec_sopn => [vs' /= | ?]; last by apply eqit_Vis => -[].
  case: write_lexprs => [s' /= | ?]; last by apply eqit_Vis => -[].
  rewrite mix_ilsteps_b0 => //=; last by rewrite hpc addn1.
  by apply eqit_Ret; split => //=; rewrite hpc addn1.
Qed.

Lemma eq_lsyscall o s :
  eutt
    (fun s1' s2' => [/\ s1' = s2', lfn s1' = lfn s & lpc s1' = (lpc s).+1 ])
    (lexec_syscall (E:=mix_to_small_steps.CallE funname lstate +' E) o s) (lexec_syscall (E:=mix_to_small_steps.CallE funname lstate +' E) o s).
Proof.
apply: eutt_eq_bind => vs /=; apply: eutt_eq_bind => fs.
apply: (eutt_clo_bind _ (UU := fun s1' s2' => [/\ s1' = s2', lfn s1' = lfn s & lpc s1' = lpc s ])).
- rewrite /lset_fstate; case: upd_estate => [s0|e] /=; first by apply eutt_Ret.
  by apply: eqit_Vis.
move=> s' _ [<- <- <-]; by apply eutt_Ret.
Qed.

Lemma linear_c_end_syscall : ∀ (xs : lvals) (o : syscall_t) (es : pexprs), Pi_r (Csyscall xs o es).
Proof.
  move=> xs o es ii lbl lbli li P Q ls [_] /= [<- <-] D C hfn hpc.
  rewrite (step_mix_ilsteps C) //=; last by simpl_size; lia.
  apply: eutt_clo_bind; first exact: eq_lsyscall.
  move=> s' _ [<- hfn' hpc'].
  rewrite -{}hfn' in hfn.
  rewrite {}hpc in hpc'.
  rewrite tau_eutt.
  rewrite mix_ilsteps_b0 //; last by rewrite addn1.
  by apply eqit_Ret; split => //=; rewrite addn1.
Qed.

Lemma linear_c_end_assert : ∀ a : assertion, Pi_r (Cassert a).
Proof. by move=> > [] /checked_iE []. Qed.

Lemma pre_c_nil fd P li Q lbl :
  get_fundef (p_funcs p) fn = Some fd ->
  is_linear_of fn (P ++ li ++ Q) ->
  pre_c [::] lbl lbl (P ++ li) [::] Q.
Proof.
  move=> ok_fd C; split => //.
  + by rewrite /checked_c ok_fd.
  + rewrite /disjoint_labels; lia.
  by rewrite -catA.
Qed.

Lemma check_bool_sem_fexpr vm e v :
  check_bool e ->
  sem_fexpr vm e = ok v ->
  exists b, v = Vbool b.
Proof.
  case: e => //=.
  + move=> x /eqP hty hget.
    have := type_of_get_var hget; rewrite hty /= => /subctypeE.
    move=> /type_of_valI [hundef | ].
    + by have {hget} /(_ cbool erefl):= get_var_undef hget.
    by move=> [b ->]; exists b.
  + move=> o1 e1 hty.
    have {}hty : (type_of_op1 o1).2 = abool.
    + by case: o1 hty => // > /eqP.
    t_xrbindP => v1 _ /sem_sop1I [_] [+] [_ _ ->].
    by rewrite hty => b; exists b.
  + move=> o2 e1 e2 hty.
    have {}hty : (type_of_op2 o2).2 = abool.
    + by case: o2 hty => // > /eqP.
    t_xrbindP => v1 _ v2 _ /sem_sop2I [?] [?] [+] [_ _ _ ->].
    by rewrite hty => b; exists b.
  move=> > _; t_xrbindP => *; subst; case: ifP => _; eexists; reflexivity.
Qed.

Lemma sem_fexpr_snot vm e :
  check_bool e ->
  sem_fexpr vm (fnot e) = sem_fexpr vm (Fapp1 Onot e).
Proof.
  elim e => //=.
  + move=> o1 e1 _.
    case: o1 => // hch1.
    case heq1 : sem_fexpr => [v1 |] //=.
    have [b ->] := check_bool_sem_fexpr hch1 heq1.
    by rewrite /sem_sop1 /= negbK.
  + move=> o2 e1 he1 e2 he2.
    case: o2 => //=.
    + move=> /andP [hch1 hch2]; rewrite he1 // he2 // /sem_sop1 /sem_sop2 /=.
      case heq1 : (sem_fexpr _ e1) => [v1 |] //=.
      have [b1 -> /=] := check_bool_sem_fexpr hch1 heq1.
      case heq2 : sem_fexpr => [v2 |] //=.
      have [b2 -> /=] := check_bool_sem_fexpr hch2 heq2.
      by rewrite negb_and.
    move=> /andP [hch1 hch2]; rewrite he1 // he2 // /sem_sop1 /sem_sop2 /=.
    case heq1 : (sem_fexpr _ e1) => [v1 |] //=.
    have [b1 -> /=] := check_bool_sem_fexpr hch1 heq1.
    case heq2 : sem_fexpr => [v2 |] //=.
    have [b2 -> /=] := check_bool_sem_fexpr hch2 heq2.
    by rewrite negb_or.
  move=> e0 _ e1 he1 e2 he2 /andP [hch1 hch2].
  rewrite he1 // he2 // /sem_sop1 /=.
  case: (Let _ := sem_fexpr _ e0 in _) => //= b0.
  case: (sem_fexpr _ e1) => //= v1.
  case: (to_bool v1) => //= b1.
  case: (sem_fexpr _ e2) => //= v2.
  case: (to_bool v2) => //= b2.
  by case: b0.
Qed.

(* TODO: move ? *)
Remark next_lbl_neq (lbl: label) :
  ((lbl + 1)%positive == lbl) = false.
Proof.
  clear.
  apply/eqP => k.
  suff : (lbl < lbl)%positive by lia.
  rewrite -{2}k; lia.
Qed.

Notation Lilabel := (linear.Llabel InternalLabel).

Lemma pre_i_if_aux e c1 c2 :
  Pc c1 → Pc c2 →
  ∀ ii lbl lbli li P Q ls,
  pre_i (MkI ii (Cif e c1 c2)) lbl lbli P li Q →
  lfn ls = fn → lpc ls = size P →
  exists lbl1 lblc1 lc1 P1 Q1 lbl2 lblc2 lc2 P2 Q2,
    [/\ check_fexpr ii e = ok tt
      , pre_c c1 lbl1 lblc1 P1 lc1 Q1
      , pre_c c2 lbl2 lblc2 P2 lc2 Q2
      & mix_ilsteps p' (pc_between_c fn P li) ls ≈
        match (Let v := sem_fexpr (lvm ls) (to_fexpr e) in to_bool v) with
        | Ok b =>
          ls' <- (if b then mix_ilsteps p' (pc_between_c fn P1 lc1) (setcpc ls fn (size P1))
                  else mix_ilsteps p' (pc_between_c fn P2 lc2) (setcpc ls fn (size P2)));;
          Ret (setcpc ls' fn (size P + size li))
        | Error e0 => Exception.throw (e0, tt)
        end].
Proof.
  move=> ih1 ih2 ii lbl lbli li P Q ls [/checked_iE [fd ok_fd] /=].
  t_xrbindP => chk_b chk_e chk_c1 chk_c2.
  case: c1 ih1 chk_c1.
  + move=> _ _.
    rewrite linear_c_nil.
    case heq2: (linear_c fn) (valid_c fn c2 (next_lbl lbl)) (ih2 (next_lbl lbl)) => [lbl2 lc2] [L2 V2] {}ih2.
    set licond := {| li_i := Lcond _ _; |}.
    set lilabel := {| li_i := Lilabel _; |}.
    set P2 := rcons P licond; set Q2 := lilabel :: Q.
    move=> [??] D C hfn hpc.
    exists lbl, lbl, [::], (P++li), Q, (next_lbl lbl), lbl2, lc2, P2, Q2.
    subst lbli li.
    have pre1 := pre_c_nil lbl ok_fd C.
    have D2 : disjoint_labels (next_lbl lbl) lbl2 P2.
    + rewrite /P2 -cats1; apply: disjoint_labels_cat; last by [].
      apply: disjoint_labels_wL _ D; rewrite /next_lbl; lia.
    have C2 : is_linear_of fn (P2 ++ lc2 ++ Q2).
    + by move: C; rewrite /P2 /Q2 -cats1 -!catA /= -catA.
    have pre2 : pre_c c2 (next_lbl lbl) lbl2 P2 lc2 Q2.
    + split => //.
      by rewrite /checked_c ok_fd chk_c2.
    split => //.
    rewrite (step_mix_ilsteps C) /eval_instr //=; last by simpl_size; lia.
    case: (Let x := sem_fexpr (lvm ls) (to_fexpr e) in to_bool x) => [b | err] /=; last reflexivity.
    case: b.
    + rewrite hfn (eval_jumpE C).
      rewrite find_label_cat_hd; last by apply: D; move:L2; rewrite /next_lbl; lia.
      rewrite find_labelE /= -catA find_label_cat_hd; last first.
      * apply: (valid_has_not_label V2); left; rewrite /next_lbl; lia.
      rewrite /= find_labelE /is_label /= eqxx /= /setcpc /= addn0.
      rewrite mix_ilsteps_b0 //=; last by simpl_size; lia.
      rewrite mix_ilsteps_b0 //=; last by simpl_size; lia.
      by rewrite bind_ret_l /=; apply eqit_Ret; f_equal; simpl_size; f_equal; lia.
    rewrite (mix_ilsteps_split p' (pcs' := size P2) (pce' := size P2 + size lc2)) //; [| simpl_size; lia ..].
    apply eqit_bind' with (post P2 lc2).
    + have -> : lnext_pc ls = setcpc ls fn (size P2).
      + by rewrite /lnext_pc /setcpc /P2 hfn hpc /= size_rcons.
      by apply (ih2 _ _ _ _ _ pre2).
    move=> ls' _ [<- hfn' hpc'].
    rewrite catA in C2.
    rewrite (step_mix_ilsteps C2) /eval_instr //=; [| rewrite /P2 ?hpc'; simpl_size; lia ..].
    rewrite mix_ilsteps_b0 => //; last first.
    + rewrite /lnext_pc /= hpc'; simpl_size; lia.
    apply eqit_Ret.
    by rewrite /lnext_pc /setcpc /= hpc' /P2 ; f_equal => //; simpl_size; lia.
  move=> i1 c1;move: (i1::c1) => {}c1 ih1 chk_c1.
  case: c2 ih2 chk_b chk_c2.
  + move=> _ chk_b _.
    rewrite linear_c_nil.
    case heq1: (linear_c fn) (valid_c fn c1 (next_lbl lbl)) (ih1 (next_lbl lbl)) => [lbl1 lc1] [L1 V1] {}ih1.
    set licond := {| li_i := Lcond _ _; |}.
    set lilabel := {| li_i := Lilabel _; |}.
    set P1 := rcons P licond; set Q1 := lilabel :: Q.
    move=> [??] D C hfn hpc.
    exists (next_lbl lbl), lbl1, lc1, P1, Q1, lbl, lbl, [::], (P++li), Q.
    subst lbli li.
    have D1 : disjoint_labels (next_lbl lbl) lbl1 P1.
    + rewrite /P1 -cats1; apply: disjoint_labels_cat; last by [].
      apply: disjoint_labels_wL _ D; rewrite /next_lbl; lia.
    have C1 : is_linear_of fn (P1 ++ lc1 ++ Q1).
    + by move: C; rewrite /P1 /Q1 -cats1 -!catA /= -catA.
    have pre1 : pre_c c1 (next_lbl lbl) lbl1 P1 lc1 Q1.
    + split => //.
      by rewrite /checked_c ok_fd chk_c1.
    have pre2 := pre_c_nil lbl ok_fd C.
    split => //.
    rewrite (step_mix_ilsteps C) /eval_instr //=; last by simpl_size; lia.
    rewrite sem_fexpr_snot //= /sem_sop1 /=.
    case: sem_fexpr => [v | ?] /=; last reflexivity.
    case: to_bool => [b | ?] /=; last reflexivity.
    case: b => /=.
    + rewrite (mix_ilsteps_split p' (pcs' := size P1) (pce' := size P1 + size lc1)) //; [| simpl_size; lia ..].
      apply eqit_bind' with (post P1 lc1).
      + have -> : lnext_pc ls = setcpc ls fn (size P1).
        + by rewrite /lnext_pc /setcpc /P1 hfn hpc /= size_rcons.
        by apply (ih1 _ _ _ _ _ pre1).
      move=> ls' _ [<- hfn' hpc'].
      rewrite catA in C1.
      rewrite (step_mix_ilsteps C1) /eval_instr //=; [| rewrite /P1 ?hpc'; simpl_size; lia ..].
      rewrite mix_ilsteps_b0 => //; last first.
      + rewrite /lnext_pc /= hpc'; simpl_size; lia.
      apply eqit_Ret.
      by rewrite /lnext_pc /setcpc /= hpc' /P1 ; f_equal => //; simpl_size; lia.
    rewrite hfn (eval_jumpE C).
    rewrite find_label_cat_hd; last by apply: D; move:L1; rewrite /next_lbl; lia.
    rewrite find_labelE /= -catA find_label_cat_hd; last first.
    * apply: (valid_has_not_label V1); left; rewrite /next_lbl; lia.
    rewrite /= find_labelE /is_label /= eqxx /= /setcpc /= addn0.
    rewrite mix_ilsteps_b0 //=; last by simpl_size; lia.
    rewrite mix_ilsteps_b0 //=; last by simpl_size; lia.
    by rewrite bind_ret_l /=; apply eqit_Ret; f_equal; simpl_size; f_equal; lia.

  move=> i c2; move: (i::c2) => {i}c2 ih2 _ chk_c2.
  rewrite linear_c_nil.
  case heq1: (linear_c fn) (valid_c fn c1 (next_lbl (next_lbl lbl))) (ih1 (next_lbl (next_lbl lbl))) => [lbl1 lc1].
  rewrite /next_lbl => -[L V] {}ih1.
  rewrite linear_c_nil.
  case heq2: (linear_c fn) (valid_c fn c2 lbl1) (ih2 lbl1) => [lbl2 lc2] [L2 V2] {}ih2.
  set licond := {| li_i := Lcond _ _; |}.
  set ligoto := {| li_i := Lgoto _; |}.
  set lilabel := {| li_i := Lilabel _; |}.
  set lilabel' := {| li_i := Lilabel _; |}.
  set P1 := P ++ licond :: lc2 ++ [:: ligoto; lilabel ].
  set Q1 := lilabel' :: Q.
  set P2 := rcons P licond.
  set Q2 := [:: ligoto, lilabel & lc1] ++ Q1.
  move=> [??] D C hfn hpc; subst li lbli.
  have D1 : disjoint_labels (lbl + 1 + 1) lbl1 P1.
  + apply: disjoint_labels_cat; first by apply: disjoint_labels_w _ _ D; lia.
    apply: disjoint_labels_cat; first by apply: (valid_disjoint_labels V2); lia.
    by move => lbl' [A B]; rewrite /= orbF /is_label /=; apply/eqP => ?; subst lbl'; lia.
  have C1 : is_linear_of fn (P1 ++ lc1 ++ Q1).
  + by move: C; rewrite /P1 /Q1 /= -!catA /= -!catA.
  have pre1 : pre_c c1 (lbl + 1 + 1) lbl1 P1 lc1 Q1.
  + by split => //; rewrite /checked_c ok_fd chk_c1.
  have D2 : disjoint_labels lbl1 lbl2 P2.
  + rewrite /P2 -cats1; apply: disjoint_labels_cat; last by [].
    apply: disjoint_labels_wL _ D; lia.
  have C2 : is_linear_of fn (P2 ++ lc2 ++ Q2).
  + by move: C; rewrite /P2 /Q2 /= -cats1 -!catA /= -!catA.
  have pre2 : pre_c c2 lbl1 lbl2 P2 lc2 Q2.
  + by split => //; rewrite /checked_c ok_fd chk_c2.
  exists (lbl + 1 + 1)%positive, lbl1, lc1, P1, Q1, lbl1, lbl2, lc2, P2, Q2; split => //.
  rewrite (step_mix_ilsteps C) //; last by simpl_size; lia.
  rewrite /eval_instr /=.
  case: (Let _ := sem_fexpr _ _ in _) => [b | ?] /=; last by reflexivity.
  rewrite hfn (eval_jumpE C).
  rewrite find_label_cat_hd; last by apply: D; lia.
  rewrite find_labelE /= -catA find_label_cat_hd; last first.
  * apply: (valid_has_not_label V2); lia.
  rewrite find_labelE /= find_labelE /is_label /= eqxx /=.
  case: b.
  + rewrite (mix_ilsteps_split p' (pcs':=size P1) (pce':=size P1 + size lc1)); [| by rewrite /P1; simpl_size; lia ..].
    apply eqit_bind' with (post P1 lc1).
    + have -> : (size P + (size lc2 + 1).+1).+1 = size P1.
      + rewrite /P1; simpl_size; lia.
      by apply:ih1 => //; apply pre1.
    move=> ls' _ [<- hfn' hpc'].
    have {}C1 : is_linear_of fn ((P1 ++ lc1) ++ [::lilabel'] ++ Q).
    + by move: C1; rewrite /Q1 /= catA.
    rewrite (step_mix_ilsteps C1) //; [| by rewrite ?hpc' /P1; simpl_size; lia ..].
    rewrite /eval_instr /=.
    rewrite mix_ilsteps_b0; last first.
    + by rewrite /lnext_pc /= hpc' /P1; simpl_size; lia.
    + by rewrite /lnext_pc hfn'.
    apply eqit_Ret; rewrite /lnext_pc /setcpc; f_equal => //.
    by rewrite /P1 hpc'; simpl_size; lia.
  rewrite (mix_ilsteps_split p' (pcs':=size P2) (pce':=size P2 + size lc2)); [| by rewrite /P2; simpl_size; lia ..].
  apply eqit_bind' with (post P2 lc2).
  + rewrite /lnext_pc /setcpc.
    have -> : (lpc ls).+1 = size P2.
    + by rewrite /P2 size_rcons hpc.
    by rewrite hfn; apply:ih2 => //; apply pre2.
  move=> ls' _ [<- hfn' hpc'].
  rewrite catA in C2.
  rewrite (step_mix_ilsteps C2) //=; last first.
  + rewrite /P2; simpl_size; lia. + by rewrite size_cat.
  rewrite /eval_instr /= (eval_jumpE C2) /P2 -cats1.
  rewrite -!catA find_label_cat_hd; last by apply: D; lia.
  rewrite find_labelE /= find_label_cat_hd; last by apply: (valid_has_not_label V2); lia.
  rewrite find_labelE /= find_labelE /is_label /= next_lbl_neq.
  rewrite /Q1 find_label_cat_hd; last by apply: (valid_has_not_label V); lia.
  rewrite find_labelE /is_label /= eqxx /=.
  rewrite mix_ilsteps_0; last first.
  + rewrite /pc_between_c /pc_between /= eqxx; simpl_size; lia.
  apply eqit_Ret; rewrite /setcpc; f_equal => //.
  simpl_size; lia.
Qed.

Lemma linear_c_end_if : ∀ (e : pexpr) (c1 c2 : cmd), Pc c1 → Pc c2 → Pi_r (Cif e c1 c2).
Proof.
  move=> e c1 c2 hc1 hc2 ii lbl lbli li P Q ls pre hfn hpc.
  have := pre_i_if_aux hc1 hc2 pre hfn hpc.
  move=> [lbl1] [lblc1] [lc1] [P1] [Q1] [lbl2] [lblc2] [lc2] [P2] [Q2] [_ pre1 pre2 ->].
  case: (Let _ := sem_fexpr _ _ in _) => [b | ?]; last apply eqit_Vis => -[].
  case: b.
  + apply eqit_bind' with (post P1 lc1).
    + by apply: hc1 => //; apply pre1.
    by move=> ls' _ [<- hfn' hpc']; apply eqit_Ret.
  apply eqit_bind' with (post P2 lc2).
  + by apply: hc2 => //; apply pre2.
  by move=> ls' _ [<- hfn' hpc']; apply eqit_Ret.
Qed.

Lemma linear_c_end_for : ∀ (v : var_i) (dir : expr.dir) (lo hi : pexpr) (c0 : cmd), Pc c0 → Pi_r (Cfor v (dir, lo, hi) c0).
Proof. by move=> > ? > [] /checked_iE []. Qed.

Lemma mix_ilsteps_add_align P ii al lc Q ls :
  lfn ls = fn → lpc ls = size P →
  is_linear_of fn (P ++ (add_align ii al [::] ++ lc) ++ Q) →
  mix_ilsteps p' (pc_between_c fn P (add_align ii al [::] ++ lc)) ls ≈
  mix_ilsteps p' (pc_between_c fn P (add_align ii al [::] ++ lc))
        (setcpc ls fn (size P + size (add_align ii al [::]))).
Proof.
  case: al => /= hfn hpc C; last first.
  + by rewrite addn0 -hpc -hfn /setcpc; case: (ls) => /= >; reflexivity.
  rewrite (step_mix_ilsteps C) //=; last by simpl_size;lia.
  rewrite /lnext_pc /setcpc addn1 hfn hpc; reflexivity.
Qed.

Lemma pre_i_while_aux al c1 e iiw c2 :
  Pc c1 → Pc c2 →
  ∀ ii lbl lbli li P Q ls,
  pre_i (MkI ii (Cwhile al c1 e iiw c2)) lbl lbli P li Q →
  lfn ls = fn → lpc ls = size P →
  exists lbl1 lblc1 lc1 P1 Q1 lbl2 lblc2 lc2 P2 Q2,
    [/\ (is_bool e = None -> check_fexpr ii e = ok tt)
      , pre_c c1 lbl1 lblc1 P1 lc1 Q1
      , (is_bool e <> Some false -> pre_c c2 lbl2 lblc2 P2 lc2 Q2)
      & mix_ilsteps p' (pc_between_c fn P li) ls ≈
        ITree.iter (fun ls =>
          ls1 <- mix_ilsteps p' (pc_between_c fn P1 lc1) (setcpc ls fn (size P1));;
          let b := if is_bool e is Some b then ok b
                   else Let v := sem_fexpr (lvm ls1) (to_fexpr e) in to_bool v in
          match b with
          | Ok b =>
            if b then
              (ls2 <- mix_ilsteps p' (pc_between_c fn P2 lc2) (setcpc ls1 fn (size P2));;
               Ret (inl ls2))%itree
            else Ret (inr (setcpc ls1 fn (size P + size li)))
          | Error e0 => Exception.throw (e0, tt)
          end)%itree ls].
Proof.
  move=> ih1 ih2 ii lbl lbli li P Q ls [/checked_iE [fd ok_fd] /=].
  t_xrbindP.
  case: is_boolP => [b | ].
  + case: ifP => hb.
    (* condition is true *)
    + t_xrbindP => chk_c1 chk_c2.
      rewrite linear_c_nil.
      case heq2: (linear_c fn c2) (valid_c fn c2 (next_lbl lbl)) (ih2 (next_lbl lbl)) => [lbl2 lc2].
      rewrite /next_lbl => -[L2 V2] {}ih2.
      rewrite linear_c_nil.
      case heq1: (linear_c fn) (valid_c fn c1 lbl2) (ih1 lbl2) => [lbl1 lc1] [L1 V1] {}ih1.
      rewrite /align add_align_nil /=.
      set ligoto := {| li_i := Lgoto _; |}.
      set lilabel := {| li_i := Lilabel _; |}.
      set lialign := add_align _ _ _.
      set P1 := P ++ lialign ++ [::lilabel]; set P2 := P1 ++ lc1.
      set Q2 := ligoto :: Q; set Q1 := lc2 ++ Q2.
      move=> [??] D C hfn hpc; subst li lbli.
      have D1 : disjoint_labels lbl2 lbl1 P1.
      + apply: disjoint_labels_cat; first by apply: disjoint_labels_w _ _ D; lia.
        apply: disjoint_labels_cat; first by rewrite /lialign; case: (al).
        by move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
      have C1 : is_linear_of fn (P1 ++ lc1 ++ Q1).
      + by move: C; rewrite /P1 /Q1 /Q2 /= -!catA /= -!catA.
      have pre1 : pre_c c1 lbl2 lbl1 P1 lc1 Q1.
      + by split => //; rewrite /checked_c ok_fd chk_c1.
      have D2 : disjoint_labels (lbl + 1) lbl2 P2.
      + rewrite /P2 /P1; apply: disjoint_labels_cat.
        + apply disjoint_labels_cat; first by apply: disjoint_labels_w _ _ D; lia.
          apply: disjoint_labels_cat; first by rewrite /lialign; case: (al).
          by move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
        by apply: (valid_disjoint_labels V1); lia.
      have C2 : is_linear_of fn (P2 ++ lc2 ++ Q2).
      + by move: C; rewrite /P2 /P1 /Q1 /Q2 /= -!catA /= -!catA.
      have pre2 : pre_c c2 (lbl + 1) lbl2 P2 lc2 Q2.
      + by split => //; rewrite /checked_c ok_fd chk_c2.
      exists lbl2, lbl1, lc1, P1, Q1, (lbl + 1)%positive, lbl2, lc2, P2, Q2.
      split => //.
      (* We skip the alignment instruction and the label *)
      rewrite (mix_ilsteps_add_align hfn hpc C).
      have {}C : is_linear_of fn ((P ++ lialign) ++ (lilabel :: lc1 ++ lc2 ++ [:: ligoto]) ++ Q).
      + by move: C; rewrite !catA.
      rewrite -/lialign (step_mix_ilsteps C) //=; [ | by rewrite /lialign; simpl_size;lia..].
      (* Here the proof is done by coinduction *)
      have {}ih1 := ih1 _ _ _ _ _ pre1.
      have {}ih2 := ih2 _ _ _ _ _ pre2.
      move=> {hfn hpc}; move: ls; ginit; gcofix SELF => s.
      rewrite unfold_iter bind_bind.
      rewrite (mix_ilsteps_split p' (pcs':=size P1) (pce':=size P1 + size lc1));[| rewrite /P1; simpl_size; lia..].
      guclo eqit_clo_bind.
      econstructor.
      + have -> : lnext_pc (setcpc s fn (size P + size lialign)) = setcpc s fn (size P1).
        + rewrite /lnext_pc /setcpc /P1 /=; f_equal; simpl_size; lia.
        by apply ih1.
      move=> ls1 _ [<- hfn1 hpc1]; rewrite bind_bind.
      rewrite (mix_ilsteps_split p' (pcs':=size P2) (pce':=size P2 + size lc2));[| rewrite /P2; simpl_size; lia..].
      guclo eqit_clo_bind.
      econstructor.
      + have -> : ls1 = (setcpc ls1 fn (size P2)).
        + rewrite /setcpc /P2 /P1 /=. case: ls1 hfn1 hpc1 => /= > -> ->.
          f_equal; simpl_size; lia.
        by apply ih2.
      move=> ls2 _ [<- hfn2 hpc2]; rewrite bind_ret_l.
      rewrite catA in C2.
      rewrite (step_mix_ilsteps_eq_itree C2) //=; [|rewrite /P2/P1 ?hpc2; simpl_size; lia..].
      rewrite /eval_instr /= (eval_jumpE C).
      rewrite find_label_cat_hd; last first.
      + apply: (disjoint_labels_cat D); rewrite /lialign; case: (al) => //; lia.
      rewrite find_labelE /lilabel /is_label /= eqxx /=.
      gstep; constructor; gfinal; left.
      have -> : setcpc ls2 fn (size (P ++ lialign) + 0).+1 =
                lnext_pc (setcpc ls2 fn (size P + size lialign)).
      + rewrite /setcpc /lnext_pc /=; f_equal; simpl_size; lia.
      by apply SELF.
    (* condition is false *)
    move=> chk_c1.
    rewrite linear_c_nil.
    case heq1: (linear_c fn) (valid_c fn c1 lbl) (ih1 lbl) => [lbl1 lc1] [L1 V1] {}ih1.
    set P1 := P; set P2 := P1 ++ lc1.
    set Q2 := Q; set Q1 := Q.
    move=> [??] D C hfn hpc; subst li lbli.
    have D1 : disjoint_labels lbl lbl1 P1.
    + apply: disjoint_labels_w _ _ D; lia.
    have C1 : is_linear_of fn (P1 ++ lc1 ++ Q1).
    + by move: C; rewrite /P1 /Q1 /= cats0.
    have pre1 : pre_c c1 lbl lbl1 P1 lc1 Q1.
    + by split => //; rewrite /checked_c ok_fd chk_c1.
    have D2 : disjoint_labels lbl1 lbl1 P2 by move=> ?; lia.
    have C2 : is_linear_of fn (P2 ++ [::] ++ Q2).
    + by move: C; rewrite /P2 /P1 /Q2 /= -!catA.
    have pre2 : Some false ≠ Some false → pre_c c2 lbl1 lbl1 P2 [::] Q2 by done.
    exists lbl, lbl1, lc1, P1, Q1, lbl1, lbl1, [::], P2, Q2.
    split => //. rewrite unfold_iter bind_bind.
    rewrite (mix_ilsteps_split_c p' (P':=P1) (Q':=lc1));[| rewrite /P1; simpl_size; lia..].
    apply eqit_bind' with (post P lc1).
    + have -> : ls = (setcpc ls fn (size P1)).
      + rewrite /setcpc /P1 /=. case: ls hfn hpc => /= > -> ->.
        f_equal; simpl_size; lia.
      by apply (ih1 _ _ _ _ _ pre1).
    move=> ls1 _ [<- hfn1 hpc1]; rewrite bind_ret_l.
    rewrite cats0 mix_ilsteps_b0 //; apply eqit_Ret.
    by rewrite /setcpc /P1 /=; case: ls1 hfn1 hpc1 => /= > -> ->; f_equal.

  t_xrbindP => {}e chk_e chk_c1 chk_c2.
  case: c2 ih2 chk_c2.
  (* The condition is not a know boolean but c2 is empty *)
  + move=> _ chk_c2.
    rewrite linear_c_nil.
    case heq1: (linear_c fn) (valid_c fn c1 (lbl + 1)) (ih1 (lbl + 1)%positive) => [lbl1 lc1] [L1 V1] {}ih1.
    rewrite /align add_align_nil /=.
    set lilabel := {| li_i := Lilabel _; |}.
    set lialign := add_align _ _ _.
    set licond  := {| li_i := Lcond _ _; |}.
    set P1 := P ++ lialign ++ [::lilabel]; set Q1 := [::licond] ++ Q.
    set P2 := P1 ++ lc1 ++ [::licond]; set Q2 := Q.
    move=> [??] D C hfn hpc; subst li lbli.
    have D1 : disjoint_labels (lbl + 1) lbl1 P1.
    + apply: disjoint_labels_cat; first by apply: disjoint_labels_w _ _ D; lia.
      apply: disjoint_labels_cat; first by rewrite /lialign; case: (al).
      by move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
    have C1 : is_linear_of fn (P1 ++ lc1 ++ Q1).
    + by move: C; rewrite /P1 /Q1 /= -!catA /= -!catA.
    have pre1 : pre_c c1 (lbl + 1) lbl1 P1 lc1 Q1.
    + by split => //; rewrite /checked_c ok_fd chk_c1.
    have D2 : disjoint_labels lbl1 lbl1 P2 by move=> ?; lia.
    have C2 : is_linear_of fn (P2 ++ [::] ++ Q2).
    + by move: C; rewrite /P2 /P1 /Q2 /= -!catA /= -!catA.
    have pre2 : pre_c [::] lbl1 lbl1 P2 [::] Q2.
    + by split => //; rewrite /checked_c ok_fd chk_c2.
    exists (lbl + 1)%positive, lbl1, lc1, P1, Q1, lbl1, lbl1, [::], P2, Q2.
    split => //.
    (* We skip the alignment instruction and the label *)
    rewrite (mix_ilsteps_add_align hfn hpc C).
    have {}C : is_linear_of fn ((P ++ lialign) ++ (lilabel :: lc1 ++ Q1)).
    + by move: C; rewrite /Q1 -!catA /= -catA.
    rewrite -/lialign (step_mix_ilsteps C) //=; [ | by rewrite /lialign; simpl_size;lia..].
    (* Here the proof is done by coinduction *)
    have {}ih1 := ih1 _ _ _ _ _ pre1.
    move=> {hfn hpc}; move: ls; ginit; gcofix SELF => s.
    rewrite unfold_iter bind_bind.
    rewrite (mix_ilsteps_split p' (pcs':=size P1) (pce':=size P1 + size lc1));[| rewrite /P1; simpl_size; lia..].
    guclo eqit_clo_bind.
    econstructor.
    + have -> : lnext_pc (setcpc s fn (size P + size lialign)) = setcpc s fn (size P1).
      + rewrite /lnext_pc /setcpc /P1 /=; f_equal; simpl_size; lia.
      by apply ih1.
    move=> ls1 _ [<- hfn1 hpc1].
    rewrite catA in C1.
    rewrite (step_mix_ilsteps_eq_itree C1) //=; [|rewrite /P1 ?hpc1; simpl_size; lia..].
    rewrite /eval_instr /=.
    case: (Let v := sem_fexpr _ _ in to_bool v) => [b | err] /=; last first.
    + rewrite bind_throw; apply gpaco2_mon with bot2 bot2 => //.
      gfinal; right; rewrite -/(eqit eq true true); reflexivity.
    rewrite hfn1 (eval_jumpE C).
    rewrite find_label_cat_hd; last first.
    + apply: (disjoint_labels_cat D); rewrite /lialign; case: (al) => //; lia.
    rewrite find_labelE /lilabel /is_label /= eqxx /=.
    case: b.
    + rewrite bind_bind (mix_ilsteps_b0 p' (size P2)) //; last first.
      + by rewrite /setcpc /=; simpl_size;lia.
      rewrite !bind_ret_l; gstep; constructor; gfinal; left.
      have -> : setcpc ls1 fn (size (P ++ lialign) + 0).+1 =
                lnext_pc (setcpc (setcpc ls1 fn (size P2)) fn (size P + size lialign)).
      + rewrite /setcpc /lnext_pc /P2 /=; f_equal; simpl_size; lia.
      apply SELF.
    rewrite bind_ret_l mix_ilsteps_b0 //; last first.
    + by rewrite /lnext_pc hpc1 /P1 /=;simpl_size;lia.
    setoid_rewrite tau_euttge; gstep; constructor.
    by rewrite /lnext_pc /setcpc hpc1 /P1 /=; f_equal => //; simpl_size; lia.

  (* The general case *)
  move=> i2 c2; move: (i2::c2) => {}c2 ih2 chk_c2.
  rewrite linear_c_nil /next_lbl.
  case heq1: (linear_c fn) (valid_c fn c1 (lbl + 1 + 1)) (ih1 (lbl + 1 + 1)%positive) => [lbl1 lc1] [L1 V1] {}ih1.
  rewrite linear_c_nil.
  case heq2: (linear_c fn c2) (valid_c fn c2 lbl1) (ih2 lbl1) => [lbl2 lc2] -[L2 V2] {}ih2.
  rewrite /align add_align_nil /=.
  set ligoto := {| li_i := Lgoto _; |}.
  set lilabel1 := {| li_i := Lilabel _; |}.
  set lilabel := {| li_i := Lilabel _; |}.
  set lialign := add_align _ _ _.
  set licond  := {| li_i := Lcond _ _; |}.
  set P2 := P ++ ligoto :: lialign ++ [::lilabel1]; set P1 := P2 ++ lc2 ++ [::lilabel].
  set Q1 := [:: licond] ++ Q; set Q2 := lilabel :: lc1 ++ Q1.
  move=> [??] D C hfn hpc; subst li lbli.
  have D1 : disjoint_labels (lbl + 1 + 1) lbl1 P1.
  + apply: disjoint_labels_cat.
    + apply disjoint_labels_cat; first by apply: disjoint_labels_w _ _ D; lia.
      apply: disjoint_labels_cat; first by rewrite /lialign; case: (al).
      by move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
    apply disjoint_labels_cat; first by apply: (valid_disjoint_labels V2); lia.
    move=> lbl' range; rewrite /is_label /= orbF; apply /eqP; lia.
  have C1 : is_linear_of fn (P1 ++ lc1 ++ Q1).
  + by move: C; rewrite /P1 /Q1 /P2 /= -!catA /= -!catA /= -catA.
  have pre1 : pre_c c1 (lbl + 1 + 1) lbl1 P1 lc1 Q1.
  + by split => //; rewrite /checked_c ok_fd chk_c1.
  have D2 : disjoint_labels lbl1 lbl2 P2.
  + rewrite /P2; apply: disjoint_labels_cat; first by apply: disjoint_labels_w _ _ D; lia.
    apply: disjoint_labels_cat; first by rewrite /lialign; case: (al).
    by move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
  have C2 : is_linear_of fn (P2 ++ lc2 ++ Q2).
  + by move: C; rewrite /P2 /P1 /Q2 /Q1 /= -!catA /= -!catA /= -catA.
  have pre2 : pre_c c2 lbl1 lbl2 P2 lc2 Q2.
  + by split => //; rewrite /checked_c ok_fd chk_c2.
  exists (lbl + 1 + 1)%positive, lbl1, lc1, P1, Q1, lbl1, lbl2, lc2, P2, Q2.
  split => //.
  (* We execute the goto *)
  rewrite (step_mix_ilsteps_eq_itree C) //; last by simpl_size;lia.
  rewrite /eval_instr /= (eval_jumpE C).
  rewrite find_label_cat_hd; last by apply: D; lia.
  rewrite find_labelE /= -!catA find_label_cat_hd; last by rewrite /lialign; case: (al).
  rewrite find_labelE /is_label /= eq_sym next_lbl_neq -!catA find_label_cat_hd; last first.
  + apply: (valid_has_not_label V2); left; lia.
  rewrite find_labelE /= /is_label /= eqxx /= -hfn.
  setoid_rewrite tau_euttge.
  (* Here the proof is done by coinduction *)
  have {}ih1 := ih1 _ _ _ _ _ pre1.
  have {}ih2 := ih2 _ _ _ _ _ pre2.
  rewrite hfn; move=> {hpc hfn}; move: ls; ginit; gcofix SELF => s.
  rewrite unfold_iter bind_bind.
  rewrite (mix_ilsteps_split p' (pcs':=size P1) (pce':=size P1 + size lc1));[| rewrite /P1; simpl_size; lia..].
  guclo eqit_clo_bind; econstructor.
  + have -> : setcpc s fn (size P + (size lialign + (size lc2 + 0).+1).+1).+1 =
              setcpc s fn (size P1).
    + rewrite /lnext_pc /setcpc /P1 /P2 /=; f_equal => //; simpl_size; lia.
    by apply ih1.
  move=> ls1 _ [<- hfn1 hpc1].
  rewrite catA in C1.
  rewrite (step_mix_ilsteps_eq_itree C1) //=; [|rewrite /P1 ?hpc1; simpl_size; lia..].
  rewrite /eval_instr /=.
  case: (Let v := sem_fexpr _ _ in to_bool v) => [b | err] /=; last first.
  + rewrite bind_throw; apply gpaco2_mon with bot2 bot2 => //.
    gfinal; right; rewrite -/(eqit eq true true); reflexivity.
  rewrite hfn1 (eval_jumpE C).
  rewrite find_label_cat_hd; last by apply: D; lia.
  rewrite find_labelE /= -!catA find_label_cat_hd; last by rewrite /lialign; case: (al).
  rewrite find_labelE /is_label /= eqxx /=.
  case: b.
  + rewrite bind_bind; setoid_rewrite tau_euttge.
    rewrite (mix_ilsteps_split p' (pcs':=size P2) (pce':=size P2 + size lc2));[| rewrite /P2; simpl_size; lia..].
    guclo eqit_clo_bind.
    econstructor.
    + have -> : setcpc ls1 fn (size P + (size lialign + 0).+1).+1 = setcpc ls1 fn (size P2).
      + rewrite /setcpc /P2 /=; f_equal; simpl_size; lia.
      by apply ih2.
    move=> ls2 _ [<- hfn2 hpc2]; rewrite bind_ret_l.
    rewrite catA in C2; rewrite (step_mix_ilsteps_eq_itree C2) //=;[|rewrite ?hpc2 /P2 /Q2; simpl_size; lia..].
    gstep; constructor; gfinal; left.
    have -> : lnext_pc ls2 = setcpc ls2 fn (size P + (size lialign + (size lc2 + 0).+1).+1).+1.
    + rewrite /lnext_pc /setcpc hpc2 /P2; f_equal => //; simpl_size; lia.
    by apply SELF.
  rewrite bind_ret_l; setoid_rewrite tau_euttge.
  rewrite mix_ilsteps_b0 //; last first.
  + by rewrite /lnext_pc hpc1 /P1 /=;simpl_size;lia.
  gstep; constructor.
  by rewrite /lnext_pc /setcpc hpc1 /P1 /=; f_equal => //; simpl_size; lia.
Qed.

Lemma linear_c_end_while al c1 e iiw c2: Pc c1 → Pc c2 → Pi_r (Cwhile al c1 e iiw c2).
Proof.
  move=> ih1 ih2 ii lbl lbli li P Q ls pre hfn hpc.
  have := pre_i_while_aux ih1 ih2 pre hfn hpc.
  move=> [lbl1] [lblc1] [lc1] [P1] [Q1] [lbl2] [lblc2] [lc2] [P2] [Q2] [chk_e pre1 pre2 ->].
  apply eutt_iter' with eq => //.
  move=> {hfn hpc}ls _ <-.
  apply eqit_bind' with (post P1 lc1).
  + by apply (ih1 _ _ _ _ _ _ pre1).
  move=> ls1 _ [<- _ _].
  case heq : (match is_bool e with | Some _ => _ | None => _ end) => [b | err] /=; last by apply eqit_Vis => -[].
  case: b heq => heq; last by apply eqit_Ret; constructor.
  apply eqit_bind' with (post P2 lc2); last first.
  + by move=> ls2 _ [<- _ _]; apply eqit_Ret; constructor.
  have /pre2{}pre2 : is_bool e ≠ Some false.
  + by case: is_bool heq => //= ? [->].
  by apply (ih2 _ _ _ _ _ _ pre2).
Qed.

(* TODO: once we remove the non-itree semantic it will be better to use this version directly *)
Definition allocate_stack_frame' (free : bool) (sz : Z) (tmp : option var_i) (rastack : bool) :=
  let sz0 := if rastack then (sz - wsize_size Uptr)%Z else sz in
  if sz0 == 0%Z then [::]
  else if free then lip_free_stack_frame liparams (vid (sp_rsp (p_extra p))) tmp sz0
  else lip_allocate_stack_frame liparams (vid (sp_rsp (p_extra p))) tmp sz0.

Lemma allocate_stack_frame_frame' free ii sz tmp rastack :
  allocate_stack_frame liparams p free ii sz tmp rastack =
  map (li_of_fopn_args ii) (allocate_stack_frame' free sz tmp rastack).
Proof. by rewrite /allocate_stack_frame /allocate_stack_frame'; case: eqP. Qed.

Lemma pre_i_call xs f es ii lbl lbli li P Q ls :
 pre_i (MkI ii (Ccall xs f es)) lbl lbli P li Q →
 lfn ls = fn → lpc ls = size P →
 exists fd fd',
  [/\ f != fn
    , get_fundef (p_funcs p) fn = Some fd
    , get_fundef (p_funcs p) f = Some fd'
    , ~~ is_RAnone (sf_return_address (f_extra fd'))
    , (sf_align (f_extra fd') ≤ sf_align (f_extra fd))%CMP
    , (sf_stk_max (f_extra fd') + frame_size (f_extra fd) <=? sf_stk_max (f_extra fd))%Z
    , disjoint_labels lbl (next_lbl lbl) P
    & let before_ops :=
        allocate_stack_frame' false (stack_frame_allocation_size (f_extra fd'))
          (tmpi_of_ra (sf_return_address (f_extra fd'))) (is_RAstack_None_call (sf_return_address (f_extra fd'))) in
      let before := [seq li_of_fopn_args ii i | i <- before_ops] in
      let licall :=
        {| li_ii := ii; li_i := Lcall (ovari_of_ra (sf_return_address (f_extra fd'))) (f, 1%positive) |} in
      let lilabel := {| li_ii := ii; li_i := Llabel ExternalLabel lbl |} in
      let after_ops :=
        allocate_stack_frame' true (stack_frame_allocation_size (f_extra fd'))
          (tmpi_of_ra (sf_return_address (f_extra fd'))) (is_RAstack_None_return (sf_return_address (f_extra fd'))) in
      let after := [seq li_of_fopn_args ii i | i <- after_ops] in
      li = before ++ [:: licall, lilabel & after] /\
      mix_ilsteps p' (pc_between_c fn P li) ls ≈
       ls1 <- match sem_fopns_args (to_estate ls) before_ops with
         | ok _ s' => Ret (of_estate s' fn (size P + size before))
         | Error err => Exception.throw (err, tt)
         end;;
       match eval_instr p' licall ls1 with
       | ok _ ls2 =>
         (ls3 <- trigger_inl1 (mix_to_small_steps.Call f ls2);;
         if check_call ls1 ls3 then
           match sem_fopns_args (to_estate ls3) after_ops with
           | ok _ s' => Ret (of_estate s' fn (size P + size li))
           | Error err => Exception.throw (err, tt)
           end
         else Exception.throw (ErrSemUndef, tt))%itree
       | Error e => Exception.throw (e, tt)
       end].
Proof.
  move=> [/checked_iE [fd ok_fd] /=].
  t_xrbindP => /negbTE ->.
  case ok_fd': get_fundef => [fd' | //]; t_xrbindP.
  move=> /negbTE hranone hal hsz _; rewrite hranone.
  rewrite !allocate_stack_frame_frame'.
  set before_ops := allocate_stack_frame' _ _ _ _.
  set before := map _ _.
  set licall := {| li_i := Lcall _ _ |}.
  set lilabel := {| li_i := Llabel _ _ |}.
  set after_ops := allocate_stack_frame' _ _ _ _.
  set after := map _ _.
  rewrite cats0 => -[??] D C hfn hpc; subst lbli li.
  exists fd, fd'; rewrite hranone; split => //; split => //.
  rewrite (mix_ilsteps_split_c p' (P' := P) (Q':= before)) //; last by simpl_size; lia.
  rewrite -catA in C.
  rewrite (sem_fopns_args_mix_ilsteps C) //; last by rewrite size_map.
  apply eqit_bind' with (post P before).
  + case: (sem_fopns_args (to_estate ls) before_ops) => [s' | err]; first by apply eqit_Ret.
    by apply eqit_Vis => -[].
  move=> ls1 _ [<- hfn1 hpc1].
  rewrite catA in C; rewrite (step_mix_ilsteps C) //=; [| by rewrite size_cat | simpl_size;lia].
  case: (eval_instr p' licall ls1) => [ls2 | err]; last by apply eqit_Vis => -[].
  apply eqit_bind' with eq; first reflexivity.
  move=> ls3 _ <-.
  case: ifP; last by move=> _; apply eqit_Vis => -[].
  move=> /andP [/eqP hfn3 /eqP hpc3].
  rewrite (mix_ilsteps_split_c p' (P' := P ++ before ++ [::licall;lilabel]) (Q':= after)) //; [| simpl_size;lia ..].
  have {}C : is_linear_of fn ((P ++ before ++ [:: licall; lilabel]) ++ after ++ Q).
  + by move: C; rewrite -!catA /=.
  rewrite (sem_fopns_args_mix_ilsteps C) //; first last.
  + simpl_size; rewrite !size_map; lia.
  + rewrite hpc3 hpc1; simpl_size; lia.
  + by rewrite hfn3.
  rewrite -/after_ops. case: sem_fopns_args => [s' | err]; last by rewrite bind_throw; reflexivity.
  rewrite bind_ret_l mix_ilsteps_b0 //=; last by simpl_size; lia.
  apply eqit_Ret; f_equal; simpl_size; lia.
Qed.

Lemma linear_c_end_call : ∀ (xs : lvals) (f : funname) (es : pexprs), Pi_r (Ccall xs f es).
Proof.
  move=> xs f es ii lbl lbli li P Q ls pre hfn hpc.
  have [fd [fd' [_ _ _ _ _ _ _ [_ ->] ]]] := pre_i_call pre hfn hpc.
  apply eqit_bind' with eq; first reflexivity.
  move=> ls1 _ <-.
  case: eval_instr => [ls2 | err]; last by apply eqit_Vis => -[].
  apply eqit_bind' with eq; first reflexivity.
  move=> ls3 _ <-; case: ifP => _; last by apply eqit_Vis => -[].
  case: sem_fopns_args => [s' | err]; last by apply eqit_Vis => -[].
  by apply eqit_Ret.
Qed.

Lemma linear_c_end c : Pc c.
Proof.
  apply (cmd_rect (Pr:=Pi_r) (Pi:=Pi) (Pc:=Pc)) => //;
   auto using linear_c_end_nil, linear_c_end_cons,
     linear_c_end_assgn, linear_c_end_opn, linear_c_end_syscall, linear_c_end_assert,
     linear_c_end_if, linear_c_end_for, linear_c_end_while, linear_c_end_call.
Qed.

Lemma linear_i_end i : Pi i.
Proof.
  apply (instr_Rect (Pr:=Pi_r) (Pi:=Pi) (Pc:=Pc)) => //;
  auto using linear_c_end_nil, linear_c_end_cons,
     linear_c_end_assgn, linear_c_end_opn, linear_c_end_syscall, linear_c_end_assert,
     linear_c_end_if, linear_c_end_for, linear_c_end_while, linear_c_end_call.
Qed.

(* This are the main lemmas of this section *)
Lemma pre_c_cons i c :
  ∀ lbl lblic lic P Q ls,
  pre_c (i :: c) lbl lblic P lic Q →
  lfn ls = fn → lpc ls = size P →
  exists lbli lblc li lc,
    [/\ lblic = lbli
      , lic = li ++ lc
      , pre_i i lblc lbli P li (lc ++ Q)
      , pre_c c lbl lblc (P ++ li) lc Q
      & mix_ilsteps p' (pc_between_c fn P lic) ls ≈
         ls' <- mix_ilsteps p' (pc_between_c fn P li) ls ;;
         mix_ilsteps p' (pc_between_c fn (P ++ li) lc) ls'].
Proof.
  apply pre_c_cons_aux.
  + by apply linear_i_end.
  apply linear_c_end.
Qed.

Lemma pre_i_if e c1 c2 : ∀ ii lbl lbli li P Q ls,
  pre_i (MkI ii (Cif e c1 c2)) lbl lbli P li Q →
  lfn ls = fn → lpc ls = size P →
  exists lbl1 lblc1 lc1 P1 Q1 lbl2 lblc2 lc2 P2 Q2,
    [/\ check_fexpr ii e = ok tt
      , pre_c c1 lbl1 lblc1 P1 lc1 Q1
      , pre_c c2 lbl2 lblc2 P2 lc2 Q2
      & mix_ilsteps p' (pc_between_c fn P li) ls ≈
        match (Let v := sem_fexpr (lvm ls) (to_fexpr e) in to_bool v) with
        | Ok b =>
          ls' <- (if b then mix_ilsteps p' (pc_between_c fn P1 lc1) (setcpc ls fn (size P1))
                  else mix_ilsteps p' (pc_between_c fn P2 lc2) (setcpc ls fn (size P2)));;
          Ret (setcpc ls' fn (size P + size li))
        | Error e0 => Exception.throw (e0, tt)
        end].
Proof.
  apply pre_i_if_aux; apply linear_c_end.
Qed.

Lemma pre_i_while al c1 e iiw c2 :
  ∀ ii lbl lbli li P Q ls,
  pre_i (MkI ii (Cwhile al c1 e iiw c2)) lbl lbli P li Q →
  lfn ls = fn → lpc ls = size P →
  exists lbl1 lblc1 lc1 P1 Q1 lbl2 lblc2 lc2 P2 Q2,
    [/\ (is_bool e = None -> check_fexpr ii e = ok tt)
      , pre_c c1 lbl1 lblc1 P1 lc1 Q1
      , (is_bool e <> Some false -> pre_c c2 lbl2 lblc2 P2 lc2 Q2)
      & mix_ilsteps p' (pc_between_c fn P li) ls ≈
        ITree.iter (fun ls =>
          ls1 <- mix_ilsteps p' (pc_between_c fn P1 lc1) (setcpc ls fn (size P1));;
          let b := if is_bool e is Some b then ok b
                   else Let v := sem_fexpr (lvm ls1) (to_fexpr e) in to_bool v in
          match b with
          | Ok b =>
            if b then
              (ls2 <- mix_ilsteps p' (pc_between_c fn P2 lc2) (setcpc ls1 fn (size P2));;
               Ret (inl ls2))%itree
            else Ret (inr (setcpc ls1 fn (size P + size li)))
          | Error e0 => Exception.throw (e0, tt)
          end)%itree ls].
Proof.
  apply pre_i_while_aux; apply linear_c_end.
Qed.

End ILSTEPS_END.


  (* ----------------------------------------------------------------------- *)

  Context {rE0 : EventRels E0}.

  (* Assuming [fn] takes [(scs1, m1, vm1)] to [(scs2, m2, vm2)],
     we need to prove that its compilation has the same behavior, and
     - if it's an export function (that is, [lret] is [None]), we are done.
     - if it's a callee ([lret] carries the caller), we return.
     Note that if it's a callee then we start execution at position 1 (because
     the first instruction is just the label). *)
  Definition killed_on_entry (ra : return_address_location) : Sv.t :=
    match ra with
    | RAnone => var_tmps
    | RAreg x _ => Sv.singleton x
    | RAstack or _ _ _ => sv_of_option or
    end.

  (* The set of variable killed/written by the execution of the function,
     for export function saved are removed since those variables are restored *)
  Definition killed_on_exit
    (ra : return_address_location) (killed saved : Sv.t) : Sv.t :=
    match ra with
    | RAnone => Sv.diff killed saved
    | RAreg _ _ => killed
    | RAstack _ _ _ _ => Sv.add vrsp killed
    end.

  (* The set of variable written by the execution of the exit code of function *)
  Definition killed_by_exit
    (ra : return_address_location) (saved : Sv.t) : Sv.t :=
    match ra with
    | RAnone => Sv.add var_tmp2 saved
    | RAreg _ _ => saved
    | RAstack _ _ _ _ => saved
    end.

  Definition sp_alloc_ra
    (sp : word Uptr) (ra : return_address_location) : word Uptr :=
    if is_RAstack_None_return ra then (sp + wrepr _ (wsize_size Uptr))%R else sp.

  (* Precondition for function *)
  Definition preF (fn1 fn2 : funname) (s1 : estate) (ls1 : lstate) :=
    let m1 := lmem ls1 in
    let vm1 := lvm ls1 in
    [/\ fn1 = fn2
      , escs s1 = lscs ls1
      , match_mem_gen (top_stack m0) s1 m1
      , lfn ls1 = fn1
      , source_mem_split s1 (top_stack (emem s1))
      , max_bound fn1 (top_stack (emem s1))
      & exists body ra lret sp callee_saved,
          [/\ is_linear_of fn1 body
            , is_ra_of fn1 ra
            , (kill_vars (killed_on_entry ra) s1).[vrsp <- Vword sp] <=1 vm1
            , value_of_ra m1 vm1 ra lret
            , if lret is Some (caller, _, _) then fn1 != caller.1 else true
            , lpc ls1 = if lret is Some _ then 1 else 0
            , is_sp_for_call fn1 s1 sp
            , is_callee_saved_of fn1 callee_saved
            , vm_initialized_on vm1 callee_saved
            & if is_RAnone ra then m0 = emem s1 else True]].

  Definition postF (fn1 fn2 : funname) (s1 : estate) (ls1 : lstate) (ks2 : Sv.t* estate) (ls2 : lstate) :=
    let m1 := lmem ls1 in
    let vm1 := lvm ls1 in
    let m2 := lmem ls2 in
    let vm2 := lvm ls2 in
    let (k, s2) := (ks2.1, ks2.2) in
    forall body ra lret sp callee_saved,
       is_linear_of fn1 body ->
       is_ra_of fn1 ra ->
       value_of_ra m1 vm1 ra lret ->
       is_sp_for_call fn1 s1 sp ->
       is_callee_saved_of fn1 callee_saved ->
       let: ssaved := sv_of_list id callee_saved in
       [/\ escs ks2.2 = lscs ls2
         , validw (emem s1) =3 validw (emem ks2.2)
         , (kill_vars (killed_by_exit ra ssaved) s2).[vrsp <- Vword (sp_alloc_ra sp ra)] <=1 vm2
         , vm1 =[\ killed_on_exit ra k ssaved ] vm2
         , if lret is Some ((caller, lbl), _, pc) then lfn ls2 = caller /\ lpc ls2 = pc.+1
           else lpc ls2 = size body
         , stack_stable (emem s1) (emem s2)
         , preserved_metadata s1 m1 m2
         , match_mem_gen (top_stack m0) s2 m2
         & target_mem_unchanged m1 m2].

  Notation CallE := (mix_to_small_steps.CallE funname lstate).

  Definition PreF {T1 T2} (d1 : recCallK T1) (d2 : CallE T2) : Prop :=
    match d1, d2 with
    | RecCallK fn1 s1, mix_to_small_steps.Call fn2 ls1 => preF fn1 fn2 s1 ls1
    end.

  Definition PostF {T1 T2} (d1 : recCallK T1) (t1: T1) (d2 : CallE T2) (t2: T2) : Prop :=
    match d1 in recCallK T1_ return T1_ -> T2 -> Prop with
    | RecCallK fn1 s1 =>
      match d2 in mix_to_small_steps.CallE _ _ T2_ return Sv.t * estate -> T2_ -> Prop with
      | mix_to_small_steps.Call fn2 ls1 => postF fn1 fn2 s1 ls1
      end
    end t1 t2.

  #[local] Instance relEvent_recCall {E E0 : Type -> Type} {wE: with_Error E E0} {rE0 : EventRels E0} :
      EventRels2 (Sum.sum1 recCallK E0) (Sum.sum1 CallE E0) :=
    {| EPreRel0_  := sum_prerelF (@PreF) EPreRel0
     ; EPostRel0_ := sum_postrelF (@PostF) EPostRel0
    |}.

  Section LINEAR_CMD.

  Context (fn : funname).

  Definition inv_c (P : lcmd) (s : estate) (ls : lstate) :=
    let sp := top_stack (emem s) in
    [/\ match_mem_gen (top_stack m0) s (lmem ls)
      , escs s = lscs ls
      , evm s <=1 lvm ls
      , lpc ls = size P
      , lfn ls = fn
      , (evm s).[vrsp] = Vword sp
      , source_mem_split s sp
      & max_bound_sub fn sp].

  Definition inv_ir (P : lcmd) (s : estate) (ls : lstate) :=
    let sp := top_stack (emem s) in
    [/\ match_mem_gen (top_stack m0) s (lmem ls)
      , escs s = lscs ls
      , evm s <=1 lvm ls
      , lpc ls = size P
      , lfn ls = fn
      & (evm s).[vrsp] = Vword sp].

  Definition post_ir (P : lcmd) (s1 : estate) (ls1 : lstate) (ks2 : Sv.t * estate) (ls2 : lstate) :=
    [/\ match_mem_gen (top_stack m0) ks2.2 (lmem ls2)
      , escs ks2.2 = lscs ls2
      , evm ks2.2 <=1 lvm ls2
      , lpc ls2 = size P
      , lfn ls2 = fn
      , lvm ls1 =[\ ks2.1 ] lvm ls2
      , validw (emem s1) =3 validw (emem ks2.2)
      , preserved_metadata s1 (lmem ls1) (lmem ls2)
      & target_mem_unchanged (lmem ls1) (lmem ls2)].

  Definition post_c (P : lcmd) (ks1 : Sv.t * estate) (ls1 : lstate) (ks2 : Sv.t * estate) (ls2 : lstate) :=
    [/\ inv_c P ks2.2 ls2
      , (disjoint ks1.1 (magic_variables p) -> disjoint ks2.1 (magic_variables p))
      , Sv.Subset ks1.1 ks2.1
      , lvm ls1 =[\ ks2.1 ] lvm ls2
      , validw (emem ks1.2) =3 validw (emem ks2.2)
      , stack_stable (CM:= (@CM (@_pd syscall_state ep))) ks1.2 ks2.2
      , preserved_metadata ks1.2 (lmem ls1) (lmem ls2)
      & target_mem_unchanged (lmem ls1) (lmem ls2)].

  Definition post_i P (s1 : estate) (ls1 : lstate) (ks2 : Sv.t * estate) (ls2 : lstate) :=
    post_c P (Sv.empty, s1) ls1 ks2 ls2.

  Let Pi (i:instr) :=  ∀ lbl lbli P li Q,
    pre_i fn i lbl lbli P li Q →
    wkequiv_io
      (inv_c P)
      (isem_i var_tmps (sem_F := sem_funK_rec_check var_tmps) p i)
      (mix_ilsteps p' (pc_between_c fn P li))
      (post_i (P ++ li)).

  Let Pi_r (i:instr_r) := ∀ ii lbl lbli P li Q,
    pre_i fn (MkI ii i) lbl lbli P li Q →
    wkequiv_io
      (inv_c P)
      (isem_ir var_tmps (sem_F := sem_funK_rec_check var_tmps) p i)
      (mix_ilsteps p' (pc_between_c fn P li))
      (post_ir (P ++ li)).

  Let Pc (c:cmd) := ∀ lbl lblc P lc Q,
    pre_c fn c lbl lblc P lc Q →
    wkequiv_io
      (fun ks ls => inv_c P ks.2 ls)
      (isem_cmd_ (isem_i var_tmps (sem_F := sem_funK_rec_check var_tmps)) p c)
      (mix_ilsteps p' (pc_between_c fn P lc))
      (post_c (P ++ lc)).

  Lemma RSP_in_magic :
    Sv.In vrsp (magic_variables p).
  Proof. by rewrite Sv.add_spec Sv.singleton_spec; right. Qed.

  Lemma HMkI : ∀ (i : instr_r) (ii : instr_info), Pi_r i → Pi (MkI ii i).
  Proof.
    move => i ii hir lbl lbli P li Q hpre s1 ls1 hinv1.
    have h := hir ii _ _ _ _ _ hpre _ _ hinv1.
    rewrite -(bind_ret_r (mix_ilsteps p' (pc_between_c fn P li) ls1)).
    apply (xrutt_facts.xrutt_bind h).
    move=> ks2 ls2 hinv2; apply xrutt_bind_iresult_left; t_xrbindP.
    move=> /and3P [/stack_stableP hstable /value_eqb_eq hrsp' hdisj].
    apply xrutt.xrutt_Ret.
    case: hinv1 => hmm1 hscs1 hu1 hpc1 hfn1 hrsp hsource hbound.
    case: hinv2 => hmm2 hscs2 hu2 hpc2 hfn2 hex hvalid hpres htarg.
    split => //=; last by apply SvP.MP.subset_empty.
    have heq := ss_top_stack hstable.
    rewrite /inv_c -{-1}heq.
    split => //.
    move=> pr; rewrite -hvalid; apply hsource.
  Qed.

  Lemma inv_c_lfn P s ls : inv_c P s ls -> lfn ls = fn.
  Proof. by case => _ _ _ _ ->. Qed.

  Lemma inv_c_lpc P s ls : inv_c P s ls -> lpc ls = size P.
  Proof. by case. Qed.

  Lemma Hnil : Pc [::].
  Proof.
    move=> lbl lblc P lc Q [/= _ [? <-]] D C ks1 ls1 hinv.
    rewrite cats0 mix_ilsteps_0; last first.
    + rewrite /pc_between_c /pc_between /= (inv_c_lfn hinv) eqxx.
      rewrite (inv_c_lpc hinv); simpl_size; lia.
    by apply xrutt.xrutt_Ret; split.
  Qed.

  Lemma post_c_inv_c P ks1 ls1 ks2 ls2 : post_c P ks1 ls1 ks2 ls2 → inv_c P ks2.2 ls2.
  Proof. by case. Qed.

  Lemma post_c_trans P1 ks2 ls2 P2 ks1 ls1 ks3 ls3 :
    post_c P1 ks1 ls1 ks2 ls2 -> post_c P2 ks2 ls2 ks3 ls3 ->
    post_c P2 ks1 ls1 ks3 ls3.
  Proof.
    move=> [] hinv1 hdisj1 hsub1 hex1 hval1 hstable1 hpres1 htarget1.
    move=> [] hinv2 hdisj2 hsub2 hex2 hval2 hstable2 hpres2 htarget2.
    split => //.
    + by move=> /hdisj1.
    + by apply: SvD.F.Subset_trans hsub1 hsub2.
    + by apply: eq_exT hex2; apply: eq_exI hex1.
    + by move=> ???; rewrite hval1 hval2.
    + by apply: stack_stable_trans hstable1 hstable2.
    + etransitivity; first exact: hpres1.
      by apply: preserved_metadataE hpres2.
    move=> pr hnv hnpr.
    rewrite (htarget1 pr hnv hnpr).
    by rewrite (htarget2 pr hnv hnpr).
  Qed.

  Lemma post_i_c P ks1 ls1 ks2 ls2:
    post_i P ks1.2 ls1 ks2 ls2 ->
    post_c P ks1 ls1 (Sv.union ks1.1 ks2.1, ks2.2) ls2.
  Proof.
    move=> [] hinv1 hdisj1 hsub1 hex1 hval1 hstable1 hpres1 htarget1.
    split => //=.
    + by move=> hd1; apply union_disjoint => //; apply hdisj1.
    + by apply SvP.MP.union_subset_1.
    apply: eq_exI hex1; by apply SvP.MP.union_subset_2.
  Qed.

  Lemma Hcons : ∀ (i : instr) (c : cmd), Pi i → Pc c → Pc (i :: c).
  Proof.
    move=> i c hi hc lbl lblc P lc Q hpre ks1 ls1 hinv.
    have := pre_c_cons hpre (inv_c_lfn hinv) (inv_c_lpc hinv).
    move=> [lbli] [lblc'] [li] [lc'] [? hlc hprei hprec ->].
    rewrite /=.
    apply (xrutt_facts.xrutt_bind (hi _ _ _ _ _ hprei _ _ hinv)).
    move=> ks2 ls2 /post_i_c hinv2.
    have := hc _ _ _ _ _ hprec _ _ (post_c_inv_c hinv2).
    apply xrutt_facts.xrutt_weaken => //.
    move=> ks3 s3; rewrite hlc catA.
    apply: post_c_trans hinv2.
  Qed.

  Lemma Hassgn : ∀ (x : lval) (tg : assgn_tag) (ty : atype) (e : pexpr), Pi_r (Cassgn x tg ty e).
  Proof. by move=> > [/checked_iE[]]. Qed.

  Lemma check_rexprsP ii es u :
    allM (check_rexpr ii) es = ok u →
    exists2 rs, oseq.omap rexpr_of_pexpr es = Some rs &
    ∀ s vs, sem_pexprs true [::] s es = ok vs → sem_rexprs s rs = ok vs.
  Proof.
    case: u; elim: es.
    - by move => _; exists [::].
    move => e es ih.
    rewrite /allM /=; t_xrbindP => /check_rexprP[] r ok_r /ih{}[] rs -> rec.
    rewrite  ok_r; eexists; first reflexivity.
    by t_xrbindP => s vs z /(rexpr_of_pexprP ok_r) /= -> > /rec -> <-.
  Qed.

  Lemma check_lexprsP ii xs u :
    allM (check_lexpr ii) xs = ok u →
    exists2 ds, oseq.omap lexpr_of_lval xs = Some ds &
    ∀ s vs s', write_lvals true [::] s xs vs = ok s' → write_lexprs ds vs s = ok s'.
  Proof.
    case: u; elim: xs.
    - by move => _; exists [::].
    move => x xs ih.
    rewrite /allM /=; t_xrbindP => /check_lexprP[] d ok_d /ih{}[] ? -> rec.
    rewrite ok_d; eexists; first reflexivity.
    by move => s [] // v vs s'; t_xrbindP => ? /(lexpr_of_lvalP ok_d) /= -> /rec.
  Qed.

  Lemma Hopn : ∀ (xs : lvals) (t : assgn_tag) (o : sopn) (es : pexprs), Pi_r (Copn xs t o es).
  Proof.
    move=> xs tag o es ii lbl lbli P li Q [/checked_iE [fd ok_fd] /=].
    t_xrbindP => /check_rexprsP [] qs -> chk_es /check_lexprsP[] ds -> chk_xs [??]; subst lbl li.
    move=> D C s1 ls1 [M1 SC1 X1 hpc hfn hsp1 S1 MAX1].
    rewrite (step_mix_ilsteps C) //; last by simpl_size; lia.
    rewrite -(bind_ret_r (iresult _ _)); apply xrutt_bind_iresult_left => /= ks2.
    rewrite /sem_sopn p_globs_nil; t_xrbindP => s2 vxs ves hes hex ok_s2 ?; subst ks2.
    rewrite /eval_instr /=.
    have [ vs' /(match_mem_gen_sem_pexprs M1) /chk_es ok_vs' vs_vs' ] := sem_pexprs_uincl X1 hes.
    have [ rs' ok_rs' rs_rs' ] := vuincl_exec_opn vs_vs' hex.
    have [ vm2 /(match_mem_gen_write_lvals M1) [ m2 ok_s2' M2 ] ok_vm2 ] := writes_uincl X1 rs_rs' ok_s2.
    have {} ok_s2'' := chk_xs _ _ _ ok_s2'.
    rewrite SC1 in ok_vs', ok_s2', ok_s2''; rewrite ok_vs' /= ok_rs'/= ok_s2'' /=.
    rewrite mix_ilsteps_b0 => //=; last by rewrite hpc addn1.
    apply xrutt.xrutt_Ret; split => //=.
    + simpl_size; lia.
    + exact: vrvsP ok_s2'.
    + exact: write_lvals_validw ok_s2.
    + exact: preserved_metadata_write_lvals rs_rs' ok_s2 ok_s2' SC1 X1 M1.
    move=> pr hnv hnpr.
    apply (write_lvals_mem_unchanged rs_rs' ok_s2 ok_s2' SC1 X1 M1).
    apply /negP => /S1 /orP [//|].
    move=> hpr; apply hnpr.
    apply: pointer_range_incl_l hpr.
    have h: (wunsigned sp0 - max0 <= wunsigned (top_stack (emem s1)))%Z.
    + have /= := MAX1 _ ok_fd.
      move: (checked_prog ok_fd) => /=; rewrite /check_fd.
      t_xrbindP=> _ _ _ _ /and4P [_ _ _ /ZleP /= ?] _ _ _.
      by lia.
    rewrite wunsigned_sub; first by lia.
    move: (top_stack (emem s1)) h => sp.
    have /= := wunsigned_range sp; lia.
  Qed.

  Lemma vm_after_syscall_uincl vm1 vm2 :
    vm1 <=1 vm2 ->
    vm_after_syscall vm1 <=1 vm_after_syscall vm2.
  Proof.
    by move=> h x; rewrite /vm_after_syscall !kill_varsE; case: ifP.
  Qed.

  Lemma match_mem_gen_fill_mem m1 m1' m2 ptr bytes:
    match_mem_gen (top_stack m0) m1 m1' → fill_mem m1 ptr bytes = ok m2 →
    exists2 m2', fill_mem m1' ptr bytes = ok m2' & match_mem_gen (top_stack m0) m2 m2'.
  Proof.
    rewrite /fill_mem; t_xrbindP => mm [z m2'] /= hf ?; subst m2' => /=.
    elim: bytes 0%Z m1 m1' mm hf => [ | b bytes ih] z1 m1 m1' mm /=.
    + by move=> [_ <-]; exists m1'.
    by t_xrbindP => _ m3  /(mm_write mm) [m3' -> mm3 /=] <- /ih -/(_ _ mm3).
  Qed.

  Lemma match_mem_gen_exec_syscall o scs1 m1 m1' scs2 m2 ves vs:
    match_mem_gen (top_stack m0) m1 m1' → exec_syscall_s scs1 m1 o ves = ok (scs2, m2, vs) →
    exists2 m2', exec_syscall_s scs1 m1' o ves = ok (scs2, m2', vs) & match_mem_gen (top_stack m0) m2 m2'.
  Proof.
  move: o => [ws n] mm; rewrite /exec_syscall_s /=; t_xrbindP=> z -> /=.
  case: get_random => [scs' bytes]; rewrite /exec_getrandom_store_s.
  t_xrbindP=> -[_ _] w -> {}m2 hm1 [<- <- ->] /= <- <-.
  have [m2' -> mm2] := match_mem_gen_fill_mem mm hm1.
  by exists m2'.
  Qed.

  Lemma syscall_killP vm : vm =[\syscall_kill] vm_after_syscall vm.
  Proof. by move=> x /Sv_memP /negPf; rewrite /vm_after_syscall kill_varsE => ->. Qed.

  Lemma fill_mem_mem_unchanged m1 m2 m1' m2' ptr bytes :
    fill_mem m1 ptr bytes = ok m1' ->
    fill_mem m2 ptr bytes = ok m2' ->
    forall p, ~~ validw m1 Aligned p U8 -> read m2 Aligned p U8 = read m2' Aligned p U8.
  Proof.
    rewrite /fill_mem; t_xrbindP.
    rewrite /fill_mem; t_xrbindP => -[z m1''] /= hf ? -[z' m2''] /= hf' ?; subst m1'' m2''.
    elim: bytes 0%Z m1 m2 hf hf' => [ | b bytes ih] z1 m1 m2 /=.
    + by move=> _ [_ <-].
    t_xrbindP=> _ m1'' hw1 <- /ih{}ih _ m2'' hw2 <- /ih{}ih pr hnv.
    rewrite (write_mem_unchanged hw1 hw2 hnv).
    apply ih.
    by rewrite (write_validw_eq hw1).
  Qed.

  Lemma exec_syscall_mem_unchanged m1 m2 m1' m2' scs scs' o ves ves' vs vs' :
    List.Forall2 value_uincl ves ves' ->
    exec_syscall_s scs m1 o ves = ok (scs', m1', vs) ->
    exec_syscall_s scs m2 o ves' = ok (scs', m2', vs') ->
    forall p, ~~ validw m1 Aligned p U8 -> read m2 Aligned p U8 = read m2' Aligned p U8.
  Proof.
    move: o => [ws n] hall hex; have {hex hall} := exec_syscallPs_eq hex hall.
    rewrite /exec_syscall_s; t_xrbindP => z -> + _ [<-].
    case: get_random => [scs'' bytes].
    rewrite /exec_syscall_store_s /exec_getrandom_store_s.
    t_xrbindP=> -[_ _] w1 hw1 {}m1' hm1 [<-] _ _ _ _
      [_ _] w2 hw2 {}m2' hm2 [<- _] _ /= <- _.
    move: ves' hw1 hw2 => [//| _ [//| _ [|//]]] -> [?]; subst w2.
    exact: fill_mem_mem_unchanged hm1 hm2.
    Qed.

  Lemma preserved_metadata_syscall m1 m2 m1' m2' scs scs' o ves ves' vs vs' :
    List.Forall2 value_uincl ves ves' ->
    exec_syscall_s scs m1 o ves = ok (scs', m1', vs) ->
    exec_syscall_s scs m2 o ves' = ok (scs', m2', vs') ->
    preserved_metadata m1 m2 m2'.
  Proof.
    move=> huincl hsys1 hsys2 pr hpr hnv.
    by apply (exec_syscall_mem_unchanged huincl hsys1 hsys2 hnv).
  Qed.

  Lemma Hsyscall : ∀ (xs : lvals) (o : syscall_t) (es : pexprs), Pi_r (Csyscall xs o es).
  Proof.
    move=> xs o es ii lbl lbli P li Q [/checked_iE [fd ok_fd] /= _] [??]; subst lbli li.
    move=> D C s1 ls1 [M1 SC1 X1 hpc hfn hsp1 S1 MAX1].
    rewrite (step_mix_ilsteps C) //; last by simpl_size; lia.
    rewrite /= -!bind_bind.
    apply: (xrutt_bind (RR := fun fs' ls' =>
      exists ves len scs' bytes ls0,
        [/\ sem_pexprs true (p_globs p) s1 es = ok ves
          , exec_syscall_arg_s o ves = ok len
          , exec_syscall_store_s o scs' (emem s1) ves bytes = ok (fscs fs', fmem fs', fvals fs')
          , lset_fstate (syscall_sig o).(scs_vout) ls1 fs' = ok ls0
          & ls' = lnext_pc ls0])).
    - admit.
    case: o C => [ws n] C /=.
    move=> [scs1 m1 vs1] ? [ves [len [scs' [bytes [ls0 [hves hlen +++]]]]]].
    rewrite /lset_fstate /upd_estate /=; t_xrbindP.
    move=> [{}m1 w] hm1 ? /= <- _ s2 ok_s2 ? ->; subst ls0 scs1.

    rewrite mix_ilsteps_b0 => //=; last by rewrite hpc addn1.
    rewrite tau_eutt.
    apply xrutt_iresult_left.
    rewrite /rmap; t_xrbindP=> -[_ _] s2' ok_s2' [<- <-].
    split => //=.
    + admit.
    + by move: ok_s2 ok_s2' => /write_lvals_escs -> /write_lvals_escs ->.
    + admit.
    + rewrite /lnext_pc /lset_estate' /= hpc; simpl_size; lia.
    + apply: (eq_exT (vm2 := vm_after_syscall (lvm ls1))).
      + by apply: eq_exI (syscall_killP (lvm ls1)); SvD.fsetdec.
      admit.
    + admit.
    + admit.
    move=> pr hnv hnpr.
    have hnv1: ~~ validw (emem s1) Aligned pr U8.
    + apply /negP; move=> /S1 /orP [//|].
      move=> hpr; apply hnpr.
      apply: pointer_range_incl_l hpr.
      have h: (wunsigned sp0 - max0 <= wunsigned (top_stack (emem s1)))%Z.
      + have /= := MAX1 _ ok_fd.
        move: (checked_prog ok_fd) => /=; rewrite /check_fd.
        t_xrbindP=> _ _ _ _ /and4P [_ _ _ /ZleP /= ?] _ _ _.
        by lia.
      rewrite wunsigned_sub; first by lia.
      move: (top_stack (emem s1)) h => sp.
      by have := wunsigned_range sp; lia.
    admit.
  Admitted.

  Lemma Hassert : ∀ a : assertion, Pi_r (Cassert a).
  Proof. by move => > [/checked_iE[]]. Qed.

  Lemma sem_fexpr_bool P s1 ls1 ii e (b:bool) :
    inv_c P s1 ls1 ->
    check_fexpr ii e = ok tt ->
    sem_pexpr true (p_globs p) s1 e = ok (Vbool b) ->
    sem_fexpr (lvm ls1) (to_fexpr e) = ok (Vbool b).
  Proof.
    rewrite p_globs_nil => -[M _ U _ _ _ _ _] /check_fexprP [] f ok_f ok_e.
    rewrite /to_fexpr ok_f.
    have [ ? /(match_mem_gen_sem_pexpr M) + /value_uinclE ?]:= sem_pexpr_uincl U ok_e; subst.
    apply: fexpr_of_pexprP ok_f.
  Qed.

  Lemma post_c_post_ir P s1 ls1 ks2 ls2 :
    post_c P (Sv.empty, s1) ls1 ks2 ls2 ->
    post_ir P s1 ls1 ks2 ls2.
  Proof. case => -[] *; split => //. Qed.

  Lemma inv_c_setpc P1 P2 ks1 ls1 pc:
    inv_c P2 ks1 ls1 ->
    size P1 = pc ->
    inv_c P1 ks1 (setcpc ls1 fn pc).
  Proof. by case => *; split => //. Qed.

  Lemma post_c_setpc P1 P2 ks1 ls1 ks2 ls2 pc:
    post_c P2 ks1 ls1 ks2 ls2 ->
    size P1 = pc ->
    post_c P1 ks1 ls1 ks2 (setcpc ls2 fn pc).
  Proof. case => hinv *; split => //; by apply: (inv_c_setpc hinv). Qed.

  Lemma Hif : ∀ (e : pexpr) (c1 c2 : cmd), Pc c1 → Pc c2 → Pi_r (Cif e c1 c2).
  Proof.
    move => e c1 c2 ih1 ih2 ii lbl lbli P li Q hpre s1 ls1 hinv.
    have := pre_i_if hpre (inv_c_lfn hinv) (inv_c_lpc hinv).
    move=> [lbl1] [lblc1] [lc1] [P1] [Q1] [lbl2] [lblc2] [lc2] [P2] [Q2] [chk_e hpre1 hpre2 ->].
    apply xrutt_bind_iresult_left => b /sem_cond_sem_pexpr hb.
    rewrite (sem_fexpr_bool hinv chk_e hb) /=; rewrite -(bind_ret_r (isem_cmd_ _ _ _ _)) => {hb}; case: b.
    + have {}ih1:= ih1 _ _ _ _ _ hpre1 (Sv.empty, s1) (setcpc ls1 fn (size P1)) (inv_c_setpc hinv erefl).
      apply (xrutt_facts.xrutt_bind ih1) => ks2 ls2 hpost.
      by apply/xrutt.xrutt_Ret/post_c_post_ir/(post_c_setpc hpost); rewrite size_cat.
    have {}ih2:= ih2 _ _ _ _ _ hpre2 (Sv.empty, s1) (setcpc ls1 fn (size P2)) (inv_c_setpc hinv erefl).
    apply (xrutt_facts.xrutt_bind ih2) => ks2 ls2 hpost.
    by apply/xrutt.xrutt_Ret/post_c_post_ir/(post_c_setpc hpost); rewrite size_cat.
  Qed.

  Lemma Hfor : ∀ (v : var_i) (dir : expr.dir) (lo hi : pexpr) (c : cmd), Pc c → Pi_r (Cfor v (dir, lo, hi) c).
  Proof. by move => > _ > [/checked_iE[]]. Qed.

  Lemma Hwhile : ∀ (a : expr.align) (c : cmd) (e : pexpr) (info : instr_info) (c' : cmd),
      Pc c → Pc c' → Pi_r (Cwhile a c e info c').
  Proof.
    move=> al c1 e iiw c2 ih1 ih2 ii lbl lbli P li Q hpre s1 ls1 hinv.
    have := pre_i_while hpre (inv_c_lfn hinv) (inv_c_lpc hinv).
    move=> [lbl1] [lblc1] [lc1] [P1] [Q1] [lbl2] [lblc2] [lc2] [P2] [Q2] [chk_e hpre1 hpre2 ->] {hpre}.
    rewrite /= /isem_while_loop.
    pose inv_w ks2 ls2 := exists P, post_c P (Sv.empty, s1) ls1 ks2 ls2.
    have : inv_w (Sv.empty, s1) ls1 by exists P; split.
    move: (Sv.empty, s1) {-2}ls1 => ks1' ls1'.
    apply: xrutt_facts.xrutt_iter => {}ks1' {}ls1' [P' hpost1].
    rewrite /isem_while_round.
    have {}ih1:= ih1 _ _ _ _ _ hpre1 ks1' (setcpc ls1' fn (size P1)) (post_c_inv_c (post_c_setpc hpost1 erefl)).
    apply (xrutt_facts.xrutt_bind ih1) => ks2 ls2 hpost2.
    apply xrutt_bind_iresult_left => b /sem_cond_sem_pexpr he.
    have [-> {}hpre2 {he}] :
      match is_bool e with
      | Some b0 => ok b0
      | None => Let v := sem_fexpr (lvm ls2) (to_fexpr e) in to_bool v
      end = ok b
      /\ (b -> pre_c fn c2 lbl2 lblc2 P2 lc2 Q2).
    + case: is_boolP he chk_e hpre2 => [be | {}e].
      + by move=> [->] _ h; split => // hb; apply h; rewrite hb.
      move=> hb /(_ erefl) chk_e hpre2; split; last by move=> _; apply hpre2.
      by rewrite (sem_fexpr_bool (post_c_inv_c hpost2) chk_e hb).
    have hpost2' := post_c_trans hpost1 hpost2.
    case: b hpre2 => hpre2; last first.
    + apply/xrutt.xrutt_Ret;constructor.
      by apply/post_c_post_ir /(post_c_setpc hpost2'); rewrite size_cat.
    have {}ih2:= ih2 _ _ _ _ _ (hpre2 erefl) ks2 (setcpc ls2 fn (size P2)) (post_c_inv_c (post_c_setpc hpost2 erefl)).
    apply (xrutt_facts.xrutt_bind ih2) => ks3 ls3 hpost3.
    apply/xrutt.xrutt_Ret;constructor.
    exists (P2 ++ lc2); apply: post_c_trans hpost2' hpost3.
  Qed.

  Lemma find_entry_label f fd :
    sf_return_address (f_extra fd) ≠ RAnone →
    find_label xH (lfd_body (linear_fd f fd).2) = ok 0.
  Proof. by rewrite /linear_fd /linear_body; case: sf_return_address. Qed.

  Lemma is_label_lstore ii lbl x ofs y :
    is_label lbl (lstore liparams ii x ofs y) = false.
  Proof. done. Qed.

  Lemma preserved_metadata_store_top_stack m1 ws sz ioff sz' m1' m2 (ptr : word Uptr) m2' :
    alloc_stack m1 ws sz ioff sz' = ok m1'
    → write m2 Aligned (top_stack_after_alloc (top_stack m1) ws (sz + sz')) ptr = ok m2'
    → (wsize_size Uptr <= ioff)%Z
    → preserved_metadata m1 m2 m2'.
  Proof.
    move=> ok_m1' ok_m2' hioff a ha _.
    symmetry; apply (writeP_neq _ ok_m2').
    apply: disjoint_range_alt.
    have A := alloc_stackP ok_m1'.
    have: pointer_range (top_stack m1) (stack_root m1) a.
    + rewrite /pointer_range !zify; lia.
    rewrite pointer_range_between => hb.
    apply (disjoint_zrange_incl_r hb).
    rewrite -(alloc_stack_top_stack ok_m1').
    apply: disjoint_zrange_incl_l (ass_above_limit_disjoint_zrange A).
    apply zbetween_le.
    by have := ass_ioff A; lia.
  Qed.

  Lemma stack_frame_allocation_size_bound e :
    (0 <= sf_stk_sz e)%Z ->
    (0 <= sf_stk_extra_sz e)%Z ->
    (sf_stk_sz e + sf_stk_extra_sz e <= stack_frame_allocation_size e)%Z.
  Proof.
    move=> hsz hextra.
    rewrite /stack_frame_allocation_size.
    have := round_ws_range (sf_align e) (sf_stk_sz e + sf_stk_extra_sz e).
    by clear; lia.
  Qed.

  Lemma frame_size_bound e :
    (0 <= sf_stk_sz e)%Z ->
    (0 <= sf_stk_extra_sz e)%Z ->
    (sf_stk_sz e + sf_stk_extra_sz e <= frame_size e)%Z.
  Proof.
    move=> hsz hextra.
    rewrite /frame_size.
    have := stack_frame_allocation_size_bound hsz hextra.
    by case: is_RAnone; clear; lia.
  Qed.

  (* If we write in a frame that is itself inside the stack, we can establish
     [target_mem_unchanged]. *)
  Lemma target_mem_unchanged_store al top sz pr ws (w:word ws) m1 m2 :
    zbetween (sp0 - wrepr Uptr max0) max0 top sz ->
    between top sz pr ws ->
    write m1 al pr w = ok m2 ->
    target_mem_unchanged m1 m2.
  Proof.
    move=> hb1 hb2 ok_m2.
    move=> pr' hnv hnpr.
    symmetry; apply (writeP_neq _ ok_m2).
    apply: disjoint_range_alt.
    apply (disjoint_zrange_incl_l hb2).
    apply (disjoint_zrange_incl_l hb1).
    apply (not_between_U8_disjoint_zrange no_overflow_max0).
    move: hnpr; rewrite pointer_range_between.
    rewrite wunsigned_sub; last by have := wunsigned_range sp0; lia.
    by rewrite Z.sub_add_distr Z.sub_diag Z.sub_0_l Z.opp_involutive.
  Qed.

  Notation sv_of_ra := (fun ra => sv_of_option (ovar_of_ra ra)) (only parsing).

  Lemma killed_on_entry_uincl vm vm' (w : word Uptr) s ra :
    vm.[vrsp] = Vword w ->
    vm' =[\ Sv.add vrsp (sv_of_ra ra) ] vm ->
    s <=1 vm' ->
    (kill_vars (killed_on_entry ra) s).[vrsp <- Vword w] <=1 vm.
  Proof.
    move=> hw heq hincl x.
    rewrite Vm.setP.
    case: (vrsp =P x) => [? | hneq].
    - subst x. by rewrite hw vm_truncate_val_eq.
    rewrite kill_varsE.
    case: Sv_memP => [_ | hnin].
    - by apply/compat_value_uincl_undef/Vm.getP.
    rewrite -heq //.
    case: ra hneq hnin heq => [ | ? | [?|] ?] /=;
      SvD.fsetdec.
  Qed.

  Lemma has_label_allocate_stack_frame p1 b ii z tmp rastack lbl :
    ~~has (is_label lbl) (allocate_stack_frame liparams p1 b ii z tmp rastack).
  Proof.
    rewrite /allocate_stack_frame; case: eqP => // _.
    by rewrite map_li_of_fopn_args_has_label.
  Qed.

  Lemma has_label_allocate_stack_frame' b ii z tmp rastack lbl :
    ~~has (is_label lbl) (map (li_of_fopn_args ii) (allocate_stack_frame' b z tmp rastack)).
  Proof.
    rewrite -allocate_stack_frame_frame'.
    apply has_label_allocate_stack_frame.
  Qed.

  Lemma Hcall : ∀ (xs : lvals) (f : funname) (es : pexprs), Pi_r (Ccall xs f es).
  Proof.
    move=> xs f es ii lbl lbli P li Q hpre s1 ls1 hinv.
    have := pre_i_call hpre (inv_c_lfn hinv) (inv_c_lpc hinv).
    move=> [fd] [fd'] [/negbTE fn'_neq_fn ok_fd ok_fd' ok_ra ok_align /ZleP ok_max D].
    set rastack_before := is_RAstack_None_call _.
    set rastack_after  := is_RAstack_None_return _.
    set sz := stack_frame_allocation_size _.
    set sz_before := if rastack_before then (sz - wsize_size Uptr)%Z else sz.
    set sz_after := if rastack_after then (sz - wsize_size Uptr)%Z else sz.
    set before_ops := allocate_stack_frame' _ _ _ rastack_before.
    set after_ops := allocate_stack_frame' _ _ _ rastack_after.
    set licall := {| li_i := Lcall _ _ |}.
    set lilabel := {| li_i := Llabel _ _ |} => /=.
    set before := map _ before_ops.
    set after := map _ after_ops => -[? ->]; subst li.
    case: (hpre) => _ _ _ C.
    have := get_fundef_p' ok_fd'.
    set lfd' := linear_fd _ fd'.
    move => ok_lfd'.
    move: (checked_prog ok_fd') => /=; rewrite /check_fd /frame_size.
    t_xrbindP => chk_body ok_to_save _ _ ok_stk_sz ok_ret_addr ok_save_stack _.
    have lbl_valid : (fn, lbl) \in (label_in_lprog p').
    - apply: (label_in_lfundef _ C).
      rewrite /label_in_lcmd /=.
      by rewrite !pmap_cat !mem_cat inE eqxx !orbT.
    have h := encode_label_dom small_dom_p' lbl_valid.
    case ok_ptr: encode_label h => [ ptr | // ] _.
    rewrite /is_disjoint_magic ok_fd'.
    apply xrutt_bind_iresult_left; t_xrbindP => ra_sem.
    rewrite bind_bind. apply xrutt_bind_iresult_left.
    rewrite /is_init_state_ok /initialize_funcall /= ok_fd' /=.
    move=> [] /map_errP; t_xrbindP => z /map_errP; t_xrbindP.
    move=> /andP [sp_aligned T] m /map_errP ok_m _ _ {z}.
    case: hinv => M SC1 X hpc hfn hsp S MAX.
    (* FIXME : the test corresponding to ok_save_stack seems to be not used in the proof.
               can we remove it ? *)
    move: ok_stk_sz sp_aligned {ok_save_stack}.
    rewrite /top_stack_aligned (negbTE ok_ra) /= => ok_stk_sz sp_aligned.
    pose Stmp := if tmpi_of_ra (sf_return_address (f_extra fd')) is Some x then Sv.singleton x else Sv.empty.
    have StmpE : Sv.Equal Stmp (tmp_call (f_extra fd')).
    + by rewrite /tmp_call /Stmp /tmpi_of_ra; case: sf_return_address => //= [_ | _ _ _] [].
    move: (X vrsp). rewrite hsp.
    move=> /get_word_uincl_eq -/(_ (subctype_refl _)) vm2_rsp.
    have vrsp_ne_aux :
      match tmpi_of_ra (sf_return_address (f_extra fd')) with
      | Some x => v_var (vid (sp_rsp (p_extra p))) ≠ v_var x
      | None => True
      end.
    + move: T; rewrite /valid_RSP /kill_tmp_call /= kill_varsE.
      case: Sv_memP => // + _.
      rewrite /tmpi_of_ra /fd_tmp_call /tmp_of_ra /tmp_call ok_fd'.
      by case: sf_return_address => // [_ | _ _ _] [?|] //=; clear; SvD.fsetdec.
    have hgetrsp : get_var true (to_estate ls1) vrsp = ok (Vword (top_stack (CM:= (@CM (@_pd syscall_state ep))) s1)).
    + by rewrite /get_var vm2_rsp.
    have [vm2_b [hsem_before heqvm2 hvm2_b_rsp]] :
      exists (vm2_b:Vm.t),
        [/\ sem_fopns_args (to_estate ls1) before_ops = ok (with_vm (to_estate ls1) vm2_b)
          , (lvm ls1) =[\ Sv.add vrsp Stmp] vm2_b
          & vm2_b.[vrsp] = Vword (top_stack (emem s1) - wrepr Uptr sz_before)].
    + rewrite /before_ops /allocate_stack_frame' -/sz_before; case: eqP => [-> | _].
      + by exists (lvm ls1); split => //; rewrite GRing.subr0.
      apply: (spec_lip_allocate_stack_frame hliparams _ _ hgetrsp).
      case: sf_return_address ok_ret_addr vrsp_ne_aux => //=.
      + by move=> v [x|] //= /andP [] _.
      by move=> ra_call ra_return z [x|] //= /and5P [_ _ + _ _].
    rewrite hsem_before bind_ret_l.
    set P' := (P ++ (before ++ [:: licall, lilabel & after]) ++ Q).
    set ra := sf_return_address (f_extra fd').
    set o := Some ((fn, lbl), P', (size P + size before).+1).
    set s := (top_stack (emem s1) - wrepr Uptr sz)%R.
    have [m' [vm' [hmatch hvm'_rsp heq_vm' hvalue_of hpres_m1_m' U h2]]] : exists m' vm',
      let ls := of_estate (with_vm (to_estate ls1) vm2_b) fn (size P + size before) in
      let ls' :=
        {|
          lscs := lscs ls1;
          lmem := m';
          lvm := vm';
          lfn := f;
          lpc := 1;
        |}
      in
      [/\ match_mem_gen (top_stack m0) (kill_tmp_call p f s1) m'
        , vm'.[vrsp] = Vword s
        , vm2_b =[\ Sv.add vrsp (killed_on_entry ra) ] vm'
        , value_of_ra m' vm' ra o
        , preserved_metadata (kill_tmp_call p f s1) (lmem ls1) m'
        , target_mem_unchanged (lmem ls1) m'
        & eval_instr p' licall ls = ok ls'
      ].
    + rewrite /eval_instr /= /ra /get_label_after_pc /setpc /=.
      set ls1_ := (of_estate _ _ _).
      have -> /= : find_instr p' (lnext_pc ls1_) = Some {| li_ii := ii; li_i := linear.Llabel ExternalLabel lbl |}.
      + rewrite /lnext_pc; assert (h := find_instr_skip C).
        have h1 := h ls1_ (size before + 1) erefl.
        by rewrite -addn1 -addnA -/before h1 -catA oseq.onth_cat ltnNge addn1 leqnSn /= subSnn.
      rewrite /rencode_label ok_ptr /= (eval_jumpP ok_lfd' (find_entry_label _ _)); last by apply/eqP.
      have hfind : find_label lbl P' = ok (size P + size before).+1.
      + rewrite /P' find_label_cat_hd; last by apply: D; rewrite /next_lbl; lia.
        rewrite -catA find_label_cat_hd; last by apply has_label_allocate_stack_frame'.
        by rewrite /find_label /= /is_label /= eqxx /= addn1 addnS.
      rewrite /ra_vm in ra_sem. rewrite /sz_before /rastack_before in hvm2_b_rsp.
      rewrite /Stmp in heqvm2.
      have /disjointP{}ra_sem := ra_sem.
      have rsp_magic := RSP_in_magic.
      have rsp_singleton: Sv.In vrsp (Sv.singleton vrsp) by apply SvD.F.singleton_iff.
      case eq_ra : sf_return_address ok_ra ok_ret_addr ra_sem hvm2_b_rsp heqvm2 => [ | x | [ x | ] ra_return ofs] //= _
        ok_ret_addr ra_sem hvm2_b_rsp heqvm2.
       (* RAreg x _ *)
      + exists (lmem ls1),  vm2_b.[x <- Vword ptr]; split => //.
        + rewrite Vm.setP_neq ?hvm2_b_rsp //; apply /eqP => ?; subst x.
          by apply: (ra_sem vrsp).
        + by move=> /= y hy; rewrite Vm.setP_neq //; apply/eqP; move: hy; clear; SvD.fsetdec.
        + move: ok_ret_addr => /andP[] hty _.
          split => //.
          rewrite ok_ptr; exists ptr => //; rewrite Vm.setP_eq vm_truncate_val_eq //.
          by rewrite (convertible_eval_atype hty).
        rewrite /= set_var_truncate //=.
        move: ok_ret_addr => /andP[] hty _.
        by rewrite (convertible_eval_atype hty).
      (* RAstack (Some x) ofs _ *)
      + case/and5P: ok_ret_addr => ok_ret_addr _ _ _ _.
        exists (lmem ls1), vm2_b.[x <- Vword ptr]; split => //.
        + rewrite Vm.setP_neq ?hvm2_b_rsp //; apply /eqP => ?; subst x.
          by apply: (ra_sem vrsp).
        + by move=> /= y hy; rewrite Vm.setP_neq //; apply/eqP; move: hy; clear; SvD.fsetdec.
        + split => //.
          rewrite ok_ptr; exists ptr => //; rewrite Vm.setP_eq vm_truncate_val_eq //.
          by rewrite (convertible_eval_atype ok_ret_addr).
        by rewrite /= set_var_truncate //= (convertible_eval_atype ok_ret_addr).
      (* RAstack None ofs _ *)
      move: ok_ret_addr => /and5P [] _ _ /eqP ? /eqP hioff sf_align_for_ptr; subst ofs.
      have [m' ok_m' M']:
         exists2 m1', write (lmem ls1) Aligned (top_stack_after_alloc (top_stack (emem (kill_tmp_call p f s1))) (sf_align (f_extra fd'))
                   (sf_stk_sz (f_extra fd') + sf_stk_extra_sz (f_extra fd')))%R ptr = ok m1' &
                         match_mem_gen (top_stack m0) (kill_tmp_call p f s1) m1'.
      + apply: mm_write_invalid.
        * have /= := MAX _ ok_fd; lia.
        * exact: M.
        1-2: cycle -1.
        * apply: (is_align_m sf_align_for_ptr); exact: do_align_is_align.
        rewrite -(alloc_stack_top_stack ok_m).
        have := (Memory.alloc_stackP ok_m).(ass_above_limit).
        have := (Memory.alloc_stackP ok_m).(ass_ioff).
        rewrite /kill_tmp_call /= hioff /=.
        lia.
      exists m', vm2_b.[vrsp <- Vword s]; split => //.
      + by rewrite Vm.setP_eq vm_truncate_val_eq.
      + by move=> /= y hy; rewrite Vm.setP_neq //; apply/eqP; move: hy; clear; SvD.fsetdec.
      + split => //.
        rewrite ok_ptr; exists ptr => //; exists s; first by rewrite Vm.setP_eq vm_truncate_val_eq.
        move: ok_m'; rewrite /= wrepr0 GRing.addr0 top_stack_after_aligned_alloc // wrepr_opp.
        by apply writeP_eq.
      + apply: (preserved_metadata_store_top_stack ok_m ok_m').
        by rewrite -hioff; apply Z.le_refl.
      + case/and4P: ok_stk_sz => /ZleP stk_sz_pos /ZleP stk_extra_sz_pos /ZltP frame_noof /ZleP stk_frame_le_max.
        (* the new frame is inside the stack *)
        have hb1:
          zbetween
            (sp0 - wrepr Uptr max0) max0
            (top_stack m) (sf_stk_sz (f_extra fd') + sf_stk_extra_sz (f_extra fd')).
        + rewrite /zbetween !zify.
          rewrite wunsigned_sub; last by have := wunsigned_range sp0; lia.
          have := MAX _ ok_fd.
          rewrite (wunsigned_top_stack_after_aligned_alloc _ _ _ _ ok_m) //=.
          have := stack_frame_allocation_size_bound stk_sz_pos stk_extra_sz_pos.
          move: sp0_le ok_max => /=; lia.
        (* the range is inside the new frame *)
        have hb2:
          between (top_stack m) (sf_stk_sz (f_extra fd') + sf_stk_extra_sz (f_extra fd'))
                  (top_stack m) Uptr.
        + apply zbetween_le.
          rewrite hioff /=.
          by have /= := (alloc_stackP ok_m).(ass_ioff); lia.
        move: ok_m'; rewrite -(alloc_stack_top_stack ok_m).
        by apply (target_mem_unchanged_store hb1 hb2).

      set s_ := (top_stack (emem s1) - wrepr Uptr (sz - wsize_size Uptr))%R; rewrite lp_rspE.
      have -> /= : Let x := get_var true vm2_b vrsp in to_pointer x = ok s_.
      + by rewrite /get_var hvm2_b_rsp /= truncate_word_u.
      move: ok_m'; rewrite /s_ /= wrepr_sub.
      set ts := top_stack _.
      have -> :
        (ts - (wrepr Uptr sz - wrepr Uptr (wsize_size Uptr)) - wrepr Uptr (wsize_size Uptr))%R =
        (ts - wrepr Uptr sz)%R
        by ssrring.ssring.
      by rewrite top_stack_after_aligned_alloc // wrepr_opp => ->.
    rewrite h2 /= !bind_trigger.
    have C' : is_linear_of f (lfd_body lfd'.2) by exists lfd'.2.
    have hraof : is_ra_of f (sf_return_address (f_extra fd')) by exists fd'.
    have sp_call :  is_sp_for_call f (kill_tmp_call p f s1) s.
    + by exists fd' => //=; rewrite (negbTE ok_ra).
    have is_saved_of :  is_callee_saved_of f [::].
    + by exists fd' => //=; rewrite (negbTE ok_ra).
    apply xrutt.xrutt_Vis.
    + split => //.
      + move=> fd''; rewrite ok_fd' => -[?]; subst fd''.
        rewrite (negbTE ok_ra).
        by move: (MAX _ ok_fd) ok_max sp0_le => /=; lia.
      exists (lfd_body lfd'.2), (sf_return_address (f_extra fd')), o, s, [::]; split => //.
      + rewrite -/ra /=.
        move=> x; rewrite Vm.setP; case: eqP => [<- | hne].
        + by rewrite hvm'_rsp /= cmp_le_refl.
        rewrite /kill_tmp_call !kill_varsE; case: Sv_memP.
        + by move=> _; apply/compat_value_uincl_undef/Vm.getP.
        move=> hnin1; case: Sv_memP.
        + by move=> _; apply/compat_value_uincl_undef/Vm.getP.
        rewrite /fd_tmp_call ok_fd' => hnin2.
        apply: (value_uincl_trans (X x)); rewrite heqvm2; last by clear -hne hnin2 StmpE; SvD.fsetdec.
        by rewrite heq_vm' //; clear -hne hnin1; SvD.fsetdec.
      + by rewrite /o /= fn'_neq_fn.
      by rewrite (negbTE ok_ra).
    move=> ks2 ls2; rewrite /EPostRel /= /postF => hpost.
    have /= := hpost _ _ _ _ _ C' hraof hvalue_of sp_call is_saved_of.
    move=> [hscs' hvalid hsub_vm' heq_vm [hfn2 hpc2] hstable hpres hmatch' U' {hpost}].
    rewrite /check_call /= hfn2 hpc2 !eqxx /=.
    set ts := top_stack (M := Memory.M) s1.
    have vm2'_rsp:
       (lvm ls2).[vrsp] = Vword (s + wrepr Uptr (if rastack_after then wsize_size Uptr else 0%Z)).
    + move: (hsub_vm' vrsp); rewrite /kill_vars /=.
      rewrite Vm.setP_eq /= cmp_le_refl => /get_word_uincl_eq -/(_ (subctype_refl _)).
      rewrite /rastack_after /ra /sp_alloc_ra.
      by case: (sf_return_address (f_extra fd')) => [|??|?[?|//]??] /=; rewrite wrepr0 GRing.addr0.
    have [vm2'_b [hsem_after heqvm2' hvm2'_b_rsp]] :
      exists (vm2'_b:Vm.t),
        [/\ sem_fopns_args (to_estate ls2) after_ops = ok {| escs := lscs ls2; emem := lmem ls2; evm := vm2'_b|},
             (lvm ls2) =[\ Sv.add vrsp Stmp] vm2'_b  &
             vm2'_b.[vrsp] = Vword ts].
    + move: vm2'_rsp; rewrite /after_ops /allocate_stack_frame' /rastack_after /sz.
      case: eqP => H0 vm2'_rsp /=.
      + exists (lvm ls2); split => //.
        rewrite vm2'_rsp /s /ts /sz.
        move: H0; case: ifP => _ H.
        + have -> : stack_frame_allocation_size (f_extra fd') = wsize_size Uptr by lia.
          by f_equal; ssrring.ssring.
        by rewrite H wrepr0; f_equal; ssrring.ssring.
      set sz0 := (if _ then _ else _).
      have := spec_lip_free_stack_frame hliparams.
      rewrite /free_stack_frame_correct.
      move=> /(_ (sp_rsp (p_extra p)) (tmpi_of_ra (sf_return_address (f_extra fd'))) (to_estate ls2)).
      move=> /(_ (s + wrepr Uptr (if is_RAstack_None_return (sf_return_address (f_extra fd')) then wsize_size Uptr else 0%Z))%R sz0) [].
      + case: sf_return_address ok_ret_addr vrsp_ne_aux => //=.
        + by move=> v [x|] //= /andP [] _.
        by move=> ?? z [x|] //= /and5P [_ _ + _ _].
      + by rewrite /get_var /with_vm /= vm2'_rsp.
      move => vm2'_b [H1 H2 H3]; exists vm2'_b; split => //.
      rewrite /sz0 H3 /ts /s /sz /sz0; f_equal.
      by case: ifP => _; rewrite ?wrepr_sub ?wrepr0; ssrring.ssring.
    case : (boolP (valid_RSP p s1 ks2.2 && Sv.subset (writefun_RA var_tmps p f) ks2.1)) => /=; last first.
    + move=> _; rewrite bind_throw; apply xrutt.xrutt_CutL.
      by rewrite /core_logics.errcutoff /is_error /subevent /resum /fromErr mid12.
    move=> /andP [] hrsp /Sv.subset_spec hsubk.
    rewrite bind_ret_l hsem_after; apply xrutt.xrutt_Ret; split => //=.
    + move: hrsp; rewrite /= /valid_RSP /set_RSP => /value_eqb_eq h x /=.
      rewrite kill_varsE; case: Sv_memP => [_ | ].
      + by apply/compat_value_uincl_undef/Vm.getP.
      rewrite /fd_tmp_call ok_fd' -StmpE => hnin.
      have := hsub_vm' x.
      rewrite Vm.setP; case: eqP => [? | hneq]; first by subst x; rewrite h hvm2'_b_rsp.
      rewrite kill_varsE; case: Sv_memP.
      + move=> hin; have : Sv.In x (sv_of_list id [::]).
        + move: ok_ra hin;rewrite /killed_by_exit; case: sf_return_address => //=.
        rewrite /sv_of_list /=; clear; SvD.fsetdec.
      move=> _ H; apply (value_uincl_trans H).
      by rewrite heqvm2' //; move: hnin hneq; clear; SvD.fsetdec.
    + by simpl_size.
    + move => x; rewrite /fd_tmp_call ok_fd' -StmpE => x_notin_k.
      case: (vrsp =P x) => x_neq_rsp.
      + by subst x; rewrite vm2_rsp hvm2'_b_rsp.
      rewrite -heqvm2'; last by move: x_notin_k x_neq_rsp; clear; SvD.fsetdec.
      rewrite -heq_vm; last first.
      + move: x_notin_k x_neq_rsp; rewrite /ra_vm /ra /=; clear.
        by case: sf_return_address => [ | r ? | [ r | ] ???] /=; SvD.fsetdec.
      rewrite heqvm2; last by clear -x_neq_rsp x_notin_k; SvD.fsetdec.
      apply heq_vm'.
      rewrite /killed_on_entry /ra.
      move: x_notin_k x_neq_rsp hsubk; rewrite /writefun_RA ok_fd' /ra_undef /ra_vm /ra /Stmp /=; clear.
      by case: sf_return_address => [ | r ? | [ r | ] ???] /=; SvD.fsetdec.
    + by etransitivity; eauto.
    by etransitivity; [exact: U | exact: U'].
  Qed.

  Lemma linear_cP c : Pc c.
  Proof.
    by apply (cmd_rect (Pr:=Pi_r) (Pi:=Pi) (Pc:=Pc)
      HMkI Hnil Hcons Hassgn Hopn Hsyscall Hassert
      Hif Hfor Hwhile Hcall).
  Qed.

  End LINEAR_CMD.

  Lemma push_to_save_has_no_label ii lbl m sp:
    ~~ has (is_label lbl) (push_to_save liparams p ii m sp).
  Proof. by rewrite /push_to_save has_map -all_predC allT. Qed.

  Lemma all_disjoint_aligned_betweenP (lo hi: Z) (al: wsize) m :
    all_disjoint_aligned_between liparams lo hi al m = ok tt →
    if m is a :: m' then
      exists ofs ws,
        [/\ check_to_save_slot a = ok (ofs, ws) /\ lip_check_ws liparams ws,
         (lo <= ofs)%Z,
         (ws ≤ al)%CMP,
         is_align (wrepr Uptr ofs) ws &
         all_disjoint_aligned_between liparams (ofs + wsize_size ws) hi al m' = ok tt
        ]
    else
      (lo <= hi)%Z.
  Proof.
    case: m lo => [ | a m ] lo.
    - by apply: rbindP => _ /ok_inj <- /assertP /lezP.
    apply: rbindP => last /=.
    t_xrbindP => mid [ofs ws] /= hslot.
    t_xrbindP => /lezP lo_le_ofs ok_ws aligned_ofs hchk <-{mid} ih last_le_hi.
    exists ofs, ws; split => //.
    by rewrite /all_disjoint_aligned_between ih /= /assert ifT.
  Qed.

  Lemma all_disjoint_aligned_between_range (lo hi: Z) (al: wsize) m :
    all_disjoint_aligned_between liparams lo hi al m = ok tt →
    (lo <= hi)%Z.
  Proof.
    elim: m lo.
    + by move=> lo /all_disjoint_aligned_betweenP.
    move=> a m ih lo /all_disjoint_aligned_betweenP [ofs [ws] [_ lo_le_ofs _ _ /ih]].
    have := wsize_size_pos ws; lia.
  Qed.

  (* Convenient weaker form of preserved-metatada *)
  Lemma preserved_metadata_w m al sz ioff sz' m' m1 m2:
    alloc_stack m al sz ioff sz' = ok m' →
    preserved_metadata m' m1 m2 →
    ∀ p,
      (wunsigned (top_stack m') <= wunsigned p < wunsigned (top_stack m))%Z →
      ~~ validw m' Aligned p U8 → read m1 Aligned p U8 = read m2 Aligned p U8.
  Proof.
    move => ok_m' M a [] a_lo a_hi; apply: M; split; first exact: a_lo.
    have A := alloc_stackP ok_m'.
    rewrite A.(ass_root).
    apply: Z.lt_le_trans; first exact: a_hi.
    exact: top_stack_below_root.
  Qed.

  Lemma stack_slot_in_bounds m al sz ioff  sz' m' ofs ws i :
    alloc_stack m al sz ioff sz' = ok m' →
    (sz <= ofs)%Z →
    (ofs + wsize_size ws <= sz + sz')%Z →
    (0 <= i < wsize_size ws)%Z →
    (wunsigned (top_stack m') + sz <= wunsigned (add (top_stack m' + wrepr Uptr ofs)%R i)
     ∧ wunsigned (add (top_stack m' + wrepr Uptr ofs)%R i) < wunsigned (top_stack m))%Z.
  Proof.
    move => ok_m' ofs_lo ofs_hi i_range.
    have A := alloc_stackP ok_m'.
    have below_old_top : (wunsigned (top_stack m') + ofs + i < wunsigned (top_stack m))%Z.
    - apply: Z.lt_le_trans; last exact: proj2 (ass_above_limit A).
      by rewrite -!Z.add_assoc -Z.add_lt_mono_l Z.max_r; lia.
    have ofs_no_overflow : (0 <= wunsigned (top_stack m') + ofs)%Z ∧ (wunsigned (top_stack m') + ofs + i < wbase Uptr)%Z.
    - split; first by generalize (wunsigned_range (top_stack m')), (ass_ioff A); lia.
      apply: Z.lt_trans; last exact: proj2 (wunsigned_range (top_stack m)).
      exact: below_old_top.
    by rewrite !wunsigned_add; lia.
  Qed.

  Lemma mm_can_write_after_alloc m al sz ioff sz' m' m1 ofs ws (v: word ws) :
    alloc_stack m al sz ioff sz' = ok m' →
    (0 <= sz)%Z →
    (0 <= sz')%Z →
    (ws ≤ al)%CMP →
    is_align (wrepr Uptr ofs) ws →
    (sz <= ofs)%Z →
    (ofs + wsize_size ws <= sz + sz')%Z →
    (* Maybe this lemma is used only with m = m0 *)
    (wunsigned (top_stack m) <= wunsigned (top_stack m0))%Z ->
    match_mem_gen (top_stack m0) m m1 →
    ∃ m2,
      [/\
       write m1 Aligned (top_stack m' + wrepr Uptr ofs)%R v = ok m2,
       preserved_metadata m m1 m2 &
       match_mem_gen (top_stack m0) m m2
      ].
  Proof.
    move => ok_m' sz_pos extra_pos frame_aligned ofs_aligned ofs_lo ofs_hi hle0 M.
    have A := alloc_stackP ok_m'.
    have ofs_no_overflow : (0 <= wunsigned (top_stack m') + ofs)%Z ∧ (wunsigned (top_stack m') + ofs < wbase Uptr)%Z.
    - split; first by generalize (wunsigned_range (top_stack m')); lia.
      apply: Z.le_lt_trans; last exact: proj2 (wunsigned_range (top_stack m)).
      apply: Z.le_trans; last exact: proj2 (ass_above_limit A).
      rewrite -Z.add_assoc -Z.add_le_mono_l Z.max_r //.
      have := wsize_size_pos ws.
      lia.
    have ofs_below : (wunsigned (top_stack m') + ofs + wsize_size ws <= wunsigned (top_stack m))%Z.
    - apply: Z.le_trans; last exact: proj2 (ass_above_limit A).
      by rewrite -!Z.add_assoc -Z.add_le_mono_l Z.max_r.
    cut (exists2 m2, write m1 Aligned (top_stack m' + wrepr Uptr ofs)%R v = ok m2 & match_mem_gen (top_stack m0) m m2).
    - case => m2 ok_m2 M2; exists m2; split; [ exact: ok_m2 | | exact: M2 ].
      move => a [] a_lo a_hi _.
      rewrite (write_read8 ok_m2) /=.
      case: andP; last by [].
      case => _ /ltzP a_below; exfalso.
      move: a_below.
      rewrite subE wunsigned_add -/(wunsigned (_ + _)) wunsigned_add //; first lia.
      split; last by generalize (wunsigned_range a); lia.
      have := wsize_size_pos ws; lia.
    apply: (mm_write_invalid _ hle0); first exact: M; last first.
    - apply: is_align_add ofs_aligned.
      apply: is_align_m; first exact: frame_aligned.
      rewrite (alloc_stack_top_stack ok_m').
      exact: do_align_is_align.
    rewrite wunsigned_add; last exact: ofs_no_overflow.
    split; last exact: ofs_below.
    apply: Z.le_trans; first exact: proj1 (ass_above_limit A).
    lia.
  Qed.

  Lemma check_to_save_slotP x ofs ofs' ws :
    check_to_save_slot (x, ofs) = ok (ofs', ws)
    -> let: xi := mk_var_i x in
       exists2 xname,
          x = {| vtype := aword ws; vname := xname; |}
          & ofs = ofs'.
  Proof.
    rewrite /check_to_save_slot /=.
    move: x => [[|||ws'] xname] //= [<- <-]; eauto.
  Qed.

  Lemma read_after_spill top al vm m1 to_spill m2 lo hi :
    (wunsigned top + hi < wbase Uptr)%Z →
    (0 <= lo)%Z →
    all_disjoint_aligned_between liparams
      lo
      hi
      al
      to_spill
    = ok tt →
    foldM (λ '(x, ofs) m,
           Let: ws := if vtype x is aword ws then ok ws else Error ErrType in
           Let _ := assert (lip_check_ws liparams ws) ErrType in
           Let: v := get_var true vm x >>= to_word ws in
           write m Aligned (top + wrepr Uptr ofs)%R v)
          m1 to_spill = ok m2 →
    [/\
     ∀ ofs ws,
       ((0 <= ofs)%Z /\ (ofs + wsize_size ws <= lo)%Z) \/
       (hi <= ofs /\ wunsigned top + ofs + wsize_size ws <= wbase Uptr)%Z →
       read m2 Aligned (top + wrepr Uptr ofs)%R ws = read m1 Aligned (top + wrepr Uptr ofs)%R ws
     &
     ∀ x ofs, (x, ofs) \in to_spill →
       exists2 ws, is_word_type x.(vtype) = Some ws /\ lip_check_ws liparams ws &
       exists2 v, get_var true vm x >>= to_word ws = ok v & read m2 Aligned (top + wrepr Uptr ofs)%R ws = ok v
    ].
  Proof.
    move => no_overflow.
    elim: to_spill m1 lo.
    - by move => _ lo _ _ [->].
    case => - [] xt x ofs to_spill ih m1 lo lo_pos /all_disjoint_aligned_betweenP[] y [] ws [] [].
    move=> /check_to_save_slotP /= [xname] [??] ?; subst x xt y.
    move=> hchk lo_le_ofs ws_aligned ofs_aligned ok_to_spill /=; rewrite hchk /=.
    have ofs_below_hi := all_disjoint_aligned_between_range ok_to_spill.
    t_xrbindP => m1' w v ok_v ok_w ok_m1 rec.
    have ws_pos := wsize_size_pos ws.
    have lo'_pos : (0 <= ofs + wsize_size ws)%Z by lia.
    have {ih} [ih1 ih2] := ih _ _ lo'_pos ok_to_spill rec.
    split.
    - move => ofs' ws' hofs'.
      rewrite ih1; last lia.
      have n_pos := wsize_size_pos ws.
      have n_pos' := wsize_size_pos ws'.
      have [top_lo _] := wunsigned_range top.
      rewrite (writeP_neq _ ok_m1) //.
      apply: disjoint_range_alt; split.
      1-2: rewrite !zify !wunsigned_add; lia.
      rewrite !wunsigned_add; lia.
    move => y ofs_y; rewrite inE; case: eqP.
    - case => ->{y} ->{ofs_y} _ /=.
      exists ws => //; exists w; first by rewrite ok_v.
      rewrite ih1; first by exact: (writeP_eq ok_m1).
      lia.
    by move => _ /ih2.
  Qed.

  Lemma eval_uincl_kill_vars_incl X1 X2 vm1 vm2 z:
    Sv.Subset X1 X2 ->
    value_uincl (kill_vars X1 vm1).[z] vm2.[z] ->
    value_uincl (kill_vars X2 vm1).[z] vm2.[z].
  Proof.
    move=> S;
    rewrite !kill_varsE; case:Sv_memP => hin1; case: Sv_memP => hin2 // _;
      first by clear -S hin1 hin2; SvD.fsetdec.
    by apply/compat_value_uincl_undef/Vm.getP.
  Qed.

  Lemma vm_uincl_kill_vars_set_incl X1 X2 vm1 vm2 x v1 v2:
    Sv.Subset X1 X2 ->
    value_uincl v2 v1 ->
    (kill_vars X1 vm1).[x <- v1] <=1 vm2 ->
    (kill_vars X2 vm1).[x <- v2] <=1 vm2.
  Proof.
    move=> S huv huvm z.
    case: (x =P z) (huvm z) => [<- | /eqP ?].
    + by rewrite !Vm.setP_eq; apply: value_uincl_trans; apply value_uincl_vm_truncate.
    by rewrite !Vm.setP_neq //; apply eval_uincl_kill_vars_incl.
  Qed.

  Lemma vm_uincl_kill_vars X1 vm1 :
    kill_vars X1 vm1 <=1 vm1.
  Proof.
    move=> x; rewrite kill_varsE.
    case: (Sv.mem _) => //.
    by apply/compat_value_uincl_undef/Vm.getP.
  Qed.

  Lemma vm_uincl_after_alloc_stack fd m m' vm0 vm1 vm2 :
    let: ts := top_stack m in
    let: sf_sz := (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd))%Z in
    let: al := sf_align (f_extra fd) in
    let: ts' := align_word al (ts - wrepr Uptr sf_sz) in
    let: vm3 :=
      (kill_vars var_tmps vm0).[vrsp <- Vword ts]
    in
    vm3 <=1 vm1
    -> sf_return_address (f_extra fd) = RAnone
    -> let: ssr := savedstackreg (sf_save_stack (f_extra fd)) in
       vm2 =[\ Sv.union ssr (Sv.union var_tmps (Sv.add vrsp vflags)) ] vm1
    -> get_var true vm2 vrsp = ok (Vword ts')
    -> alloc_stack
         m
         al
         (sf_stk_sz (f_extra fd))
         (sf_stk_ioff (f_extra fd))
         (sf_stk_extra_sz (f_extra fd))
       = ok m'
    -> set_RSP p m' (kill_vars (ra_undef fd var_tmps) vm0) <=1 vm2.
  Proof.
    move=> hvm3 hra hvm2 hgetrsp halloc z.
    set vm4 := kill_vars _ _.
    have := hvm3 z.
    clear hvm3.
    rewrite /set_RSP -/vrspi.
    case: (vrsp =P z) => [<- | hne].

    - t_vm_get.
      move: hgetrsp.
      rewrite /get_var /= cmp_le_refl; t_xrbindP => _ ->.
      rewrite (alloc_stack_top_stack halloc) /top_stack_after_alloc.
      by rewrite wrepr_opp.

    t_vm_get.
    rewrite !kill_varsE.
    case: (Sv_memP _ (ra_undef _ _)).
    - move=> _ _. by apply/compat_value_uincl_undef/Vm.getP.

    rewrite /ra_undef /ra_vm hra {hra} /=.
    move=> hnin.
    case: Sv_memP => [? | _]; first by SvD.fsetdec.
    rewrite hvm2 {hvm2}; first done.

    clear -hne hnin.
    move: hnin.
    rewrite /saved_stack_vm /savedstackreg /=.
    case: sf_save_stack => [| r | ofs] hnin.
    all: rewrite SvP.MP.add_union_singleton || rewrite Sv_union_empty.
    all: repeat (move=> /Sv.add_spec [|] /=; first SvD.fsetdec).
    all: SvD.fsetdec.
  Qed.

  Lemma can_push (fd : sfundef) to_save lo hi vm1  s1 m1' m1 :
    alloc_stack (emem s1) (sf_align (f_extra fd)) (sf_stk_sz (f_extra fd)) (sf_stk_ioff (f_extra fd))
         (sf_stk_extra_sz (f_extra fd)) = ok m1'
    → (0 <= sf_stk_sz (f_extra fd))%Z
    → (0 <= sf_stk_extra_sz (f_extra fd))%Z
    → (hi <= sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd))%Z
    → let top := top_stack_after_alloc (top_stack (emem s1)) (sf_align (f_extra fd))
                      (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd)) in
    (∀ al (s : word Uptr) (w : wsize) (s0 : word w) (m m0 : low_memory.mem),
          between top (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd)) s w
          → write m al s s0 = ok m0 → target_mem_unchanged m m0)
    → vm_initialized_on vm1 [seq i.1 | i <- to_save]
    → all_disjoint_aligned_between liparams lo hi (sf_align (f_extra fd)) to_save = ok tt
    → ∀ m2 : low_memory.mem,
        preserved_metadata s1 m1 m2
        (* Maybe this lemma is used only with m = m0 *)
        → (wunsigned (top_stack (emem s1)) <= wunsigned (top_stack m0))%Z
        → match_mem_gen (top_stack m0) s1 m2
        → target_mem_unchanged m1 m2
        → (sf_stk_sz (f_extra fd) <= lo)%Z
        → ∃ m3 : low_memory.mem,
            [/\ foldM (λ '(x, ofs) m,
                Let: ws := if vtype x is aword ws then ok ws else Error ErrType in
                Let _ := assert (lip_check_ws liparams ws) ErrType in
                Let: v := get_var true vm1 x >>= to_word ws in
                write m Aligned (top + wrepr Uptr ofs)%R v) m2 to_save = ok m3
              , preserved_metadata s1 m2 m3
              , match_mem_gen (top_stack m0) s1 m3
              & target_mem_unchanged m2 m3].
  Proof.
    move=> ok_m1' stk_sz_pos stk_extra_sz_pos hle_rsp top spill_unchanged.
    have can_spill := mm_can_write_after_alloc _ ok_m1' stk_sz_pos stk_extra_sz_pos.
    have topE : top_stack m1' = top.
    + by rewrite (alloc_stack_top_stack ok_m1').

    elim: to_save lo => [ sz' _ _ | [x ofs] to_save ih lo wf_to_save ok_to_save]
                m2 H2 hle M2 U2 sz'_le_lo /=.
    * exists m2; split => //; rewrite addn0; exact: rt_refl.
    move: wf_to_save; rewrite /vm_initialized_on /= => /andP [wf_x wf_to_save].
    case/all_disjoint_aligned_betweenP: ok_to_save => x_ofs [] ws [] [].
    move=> /check_to_save_slotP [xname ??]; subst x x_ofs.
    set x := {| vname := xname; |}.
    move=> hchk ofs_lo ok_ws aligned_ofs ok_to_save /=.
    move/is_okP: wf_x => /= -[w]; t_xrbindP => v get_x ok_w.
    rewrite get_x /= ok_w /=.
    have := can_spill _ ofs _ w ok_ws aligned_ofs _ _ hle M2.
    have ofs_hi:
      (ofs + wsize_size ws <= sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd))%Z.
    + have := all_disjoint_aligned_between_range ok_to_save.
      move: hle_rsp. assert (H := wsize_size_pos Uptr).
      move: (sf_stk_sz _) (sf_stk_extra_sz _) => ?; lia.
    case=> //.
    * etransitivity; last exact: ofs_lo.
      etransitivity; last exact: sz'_le_lo.
      assert (h := wsize_size_pos Uptr).
      move: (sf_stk_sz _) => ?; lia.

    rewrite topE => acc [] ok_acc Hacc ACC.
    have Hacc' : preserved_metadata s1 m1 acc.
    * transitivity m2; assumption.
    have Uacc: target_mem_unchanged m2 acc.
    + apply: spill_unchanged ok_acc.
      rewrite /between /zbetween !zify.
      rewrite wunsigned_add; first by lia.
      have := (alloc_stackP ok_m1').(ass_above_limit); rewrite topE.
      have := wunsigned_range top.
      have := [elaborate (wunsigned_range (top_stack (emem s1)))].
      have := wsize_size_pos ws.
      by lia.
    have Uacc': target_mem_unchanged m1 acc.
    + transitivity m2; assumption.
    have ofs_lo': (sf_stk_sz (f_extra fd) <= ofs + wsize_size ws)%Z.
    * move: (sf_stk_sz _) sz'_le_lo ofs_lo (wsize_size_pos ws) => /=; lia.
    have {ih} := ih _ wf_to_save ok_to_save _ Hacc' hle ACC Uacc' ofs_lo'.
    case => m3 [] ok_m3 H3 M3 U3; rewrite hchk /=.
    exists m3; split.
    * rewrite ok_acc; exact: ok_m3.
    * transitivity acc; assumption.
    * exact: M3.
    transitivity acc; assumption.
  Qed.

  Lemma all_disjoint_range lo hi al to_save :
    all_disjoint_aligned_between liparams lo hi al to_save = ok tt ->
    forall x ofs ws,
      (x, ofs) \in to_save ->
      vtype x = aword ws ->
      (lo <= ofs /\ ofs + wsize_size ws <= hi)%Z.
  Proof.
    elim: to_save lo => //.
    move=> [x1 ofs1] to_save ih lo /all_disjoint_aligned_betweenP.
    move=> [] ofs1' [] ws1' [] [] /=.
    case heq: is_word_type => [ws1 | ] // [??]; subst ofs1' ws1'.
    move=> _ hlo _ _ /[dup] {}/ih ih /all_disjoint_aligned_between_range ?.
    move=> x ofs ws; rewrite in_cons => /orP [/eqP [-> ->] | hin] ht.
    + by move: heq; rewrite ht => -[->].
    have := ih _ _ _ hin ht; have := (@le0_wsize_size ws1); lia.
  Qed.
(* FIXME: move this *)
Lemma mix_ilsteps_split_in_fn P lc lbody fn ls :
  is_linear_of fn lbody ->
  size P + size lc <= size lbody ->
  mix_ilsteps p' (in_fn p' fn) ls ≅
  ITree.bind (mix_ilsteps p' (pc_between_c fn P lc) ls)
       (mix_ilsteps p' (in_fn p' fn)).
Proof.
  move=> [fd ok_fd <-] hsz.
  apply while.split_while_imp => {} ls.
  rewrite /pc_between_c /pc_between /in_fn /endpc eq_sym.
  case: ifP => // _; rewrite ok_fd /= => h.
  apply /eqP. move: hsz h; simpl_size; lia.
Qed.

  Lemma linear_funP fn1 fn2 :
    wkequiv_io
      (preF fn1 fn2)
      (isem_fun_check var_tmps p fn1)
      (mix_ilsem_fun p' fn2)
      (postF fn1 fn2).
  Proof.
    move=> s1 ls1 hpre /=.
    rewrite /isem_fun /isem_fun_def /mix_ilsem_fun.
    have {}hpre: PreF (RecCallK fn1 s1) (mix_to_small_steps.Call fn2 ls1) by done.
    apply: (xrutt_facts.mrec_xrutt (RPreInv:= @PreF) (RPostInv := @PostF) _ hpre).
    move=> {fn1 fn2 s1 ls1 hpre} R1 R2 d1 d2 hpreF.
    set sem := (handle_recCallK _ _ _).
    have :
      xrutt.xrutt (errcutoff (is_error (FIso_suml recCallK (Err:=ErrEvent)))) nocutoff EPreRel EPostRel
         (λ (v1 : R1) (v2 : R2), PostF d1 v1 d2 v2)
         sem (handle_call p' d2); rewrite /sem => {sem}; last first.
    + apply xrutt_facts.xrutt_weaken => //.
      + move=> T1 e1; rewrite /errcutoff /= /xrutt_facts.EE_MR.
        by case: e1 => //= e; rewrite /is_error /=; case: mfun1.
      + move=> T1 T2 e1 e2; rewrite /EPreRel sum_prerelP.
        case: e1 e2 => [ [fn1 fs1] | e1] [ [fn2 fs2] | e2] //=.
        + by case : mfun1. + by case : mfun1.
        by case: mfun1 => // ?; case: mfun1.
      move=> T1 T2 e1 t1 e2 t2; rewrite /EPostRel sum_postrelP.
      case: e1 t1 e2 t2 => [ [fn1 fs1] | e1] t1 [ [fn2 fs2] | e2] t2 //=.
      by case: mfun1 => // ?; case: mfun1.
    move: R1 R2 d1 d2 hpreF.
    move=> _ _ [fn s1] [_ t1] [<-] /= => hscs M hfn S MAX.
    move=> [body] [ra] [lret] [sp] [callee_saved] []hlin hisra X hvalofra hcaller hpc hissp hiscalleesaved wf_to_save ok_m0.
    rewrite /isem_fun_body.
    case ok_fd : get_fundef => [fd | ] /=; last first.
    + rewrite bind_throw; apply xrutt.xrutt_CutL.
      by rewrite /xrutt_facts.EE_MR /core_logics.errcutoff /is_error /subevent /resum /fromErr /= mid12.
    rewrite bind_ret_l.
    move: hlin hisra hvalofra hpc X hissp hiscalleesaved wf_to_save ok_m0.
    rewrite /is_linear_of /is_ra_of /value_of_ra /is_sp_for_call /is_callee_saved_of ok_fd.
    move=> [fd' ok_fd' ?] [_ [<-] <-] ok_lret hpc X [_ [<-] ok_sp] [_ [<-]] ok_callee_saved wf_to_save ok_m0; subst body.
    case hvalid_init : (saved_stack_valid_init p fd) => /=; last first.
    + rewrite bind_throw; apply xrutt.xrutt_CutL.
      by rewrite /xrutt_facts.EE_MR /core_logics.errcutoff /is_error /subevent /resum /fromErr /= mid12.
    rewrite bind_ret_l.
    case heq: (initialize_funcall var_tmps p fd s1) => [s' | err] /=; last first.
    + rewrite bind_throw; apply xrutt.xrutt_CutL.
      by rewrite /xrutt_facts.EE_MR /core_logics.errcutoff /is_error /subevent /resum /fromErr /= mid12.
    rewrite bind_ret_l.
    move: heq; rewrite /initialize_funcall; t_xrbindP => /andP [] rsp_aligned valid_rsp m1' /map_errP ok_m1' ?; subst s'.
    have A := alloc_stackP ok_m1'.
    move: (checked_prog ok_fd); rewrite /check_fd /=.
    t_xrbindP => chk_body ok_to_save _ _ ok_stk_sz ok_ret_addr ok_save_stack _.
    case/and4P: ok_stk_sz => /lezP stk_sz_pos /lezP stk_extra_sz_pos /ltzP frame_noof /lezP stk_frame_le_max.
    have ? : fd' = (linear_fd fn fd).2.
    - have := get_fundef_p' ok_fd.
      by rewrite ok_fd' => /Some_inj.
    subst fd'.
    move: ok_fd'; rewrite /linear_fd /linear_body /=.
    rewrite /check_to_save in ok_to_save.
    rewrite /ra_undef /ra_vm.
    rewrite /saved_stack_vm.
    rewrite /finalize_funcall /ra_valid /saved_stack_valid => {ra}.

    have ih := @linear_cP fn (f_body fd).
    case EQ: sf_return_address ok_to_save ok_callee_saved ok_save_stack ok_ret_addr X ok_lret ih ok_sp
      =>
      /= [ | ra ? | ra_call ra_return rastack ? ]
      ok_to_save ok_callee_saved ok_save_stack ok_ret_addr X ok_lret ih.
    2-3: case => sp_aligned.
    all: move => ?; subst sp.
    - (* Export function *)
    { case: lret ok_lret hpc {hcaller} => // _ hpc.
      subst callee_saved.
      case E1: sf_save_stack ok_save_stack ok_to_save ih =>
      [ | saved_rsp | stack_saved_rsp ] /= ok_save_stack ok_to_save ih ok_fd'.
      + (* No need to save RSP *)
      {
        move: ok_fd'; case heq : (linear_c _) => [lbl lbody] /= ok_fd'.
        have ok_body : is_linear_of fn ([::] ++ lbody ++ [::]).
        + rewrite /is_linear_of ok_fd' cats0; eexists; reflexivity.
        have /ih{}ih : pre_c fn (f_body fd) 1 lbl [::] lbody [::].
        + by rewrite /pre_c /checked_c ok_fd chk_body.
        rewrite (mix_ilsteps_split_in_fn (P:=[::]) (lc:=lbody) _ ok_body); last by rewrite cats0.
        rewrite /isem_cmd.
        set ks1 := (X in isem_cmd_ _ _ _ X).
        have hle: (wunsigned (top_stack (emem s1)) <= wunsigned (top_stack m0))%Z.
        + by have := ok_m0; rewrite EQ /= => <-; apply Z.le_refl.
        case/and4P: ok_save_stack => /eqP to_save_nil /eqP sf_align_1 /eqP stk_sz_0 /eqP stk_extra_sz_0.
        have top_stack_preserved : top_stack m1' = top_stack (s1: mem).
        + rewrite (alloc_stack_top_stack ok_m1') sf_align_1.
          rewrite top_stack_after_aligned_alloc.
          2: exact: is_align8.
          by rewrite stk_sz_0 stk_extra_sz_0 -addE add_0.
        have /ih{}ih : inv_c fn [::] ks1.2 t1.
        + split => //=.
          + by apply: mm_alloc hle M ok_m1'.
          + apply: vm_uincl_kill_vars_set_incl X => //.
            + by rewrite /ra_undef /ra_vm EQ /=; clear; SvD.fsetdec.
            by rewrite top_stack_preserved.
          + by rewrite Vm.setP_eq vm_truncate_val_eq top_stack_preserved.
          + move=> pr /=.
            rewrite A.(ass_valid) top_stack_preserved.
            have ->: (sf_stk_sz (f_extra fd) - sf_stk_ioff (f_extra fd) = 0)%Z.
            + have := A.(ass_ioff); rewrite stk_sz_0 /=.
              by lia.
            rewrite /between (negbTE (not_zbetween_neg _ _ _ _)) // orbF.
            exact: S.
          move=> fd''; rewrite ok_fd => -[?]; subst fd''.
          have /= := MAX _ ok_fd.
          rewrite /align_top_stack /align_top -(alloc_stack_top_stack ok_m1').
          rewrite top_stack_preserved.
          rewrite /frame_size EQ /= stk_sz_0 stk_extra_sz_0 /= -addE add_0.
          move=> [_ [-> ?]]; lia.
        apply: (xrutt_facts.xrutt_bind ih).
        move=> ks2 ls2 [] [] M2 SC2 X2 hpc2 hfn2 RSP2 S2 Max_sub2 hdisj2 hsub2 K2 hvalid hstable H2 U2.
        rewrite mix_ilsteps_0; last first.
        + by rewrite /in_fn /endpc hfn2 hpc2 eqxx ok_fd' /= eqxx.
        apply xrutt_bind_iresult_left; t_xrbindP.
        move=> _ valid_rsp2 <- /=.
        apply xrutt_bind_iresult_left; t_xrbindP => /stack_stableP SS.
        apply xrutt.xrutt_Ret; rewrite /postF /=.
        move=> body ra lret sp callee_saved; rewrite /is_linear_of ok_fd' /= => -[ _ [<-] <-].
        rewrite /is_ra_of /value_of_ra /is_sp_for_call /is_callee_saved_of ok_fd => -[_ [<-] <-].
        rewrite EQ; case: lret => // _ -[_ [<-]] + [_ [<-]]; rewrite EQ /= => -> ->; split => //.
        + by apply: alloc_free_validw_stable A hstable hvalid (free_stackP ks2.2).
        + move => x; move: (X2 x); rewrite /set_RSP !Vm.setP kill_varsE Vm.setP.
          case: eqP => ?; subst.
          + by rewrite RSP2 vm_truncate_val_eq /sp_alloc_ra //= -(ss_top_stack hstable) top_stack_preserved.
          case: Sv.mem.
          + by move=> _; apply compat_value_uincl_undef; apply Vm.getP.
          rewrite kill_varsE; case: Sv.mem => // _.
          by apply compat_value_uincl_undef; apply Vm.getP.
        + apply: eq_exI; last exact: K2.
          by rewrite to_save_nil Sv_diff_empty; clear; SvD.fsetdec.
        + move => a a_range /negbTE nv.
          have [L] := ass_above_limit A.
          rewrite stk_sz_0 => H.
          apply: H2.
          * rewrite (ass_root A) /=; lia.
          rewrite (ass_valid A) nv /= !zify => - [].
          change (wsize_size U8) with 1%Z.
          rewrite (ass_add_ioff A).
          have := ass_ioff A.
          move: (sf_stk_sz _) (sf_stk_extra_sz _) (sf_stk_ioff _) stk_sz_0 stk_extra_sz_0 H.
          lia.
        apply: mm_free M2.
      }
      + (* RSP is saved into register “saved_rsp” *)
      { move: ok_fd' hvalid_init; rewrite linear_c_nil /saved_stack_valid_init /saved_stack_valid_final E1.
        case: saved_rsp ok_save_stack E1 => stty saved_stack /=.
        set ri := vid saved_stack.
        move=> /and3P[] hc /eqP to_save_empty hnot_saved_stack E1.
        case heq : (linear_c _) => [lbl lbody] /=.
        set P := (P in {|lfd_body := P ++ _|}); set Q := (Q in {|lfd_body := _ ++ _ ++ Q|}).
        move => ok_fd' /andP [] /eqP saved_stack_not_GD /eqP saved_stack_not_RSP.
        have ok_body : is_linear_of (lfn t1) (P ++ lbody ++ Q).
        + by rewrite hfn /is_linear_of ok_fd' /=; eauto.
        have /ih{}ih : pre_c fn (f_body fd) 1 lbl P lbody Q.
        + rewrite /pre_c /checked_c ok_fd chk_body; split => //.
          + by move => lbl' _; rewrite /P /= set_up_sp_register_has_label.
          by rewrite -hfn.
        have ok_rsp : get_var true (lvm t1) vrsp = ok (Vword (top_stack (emem s1))).
        + move: (X vrsp); rewrite Vm.setP_eq vm_truncate_val_eq // /get_var.
          by move=> /get_word_uincl_eq -/(_ (subctype_refl _)) ->.
        have  [|vm [hsem hvm hgetrsp hgetr hflags]] :=
          set_up_sp_register_ok
            hliparams
            (P := [::])
            ok_body
            hpc
            ok_rsp
            hc erefl
            hneq_vtmp_vrsp
            saved_stack_not_RSP _.
        + by move=> [_ h]; move: hnot_saved_stack; rewrite h eqxx.
        rewrite hfn in ok_body.
        rewrite (mix_ilsteps_split_in_fn (P:=[::]) (lc:=P) _ ok_body); last by simpl_size; lia.
        move: hsem; rewrite /= -/P hfn /pc_between_c hpc => ->.
        rewrite bind_ret_l.
        rewrite (mix_ilsteps_split_in_fn (P:=P) (lc:=lbody) _ ok_body); last by simpl_size; lia.
        set s1' := {| escs := _ |}.
        set ks1' := (Sv.empty, s1').
        set ls1 := (setpc _ _).
        have hle: (wunsigned (top_stack (emem s1)) <= wunsigned (top_stack m0))%Z.
        + by have := ok_m0; rewrite EQ /= => <-; apply Z.le_refl.
        have /ih{}ih : inv_c fn P ks1'.2 ls1.
        + split => //=.
          + by apply: mm_alloc hle M ok_m1'.
          + apply: (vm_uincl_after_alloc_stack X EQ _ hgetrsp ok_m1').
            rewrite /= E1 /= -SvP.MP.add_union_singleton.
            by apply: eq_exI hvm; rewrite /vrsp => /=; clear; SvD.fsetdec.
          + by rewrite /ra_undef_vm  Vm.setP_eq vm_truncate_val_eq.
          + move=> pr /=.
            move=> hvalid; apply /orP; move: hvalid.
            rewrite A.(ass_valid).
            move=> /orP [/S /orP [hvalid | hpr] | hb]; [by left | right..].
            + apply: pointer_range_incl_l hpr.
              by have /= := A.(ass_above_limit); lia.
            rewrite pointer_range_between.
            apply: zbetween_trans hb.
            rewrite /zbetween !zify.
            have /= hioff := A.(ass_ioff).
            have /= habove := A.(ass_above_limit).
            have hrange1 := [elaborate wunsigned_range (top_stack m1')].
            have hrange2 := [elaborate wunsigned_range (top_stack (emem s1))].
            rewrite wunsigned_add; last by lia.
            have := MAX _ ok_fd.
            rewrite EQ /= /align_top_stack /align_top -(alloc_stack_top_stack ok_m1').
            move=> [_ [-> _]].
            by rewrite wunsigned_add; lia.
          move=> fd''; rewrite ok_fd => -[?]; subst fd''.
          have := MAX _ ok_fd.
          rewrite /frame_size EQ /= /align_top_stack /align_top -(alloc_stack_top_stack ok_m1').
          move=> [? [-> _]].
          rewrite wunsigned_add; first by lia.
          have /= habove := A.(ass_above_limit).
          have hrange1 := [elaborate wunsigned_range (top_stack m1')].
          have hrange2 := [elaborate wunsigned_range (top_stack (emem s1))].
          by lia.
        apply: (xrutt_facts.xrutt_bind ih).
        move=> ks2 ls2 [] [] M2 SC2 X2 hpc2 hfn2 RSP2 S2 Max_sub2 hdisj2 hsub2 K2 hvalid hstable H2 U2.
        apply xrutt_bind_iresult_left; t_xrbindP => _ + <- /=.
        move=> /andP [] /Sv_memP saved_stack_not_written _.
        apply xrutt_bind_iresult_left; t_xrbindP =>  /stack_stableP SS.
        rewrite (mix_ilsteps_split_in_fn (P:=P ++ lbody) (lc:=Q) _ ok_body); last by simpl_size; lia.
        rewrite catA in ok_body.
        rewrite (step_mix_ilsteps ok_body) //=; last by simpl_size;lia.
        have hgetr2 : get_var true (lvm ls2) (mk_var_i {| vtype := stty; vname := saved_stack|}) = ok (Vword (top_stack (emem s1))).
        + rewrite  -(get_var_eq_ex _ saved_stack_not_written K2); exact: hgetr.
        rewrite (@spec_lmove _ hliparams p' _ ls2
                  (vid (sp_rsp (p_extra p))) (mk_var_i {| vtype := stty; vname := saved_stack|}) _
                  erefl hc hgetr2).
        rewrite mix_ilsteps_b0 => //; last by rewrite /lnext_pc /= hpc2 addn1.
        rewrite bind_ret_l mix_ilsteps_0; last first.
        + by rewrite /in_fn /endpc /lnext_pc /= hfn2 eqxx ok_fd' /= hpc2 catA !size_cat /Q /= addn1 eqxx.
        apply xrutt.xrutt_Ret.
        move=> body ra lret sp callee_saved; rewrite /is_linear_of ok_fd' /= => -[ _ [<-] <-].
        rewrite /is_ra_of /value_of_ra /is_sp_for_call /is_callee_saved_of ok_fd => -[_ [<-] <-].
        rewrite EQ; case: lret => // _ -[_ [<-]] + [_ [<-]]; rewrite EQ /= => -> ->; split => //.
        + by apply: alloc_free_validw_stable A hstable hvalid (free_stackP ks2.2).
        + move => x; rewrite Vm.setP kill_varsE; case: eqP => ?.
          * by subst; rewrite Vm.setP_eq.
          rewrite Vm.setP_neq; last by apply /eqP.
          rewrite /set_RSP Vm.setP_neq; last by apply/eqP.
          case: Sv.mem.
          + by apply compat_value_uincl_undef; apply Vm.getP.
          rewrite kill_varsE; case: Sv.mem => //.
          by apply compat_value_uincl_undef; apply Vm.getP.
        + rewrite to_save_empty Sv_diff_empty.
          rewrite /ra_undef /ra_vm /saved_stack_vm EQ E1.
          clear - ok_rsp K2 hvm.
          move => x.
          rewrite !Sv.union_spec !Sv.add_spec !Sv.singleton_spec Vm.setP.
          move=> /Decidable.not_or[] x_not_k
            /Decidable.not_or[] /Decidable.not_or[] /Decidable.not_or[]
            x_not_tmp x_not_flags x_not_saved_stack _.
          case: eqP => x_rsp.
          * by subst; move/get_varP: ok_rsp => [<-]; rewrite vm_truncate_val_eq.
          rewrite -K2; last exact: x_not_k.
          rewrite /ls1 /= hvm; first done.
          move: x_rsp; rewrite /mk_var_i /=; SvD.fsetdec.
        + rewrite hpc2 /Q; simpl_size; lia.
        + move => a [] a_lo a_hi /negbTE nv.
          have /= [L H] := ass_above_limit A.
          apply: H2.
          * by rewrite (ass_root A) /=; lia.
          rewrite (ass_valid A) nv /= !zify => - [].
          rewrite (ass_add_ioff A).
          change (wsize_size U8) with 1%Z.
          have := ass_ioff A.
          move: (sf_stk_sz _) (sf_stk_extra_sz _) (sf_stk_ioff _) H => ???.
          lia.
        exact: mm_free.
      }
      (* RSP is saved in stack at offset “stack_saved_rsp” *)
      { move: ok_fd'; rewrite linear_c_nil /saved_stack_valid_init /saved_stack_valid_final E1.
        case heq : (linear_c _) => [lbl lbody] /=.
        set cmd_set_up_sp := set_up_sp_register _ _ _ _ _ _.
        set cmd_push_to_save := push_to_save _ _ _ _ _.
        set P := cmd_set_up_sp ++ cmd_push_to_save.
        set Q := (X in lbody ++ X).
        move => ok_fd'.
        have ok_body : is_linear_of (lfn t1) (P ++ lbody ++ Q).
        + by rewrite hfn /is_linear_of ok_fd' /=; eauto.
        have sz_nz : (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd) == 0)%Z = false.
        + move: ok_save_stack; clear - stk_sz_pos stk_extra_sz_pos; rewrite !zify => - [] [] C [] D _ _.
          apply/eqP.
          by have /= := [elaborate wsize_size_pos Uptr]; lia.
        have ok_rsp : get_var true (lvm t1) vrsp = ok (Vword (top_stack (emem s1))).
        + move: (X vrsp); rewrite Vm.setP_eq /get_var /= cmp_le_refl.
          by move => /get_word_uincl_eq -/(_ (subctype_refl _)) ->.
        have can_spill := mm_can_write_after_alloc _ ok_m1' stk_sz_pos stk_extra_sz_pos.
        set top := (top_stack_after_alloc (top_stack (emem s1)) (sf_align (f_extra fd)) (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd))).
        have topE : top_stack m1' = top.
        + by rewrite (alloc_stack_top_stack ok_m1').
        set ts := top_stack (emem s1).

        move: ok_to_save; t_xrbindP => /ZleP hle_rsp ok_to_save.

        move: ok_save_stack => /and4P [h tmp_not_saved tmp2_not_saved rsp_not_saved].
        move: h =>
          /and4P []
          /lezP rsp_slot_lo
          /lezP rsp_slot_hi
          aligned_frame
          rsp_slot_aligned.

        (* the frame is inside the stack *)
        have hb1:
          zbetween (sp0 - wrepr _ max0) max0
          top (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd)).
        + rewrite /zbetween !zify.
          rewrite wunsigned_sub; last by have := wunsigned_range sp0; lia.
          move: (MAX _ ok_fd) stk_frame_le_max.
          rewrite /frame_size EQ /= /align_top_stack /align_top -/top.
          move=> [? [-> _]].
          rewrite wunsigned_add; first by lia.
          have := A.(ass_above_limit); rewrite topE /=.
          have hrange1 := wunsigned_range top.
          have hrange2 := [elaborate wunsigned_range (top_stack (emem s1))].
          by lia.

        have spill_unchanged := target_mem_unchanged_store hb1.
        move: (ok_body); rewrite /P -catA => ok_body'.
        have [ | vm2 [hsem hvm2 hgetrsp htmp hflags]] :=
          set_up_sp_register_ok
            hliparams
            (ls := t1)
            (P := [::])
            ok_body'
            hpc
            ok_rsp
            (convertible_refl _) erefl
            hneq_vtmp2_vrsp
            hneq_vtmp_vrsp _.
        + by move=> []; apply: (spec_lip_tmp hliparams).
        rewrite hfn in ok_body.
        rewrite (mix_ilsteps_split_in_fn (P:=[::]) (lc:=cmd_set_up_sp) _ ok_body); last by simpl_size; lia.
        move: hsem; rewrite /pc_between_c hfn hpc /= => ->.
        rewrite bind_ret_l -/cmd_set_up_sp.
        have {}hgetrsp : get_var true vm2 vrspi = ok (Vword top).
        + by move: hgetrsp; rewrite /top -wrepr_opp.
        have D : disjoint_labels 1 lbl P.
        + move => lbl' _.
          rewrite /P has_cat /=.
          rewrite set_up_sp_register_has_label /=.
          exact: push_to_save_has_no_label.

        have is_ok_vm1_vm2 :
          forall x,
            Sv.mem x (sv_of_list fst (sf_to_save (f_extra fd)))
            -> is_ok (get_var true (lvm t1) x >>= of_val (eval_atype (vtype x)))
            -> is_ok (get_var true vm2 x >>= of_val (eval_atype (vtype x))).
        + move=> x hx ok_x.
          case: (SvP.MP.In_dec x (Sv.add var_tmp (Sv.add var_tmp2 (Sv.add vrsp vflags)))) => hin;
            last by rewrite /get_var (hvm2 _ hin).
          move: hin => /Sv.add_spec [? | hin].
          - by subst x; move: tmp_not_saved => /negP.
           move: hin => /Sv.add_spec [? | hin].
          - by subst x; move: tmp2_not_saved => /negP.
          move: hin => /Sv.add_spec [? | hin].
          - by subst x; rewrite hgetrsp /= truncate_word_u.
          rewrite /get_var; have := hflags _ hin.
          have := Vm.getP vm2 x; rewrite (vflagsP hin) => /compat_valEl [ -> /= h | [b ->]//].
          by move: ok_x; rewrite /get_var h.

        set to_save := sf_to_save (f_extra fd) ++ [:: (v_var var_tmp, stack_saved_rsp)].
        have ok_to_save1 : all_disjoint_aligned_between liparams
                   (sf_stk_sz (f_extra fd)) (stack_saved_rsp + wsize_size Uptr)
                   (sf_align (f_extra fd)) to_save = ok tt.
        + move:ok_to_save; rewrite /all_disjoint_aligned_between /to_save foldM_cat.
          t_xrbindP => ? -> /= -> /=.
          by rewrite aligned_frame /= rsp_slot_aligned /= (spec_lip_check_ws hliparams) /= Z.leb_refl.
        have wf_to_save1 : vm_initialized_on vm2 [seq i.1 | i <- to_save].
        + rewrite /vm_initialized_on /to_save map_cat all_cat /= htmp /= truncate_word_u /= andbT.
          apply/allP => x hx; apply is_ok_vm1_vm2; first by apply/Sv_memP/sv_of_listP.
          by apply: (allP wf_to_save).
        set ls1 := setpc _ _.
        have hntosave: ~~ Sv.mem (vid (lip_tmp2 liparams)) (sv_of_list fst to_save).
        + rewrite /to_save; apply /Sv_memP => /sv_of_listP.
          rewrite map_cat mem_cat in_cons in_nil orbF => /orP [].
          + by move=> /sv_of_listP; apply /Sv_memP.
          by move=> /eqP [] /= h; apply (spec_lip_tmp hliparams); rewrite h.
        have hle: (wunsigned (top_stack (emem s1)) <= wunsigned (top_stack m0))%Z.
        + by have := ok_m0; rewrite EQ /= => ->; apply Z.le_refl.
        case: (can_push ok_m1' stk_sz_pos stk_extra_sz_pos hle_rsp spill_unchanged
                  wf_to_save1 ok_to_save1 (m1:= lmem t1) (m2 := lmem t1) _ hle M _ (Z.le_refl _)) => // [m3 [ok_m3 H3 M3' U3]].
        have [] := spec_lip_lstores hliparams (rspi := vrspi) (s:= to_estate ls1) hntosave hneq_vtmp2_vrsp _ ok_m3.
        + by rewrite hgetrsp /= truncate_word_u.
        move=> vm2' hsem_push hvm2'.
        rewrite (mix_ilsteps_split_in_fn (P:=cmd_set_up_sp) (lc:=cmd_push_to_save) _ ok_body); last by simpl_size; lia.
        rewrite -hfn (sem_fopns_args_mix_ilsteps ok_body') // -/vrspi -/to_save; last first.
        + by rewrite /cmd_push_to_save /push_to_save size_map.
        rewrite hsem_push bind_ret_l.
        set ls2 := (of_estate (with_mem _ _) _ _) => {hsem_push}.
        rewrite hfn (mix_ilsteps_split_in_fn (P:=P) (lc:=lbody) _ ok_body); last by simpl_size; lia.
        have /ih{}ih : pre_c fn (f_body fd) 1 lbl P lbody Q.
        + split => //.
          by rewrite /checked_c ok_fd /= chk_body.
        set s2 := {| escs := _ |}.
        have vm2'_get_rsp : get_var true vm2' vrsp = ok (Vword top).
        + rewrite -(get_var_eq_ex _ _ hvm2') //.
          by move=> /Sv.singleton_spec h; apply hneq_vtmp2_vrsp; rewrite h.
        have /ih{}ih : inv_c fn P (Sv.empty, s2).2 ls2.
        + split => //.
          + by apply: mm_alloc hle M3' ok_m1'.
          + apply: (vm_uincl_after_alloc_stack X EQ _ _ ok_m1').
            + rewrite /savedstackreg E1 Sv_union_empty.
              apply: (eq_exT (vm2:=to_estate ls1)).
              + by apply/eq_exS;apply: eq_exI hvm2'; rewrite /var_tmps /var_tmp2; SvD.fsetdec.
              by apply: eq_exI hvm2; rewrite /var_tmps /= -/var_tmp -/vrsp; SvD.fsetdec.
            by rewrite vm2'_get_rsp /top /top_stack_after_alloc wrepr_opp.
          + by rewrite /ls2 /= /P size_cat.
          + by rewrite /s2 /= Vm.setP_eq vm_truncate_val_eq.
          + move=> pr /=.
            move=> hvalid; apply /orP; move: hvalid.
            rewrite A.(ass_valid).
            move=> /orP [/S /orP [hvalid | hpr] | hb]; [by left | right..].
            + apply: pointer_range_incl_l hpr.
              by have /= := A.(ass_above_limit); lia.
            rewrite pointer_range_between.
            apply: zbetween_trans hb.
            rewrite /zbetween !zify.
            have /= hioff := A.(ass_ioff).
            have /= habove := A.(ass_above_limit).
            have hrange1 := [elaborate wunsigned_range (top_stack m1')].
            have hrange2 := [elaborate wunsigned_range (top_stack (emem s1))].
            rewrite wunsigned_add; last by lia.
            have := MAX _ ok_fd.
            rewrite EQ /= /align_top_stack /align_top -(alloc_stack_top_stack ok_m1').
            move=> [_ [-> _]].
            by rewrite wunsigned_add; lia.
          move=> fd''; rewrite ok_fd => -[?]; subst fd''.
          have := MAX _ ok_fd.
          rewrite /frame_size EQ /= /align_top_stack /align_top -(alloc_stack_top_stack ok_m1').
          move=> [? [-> _]].
          rewrite wunsigned_add; first by lia.
          have /= habove := A.(ass_above_limit).
          have hrange1 := [elaborate wunsigned_range (top_stack m1')].
          have hrange2 := [elaborate wunsigned_range (top_stack (emem s1))].
          by lia.
        apply (xrutt_facts.xrutt_bind ih).
        move=> ks4 ls4 [] [] M4 SC4 X4 hpc4 hfn4 RSP4 S4 Max_sub4 hdisj4 hsub4 K4 hvalid hstable H4 U4.
        apply xrutt_bind_iresult_left; t_xrbindP => _ _ <- /=.
        apply xrutt_bind_iresult_left; t_xrbindP =>  /stack_stableP SS.
        rewrite (mix_ilsteps_split_in_fn (P:=P ++ lbody) (lc:=Q) _ ok_body); last by simpl_size; lia.
        have vm4_get_rsp : get_var true (lvm ls4) vrsp >>= to_pointer = ok top.
        + rewrite -(get_var_eq_ex _ _ K4).
          + by rewrite vm2'_get_rsp /= truncate_word_u.
          have /hdisj4 /disjointP K : disjoint Sv.empty (magic_variables p).
          + by apply /disjointP; clear; SvD.fsetdec.
          move => /K; apply; exact: RSP_in_magic.
        have top_no_overflow1 : (wunsigned top + (stack_saved_rsp + wsize_size Uptr) < wbase Uptr)%Z.
        + apply: Z.le_lt_trans; last exact: proj2 (wunsigned_range (top_stack (emem s1))).
          etransitivity; last exact: (proj2 A.(ass_above_limit)).
          rewrite topE; assert (h :=  wsize_size_pos Uptr).
          move: (sf_stk_sz _) (sf_stk_extra_sz _) hle_rsp => ?; lia.
        have top_no_overflow : (wunsigned top + stack_saved_rsp < wbase Uptr)%Z.
        + assert (h := wsize_size_pos Uptr); lia.
        have rsp_slot_pos : (0 <= stack_saved_rsp + wsize_size Uptr)%Z.
        + assert (h := wsize_size_pos Uptr); lia.
        have [read_in_m3 read_spilled] := read_after_spill top_no_overflow1 stk_sz_pos ok_to_save1 ok_m3.
        set to_restore := (sf_to_save (f_extra fd)) ++ [:: (vrsp, stack_saved_rsp)].
        have read_in_spilled :
          ∀ (x : var) (ofs : Z),
             (x, ofs) \in to_restore ->
             exists2 ws, vtype x = aword ws /\ lip_check_ws liparams ws &
             exists2 w: word ws, read m3 Aligned (top + wrepr Uptr ofs)%R ws = ok w &
                                 read (lmem ls4) Aligned (top + wrepr Uptr ofs)%R ws = ok w.
        + move=> x ofs hin.
          have [x' ht {}hin]: exists2 x', vtype x' = vtype x & (x', ofs) \in to_save.
          + move: hin; rewrite mem_cat /to_save => /orP -[ hin | ].
            + by exists x => //; rewrite mem_cat hin.
            rewrite in_cons /= orbF => /eqP [? <-]; subst x; exists var_tmp => //.
            by rewrite mem_cat in_cons eqxx orbT.
          case: (read_spilled x' ofs hin).
          rewrite ht => ws [] /is_word_typeP hws hchk [w _ hw]; exists ws => //; exists w => //.
          rewrite -hw; symmetry; apply: eq_read => al i i_range.
          move: hws; rewrite -ht => {}ht.
          have /(_ ofs) []:= all_disjoint_range ok_to_save1 _ ht; first done.
          move=> h1 h2;have /(_ ofs) [] := stack_slot_in_bounds ok_m1' _ _ i_range => //=; first lia.
          rewrite !(read8_alignment Aligned) => h3 h4; apply: (preserved_metadata_w ok_m1' H4); rewrite -topE; first lia.
          rewrite A.(ass_valid).
          apply/orP => - [].
          - move => /(ass_fresh_alt A); apply.
            rewrite !zify; lia.
          rewrite !zify.
          have [_] := A.(ass_above_limit).
          rewrite Z.max_r //.
          change (wsize_size U8) with 1%Z.
          rewrite (ass_add_ioff A). have := ass_ioff A.
          move: stk_sz_pos stk_extra_sz_pos h1 h2 h3 h4 => /=; lia.
        have [vm5 sem_loads]: exists vm5, foldM (λ '(x, ofs) vm,
           Let: ws := if vtype x is aword ws then ok ws else Error ErrType in
           Let _ := assert (lip_check_ws liparams ws) ErrType in
           Let w := read (lmem ls4) Aligned (top + wrepr Uptr ofs)%R ws in
           set_var true vm x (Vword w)) (lvm ls4) to_restore = ok vm5.
        + elim: to_restore (lvm ls4) read_in_spilled => /= [ | [x ofs] to_restore {}ih] vm4' read_in_spilled; first by eauto.
          have [ws [ht hchk] [w _ hr]] := read_in_spilled _ _ (mem_head _ _).
          rewrite ht /= hchk /= hr /= set_var_eq_type // ?ht //=; apply ih.
          by move=> y yofs hin; apply read_in_spilled; rewrite in_cons hin orbT.
        have {}ok_body' : is_linear_of fn ((P ++ lbody) ++ Q ++ [::]).
        + by rewrite cats0 -!catA -hfn.
        rewrite (sem_fopns_args_mix_ilsteps ok_body') // -/vrspi -/to_save; last first.
        + by rewrite /Q /pop_to_save size_map.
        have [vm5' sem_op_loads E5]:=
          spec_lip_lloads hliparams (rspi := vrspi) (s:= to_estate ls4) rsp_not_saved tmp2_not_saved hneq_vtmp2_vrsp
            vm4_get_rsp sem_loads.
        rewrite sem_op_loads bind_ret_l.
        rewrite mix_ilsteps_0; last first.
        + by rewrite /in_fn /endpc ok_fd' /= eqxx catA !size_cat eqxx.
        apply xrutt.xrutt_Ret.
        have hvm5:
          forall x, if x \in (map fst to_restore) then
                    exists ofs ws w,
                      [/\ vtype x = aword ws
                        , (x, ofs) \in to_restore
                        , read (lmem ls4) Aligned (top + wrepr Uptr ofs)%R ws = ok w
                        & vm5.[x] = Vword w ]
                     else
                       vm5.[x] = (lvm ls4).[x].
        + move=> y; elim: (to_restore) (lvm ls4) sem_loads => /= [ | [x ofs] to_rest {}ih] vm.
          + by move=> [<-].
          case ht: vtype => [|||ws'] //=; t_xrbindP => vm' hchk w hr /set_varP [_ _ hvm] /ih /=.
          rewrite in_cons; case: ifP => hin.
          + rewrite orbT => -[yofs] [yws] [yw] [h1 h2 h3 h4].
            by exists yofs, yws, yw; split => //; rewrite in_cons h2 orbT.
          rewrite hvm Vm.setP eq_sym => ->.
          case: eqP => /= [-> | //].
          exists ofs, ws', w; split => //; first by apply mem_head.
          by rewrite ht /= cmp_le_refl.
        have {hvm5} hvm5' :
          forall x, vm5'.[x] = if x == var_tmp2 then vm5'.[x] else
                               if x \in map fst (sf_to_save (f_extra fd)) then vm2.[x]
                               else if x == vrsp then Vword ts else (lvm ls4).[x].
        + move=> x; case: eqP => // hxtmp2.
          move: (hvm5 x) (read_in_spilled x).
          rewrite /to_restore /to_save map_cat mem_cat /= in_cons in_nil orbF -E5; last first.
          + by move /Sv.singleton_spec/hxtmp2.
          case: (boolP (x \in map _ _)) => /=.
          + move=> hin [ofs [ws [w [htx hin' hr4 ->]]]] /(_ _ hin'); rewrite htx.
            move=> [_ [[<-] _]]; rewrite hr4 => -[w' hr3 [?]]; subst w'.
            move: hin'; rewrite mem_cat in_cons in_nil orbF => /orP []; last first.
            + move=> /eqP [??]; subst x.
              by move: rsp_not_saved; rewrite sv_of_listE hin.
            move=> hin'; have := read_spilled x ofs.
            rewrite mem_cat hin' => -[] //; rewrite htx.
            move=> _ [[<-] _]; rewrite hr3 => -[] w'; t_xrbindP.
            move=> v /get_varP [<-] _; rewrite htx.
            move=> hcomp /to_wordI [ws'] [w''] [? htr ?]; subst w' v.
            move: hcomp; rewrite /compat_val /= => hle'.
            by move/truncate_wordP: htr => [] /(cmp_le_antisym hle') ? ->; subst ws'; rewrite zero_extend_u.
          move=> hnin; case: eqP => [? | //].
          subst x; move=> [ofs [ws [w [[?] hin' hr4 ->]]]]; subst ws.
          move: hin'; rewrite mem_cat => /orP [].
          + by move=> /(map_f fst); rewrite (negbTE hnin).
          rewrite in_cons in_nil orbF => /eqP [?]; subst ofs.
          move=> /(_ stack_saved_rsp); rewrite mem_cat mem_head orbT => -[] //.
          move=> _ [[<-] _] [w'] hr3; rewrite hr4 => -[?]; subst w'.
          have := read_spilled var_tmp stack_saved_rsp.
          rewrite mem_cat mem_head orbT => -[] // _ [[<-] _] [v].
          by rewrite htmp /= truncate_word_u hr3 => -[<-] [->].
        have vrsp_to_save : vrsp \in [seq i.1 | i <- sf_to_save (f_extra fd)] = false.
        + by apply/negbTE/sv_of_listP/Sv_memP.
        move=> body ra lret sp callee_saved. rewrite /is_linear_of /sp_alloc_ra ok_fd' /= => -[ _ [<-] <-].
        rewrite /is_ra_of /value_of_ra /is_sp_for_call /is_callee_saved_of ok_fd => -[_ [<-] <-].
        rewrite EQ; case: lret => // _ -[_ [<-]] + [_ [<-]]; rewrite EQ /= => -> ->; split => //.
        + by apply: alloc_free_validw_stable A hstable hvalid (free_stackP ks4.2).
        + move => x; rewrite !Vm.setP kill_varsE Vm.setP hvm5' (eq_sym x); case: eqP => x_rsp.
          + subst x. move/eqP/negbTE: hneq_vtmp2_vrsp => ->.
            by rewrite vrsp_to_save /= cmp_le_refl eqxx.
          rewrite Sv_mem_add sv_of_listE map_id eq_sym /=.
          case: eqP.
          + by move=> ?; subst x; apply compat_value_uincl_undef; apply Vm.getP.
          move/eqP/negbTE: x_rsp; rewrite eq_sym => -> _ /=.
          case: ifP => _.
          + by apply compat_value_uincl_undef; apply Vm.getP.
          rewrite kill_varsE; case: Sv.mem => //.
          by apply compat_value_uincl_undef; apply Vm.getP.
        + move => x /Sv_memP; rewrite hvm5'.
          rewrite /ra_undef /ra_vm /saved_stack_vm EQ E1 /=.
          rewrite SvP.diff_mem negb_and => /orP[]; last first.
          * move/negbNE; rewrite sv_of_list_map.
            have -> : (id \o fst) = fst by done.
            move=> /[dup] hin; rewrite sv_of_listE => hin'.
            have -> : (x == var_tmp2) = false.
            + by apply/negbTE/eqP => ?; subst x; rewrite hin in tmp2_not_saved.
            rewrite hin' hvm2 // => /Sv.add_spec [?| /Sv.add_spec [?| /Sv.add_spec [?| ]]].
            + by subst x; move: tmp_not_saved; rewrite hin.
            + by subst x; move: tmp2_not_saved; rewrite hin.
            + by subst x; move: rsp_not_saved; rewrite hin.
            move=> /vflagsP hxty.
            move/mapP: hin' => -[[] /= a ofs hinx ?]; subst a.
            have := read_spilled x ofs; rewrite /to_save mem_cat hinx => -[] //.
            by rewrite hxty => ? [].
          rewrite !SvP.union_mem Sv_mem_add SvP.empty_mem SvP.MP.singleton_equal_add.
          rewrite Sv_mem_add SvP.empty_mem !orbA !orbF -!orbA.
          case/norP => x_ni_k /norP[] x_neq_tmp2 /norP[] x_neq_tmp /norP[] x_not_flag _.
          rewrite (negbTE x_neq_tmp2).
          case: eqP => ?.
          + by subst x; rewrite vrsp_to_save; move/get_varP: ok_rsp => -[<- _ _].
          transitivity vm2.[x].
          + rewrite hvm2 // => /Sv.add_spec [?| /Sv.add_spec [?|]].
            * by subst x; move: x_neq_tmp => /eqP.
            * by subst x; move: x_neq_tmp2 => /eqP.
            by move=> /Sv.add_spec [? |]; [ subst x | apply/Sv_memP].
          case: ifPn => // hnin.
          transitivity vm2'.[x]; last by apply/K4/Sv_memP.
          apply: hvm2'; rewrite -/var_tmp2 => /Sv.singleton_spec ?; subst x.
          by move: x_neq_tmp2; rewrite eqxx.
        + by rewrite catA !size_cat.
        + etransitivity; [exact: H3 | ].
          exact: preserved_metadata_alloc ok_m1' H4.
        + exact: mm_free M4.
        etransitivity; [exact: U3 | exact: U4].
      }
    }
    - (* Internal function, return address in register “ra” *)
    { case: lret ok_lret hpc hcaller => // - [] [] [] caller lret cbody pc.
      move=> [] ok_cbody ok_pc mem_lret [] retptr ok_retptr ok_ra hpc /= hcaller.
      rewrite linear_c_nil.
      case heq: (linear_c fn) => [lbl lbody] /=.
      set P := (P in P :: lbody ++ _).
      set Q := (Q in P :: lbody ++ Q).
      move => ok_fd'.
      have ok_body : is_linear_of fn ([:: P ] ++ lbody ++ Q).
      + by rewrite /is_linear_of ok_fd'; eauto.
      have /ih{}ih : pre_c fn (f_body fd) 2 lbl [::P] lbody Q.
      + split => //.
        + by rewrite /checked_c ok_fd /= chk_body.
        by move => q [L H]; rewrite /P /is_label /= orbF; apply/eqP => ?; subst; lia.
      set s1' := {| escs := _ |}.
      set ks1 := (Sv.empty, s1').
      have hrsp: (set_RSP p m1' (kill_vars (ra_undef fd var_tmps) s1)).[vrsp] = Vword (top_stack m1').
      + by rewrite Vm.setP_eq vm_truncate_val_eq.

      have /ih{}ih : inv_c fn [::P] ks1.2 t1.
      + split => //.
        + have hle: (wunsigned (top_stack (emem s1)) <= wunsigned (top_stack m0))%Z.
          + by have := MAX _ ok_fd; rewrite EQ /=; lia.
          by apply: mm_alloc hle M ok_m1'.
        + apply: vm_uincl_kill_vars_set_incl X => //.
          + by rewrite /ra_undef /ra_vm EQ; SvD.fsetdec.
          rewrite (alloc_stack_top_stack ok_m1') top_stack_after_aligned_alloc;  last by exact: sp_aligned.
          by rewrite wrepr_opp -/(stack_frame_allocation_size fd.(f_extra)).
        + move=> pr /=.
          move=> hvalid; apply /orP; move: hvalid.
          rewrite A.(ass_valid).
          move=> /orP [/S /orP [hvalid | hpr] | hb]; [by left | right..].
          + apply: pointer_range_incl_l hpr.
            by have /= := A.(ass_above_limit); lia.
          rewrite pointer_range_between.
          apply: zbetween_trans hb.
          rewrite /zbetween !zify.
          have /= hioff := A.(ass_ioff).
          have /= habove := A.(ass_above_limit).
          have hrange1 := [elaborate wunsigned_range (top_stack m1')].
          have hrange2 := [elaborate wunsigned_range (top_stack (emem s1))].
          rewrite wunsigned_add; last by lia.
          have := MAX _ ok_fd.
          by rewrite EQ /=; lia.
        move=> fd''; rewrite ok_fd => -[?]; subst fd''.
        have := MAX _ ok_fd.
        rewrite /frame_size EQ /=.
        rewrite (wunsigned_top_stack_after_aligned_alloc stk_sz_pos stk_extra_sz_pos frame_noof sp_aligned ok_m1').
        have := stack_frame_allocation_size_bound stk_sz_pos stk_extra_sz_pos.
        by lia.
      rewrite (mix_ilsteps_split_in_fn (P:=[::P]) (lc:=lbody) _ ok_body); last by simpl_size; lia.
      apply (xrutt_facts.xrutt_bind ih).
      move=> ks2 ls2 [] [] M2 SC2 X2 hpc2 hfn2 RSP2 S2 Max_sub2 hdisj2 hsub2 K2 hvalid hstable H2 U2.
      apply xrutt_bind_iresult_left; t_xrbindP => _ + <- /=.
      move=> /and3P [] free_ra _ _.
      apply xrutt_bind_iresult_left; t_xrbindP =>  /stack_stableP SS.
      rewrite (mix_ilsteps_split_in_fn (P:=P :: lbody) (lc:=Q) _ ok_body); last by simpl_size; lia.
      rewrite catA in ok_body.
      rewrite (step_mix_ilsteps ok_body) //=; last by simpl_size; lia.
      rewrite /eval_instr /= /get_var /=.
      have ra_not_written : (lvm ls2).[ra] = (lvm t1).[ra].
      * symmetry; apply: K2.
        have /and3P [_ _ ?] := free_ra.
        by apply/Sv_memP.
      rewrite ra_not_written ok_ra /= truncate_word_u.
      have := decode_encode_label small_dom_p' mem_lret.
      rewrite ok_retptr /rdecode_label /= => -> /=.
      rewrite (eval_jumpE ok_cbody) ok_pc /=.
      rewrite mix_ilsteps_0 //=; last first.
      + by rewrite /pc_between /setcpc /= eq_sym (negbTE hcaller).
      rewrite bind_ret_l.
      rewrite mix_ilsteps_0 //=; last first.
      + by rewrite /in_fn /= (negbTE hcaller).
      apply xrutt.xrutt_Ret.
      move=> body ra' lret' sp callee_saved'; rewrite /is_linear_of /sp_alloc_ra ok_fd' /= => -[ _ [<-] <-].
      rewrite /is_ra_of /value_of_ra /is_sp_for_call /is_callee_saved_of ok_fd => -[_ [<-] <-].
      rewrite EQ. case: lret' => // -[] -[] [] caller' lret' cbody' pc' [] ok_cbody' ok_pc' mem_lret'.
      rewrite ok_ra => -[retptr'] ok_retptr' [] ?; subst retptr'.
      have := decode_encode_label small_dom_p' mem_lret; rewrite ok_retptr.
      have := decode_encode_label small_dom_p' mem_lret'; rewrite ok_retptr' => -> [??]; subst caller' lret'.
      move: (ok_cbody) ok_cbody'; rewrite /is_linear_of => -[fd' ->] h [_] [<-]; rewrite h => ?.
      subst cbody' => {h fd' mem_lret' ok_retptr'}; move: ok_pc'; rewrite ok_pc => -[?]; subst pc'.
      move=> [_ [<-]]; rewrite EQ /= => -[? ->].
      move=> [_ [<-]]; rewrite EQ /= => ->; split => //.
      + by apply: alloc_free_validw_stable A hstable hvalid (free_stackP ks2.2).
      + subst callee_saved; rewrite {1}/kill_vars /=.
        move => ?; rewrite /set_RSP !Vm.setP; case: eqP => ?; last first.
        + rewrite kill_varsE; case: Sv.mem => //.
          by apply/compat_value_uincl_undef/Vm.getP.
        subst; move: (X2 vrsp).
        rewrite RSP2 -(ss_top_stack hstable) (alloc_stack_top_stack ok_m1').
        rewrite top_stack_after_aligned_alloc;
          last by exact: sp_aligned.
        by rewrite vm_truncate_val_eq // wrepr_opp.
      + apply: eq_exI K2.
        exact: SvP.MP.union_subset_1.
      + move => a [] a_lo a_hi /negbTE nv.
        have /= [L H] := ass_above_limit A.
        apply: H2.
        * by rewrite (ass_root A) /=; lia.
        rewrite (ass_valid A) nv /= !zify => - [].
        change (wsize_size U8) with 1%Z.
        rewrite (ass_add_ioff A).
        move: (sf_stk_sz _) (sf_stk_ioff _) (sf_stk_extra_sz _) (ass_ioff A) H => *.
        lia.
      exact: mm_free M2.
    }
    (* Internal function, return address in stack at offset “rastack” *)
    {
      rewrite linear_c_nil.
      case heq: (linear_c fn) => [lbl lbody] /=.
      set P1 := (P in P :: _ ++ lbody ++ _).
      set P2 := (P in _ :: P ++ lbody ++ _).
      set Q := (Q in P1 :: P2 ++ lbody ++ Q).
      move => ok_fd'.
      have ok_body : is_linear_of fn ((P1 :: P2) ++ lbody ++ Q).
      + by rewrite /is_linear_of ok_fd'; eauto.
      have := X vrsp; rewrite Vm.setP_eq /= cmp_le_refl.
      move=> /get_word_uincl_eq -/(_ (subctype_refl _)).
      set rsp := (X in Vword X) => ok_rsp.
      case/and5P: ok_ret_addr =>
        ra_call_ty ra_return_ty _ /eqP ? /andP[] /eqP hioff sf_align_for_ptr; subst rastack.
      have spec_m1' := alloc_stackP ok_m1'.
      have is_align_m1' := ass_align_stk spec_m1'.
      have ts_rsp : top_stack m1' = rsp.
      + rewrite (alloc_stack_top_stack ok_m1') top_stack_after_aligned_alloc; last by exact: sp_aligned.
        by rewrite wrepr_opp -/(stack_frame_allocation_size fd.(f_extra)).

      (* We factor out what we know thanks to value_of_ra. *)
      have {ok_lret} [caller [lret' [cbody [pc [retptr [? /= ok_cbody ok_pc mem_lret ok_retptr ok_ra]]]]]]:
        exists caller lret' cbody pc retptr, [/\
          lret = Some ((caller, lret'), cbody, pc),
          is_linear_of caller cbody,
          find_label lret' cbody = ok pc,
          (caller, lret') \in label_in_lprog p',
          encode_label (label_in_lprog p') (caller, lret') = Some retptr &
          match ra_call with
          | Some ra_call => (lvm t1).[ra_call] = Vword retptr
          | None => read (lmem t1) Aligned rsp Uptr = ok retptr
          end].
      + case: (ra_call) lret ok_lret {hcaller hpc} => [ra|] [[[[caller lret] cbody] pc]|] //.
        + move=> [ok_cbody ok_pc mem_lret [retptr ok_retptr ok_ra]].
          by exists caller, lret, cbody, pc, retptr; split.
        move=> [ok_cbody ok_pc mem_lret [retptr ok_retptr ok_ra]].
        exists caller, lret, cbody, pc, retptr; split=> //.
        move: ok_ra; rewrite ok_rsp => -[_ [<-] +].
        by rewrite wrepr0 GRing.addr0.
      subst lret.
      have {}ok_body : is_linear_of fn ([::P1] ++ P2 ++ lbody ++ Q) by done.
      rewrite (mix_ilsteps_split_in_fn (P:=[::P1]) (lc:=P2) _ ok_body); last by simpl_size;lia.

      (* Initial code that stores the return address on top of the stack if it
         is passed by register. Else, it is already on top of the stack.
         After executing that code, we are in a memory [mi], and the return
         address is on top of the stack. *)
      have [mi [hsemi hreadi Mi Hi Ui]] :
        exists mi, [/\
          mix_ilsteps p' (pc_between_c fn [:: P1] P2) t1 ≈
            Ret (of_estate (with_mem (to_estate t1) mi) fn (size (P1 :: P2))),
          read mi Aligned rsp Uptr = ok retptr,
          match_mem_gen (top_stack m0) s1 mi,
          preserved_metadata s1 (lmem t1) mi &
          target_mem_unchanged (lmem t1) mi].
      + case: ra_call EQ ra_call_ty ok_ra { X} @P2 ok_body {ok_fd'}
          => [ra_call|] EQ ra_call_ty ok_ra P2 ok_body; last first.
        + (* ra_call = None, easy case: mi = m1 *)
          exists (lmem t1); split=> //.
          rewrite mix_ilsteps_b0 // /P2 /=.
          rewrite -hfn -hpc; case: (t1) => >; reflexivity.
        (* ra_call = Some _ *)
        (* TODO this should be a lemma it is used elsewhere (above)*)
        have [m1s ok_m1s M']:
          exists2 m1s,
            write (lmem t1) Aligned rsp retptr = ok m1s &
            match_mem_gen (top_stack m0) s1 m1s.
        + apply: mm_write_invalid.
          * by have := MAX _ ok_fd; rewrite EQ /=; lia.
          * exact: M.
          1-2: cycle -1.
          * by rewrite -ts_rsp; apply: is_align_m sf_align_for_ptr is_align_m1'.
          have := (Memory.alloc_stackP ok_m1').(ass_above_limit).
          rewrite -ts_rsp (alloc_stack_top_stack ok_m1').
          rewrite top_stack_after_aligned_alloc // wrepr_opp.
          have := ass_ioff (alloc_stackP ok_m1'); rewrite -hioff => uptr_sz.
          by clear -uptr_sz; lia.
        exists m1s; split=> //.
        + rewrite (step_mix_ilsteps ok_body) //=.
          set x := eval_instr _ _ _.
          have -> : x = ok (lnext_pc (lset_mem t1 m1s)).
          + apply: (spec_lstore hliparams) => //=.
            * by rewrite /get_var ok_ra.
            * by rewrite truncate_word_u.
            * by rewrite /get_var ok_rsp.
            rewrite wrepr0 GRing.addr0.
            exact: ok_m1s.
          rewrite mix_ilsteps_b0 //=.
          + by apply eqit_Ret; rewrite -hpc -hfn; case: (t1).
          by rewrite hpc.
        + exact: (writeP_eq ok_m1s).
        + apply: (preserved_metadata_store_top_stack ok_m1');
            last by rewrite -hioff; apply Z.le_refl.
          by rewrite top_stack_after_aligned_alloc // wrepr_opp; apply: ok_m1s.
        (* the frame is inside the stack *)
        have hb1:
          zbetween
            (sp0 - wrepr Uptr max0) max0
            rsp (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd)).
        + rewrite /zbetween !zify.
          rewrite wunsigned_sub; last by have := wunsigned_range sp0; lia.
          move: (MAX _ ok_fd) stk_frame_le_max.
          rewrite /frame_size EQ /=.
          rewrite (wunsigned_top_stack_after_aligned_alloc _ _ _ _ ok_m1') //= ts_rsp.
          have := stack_frame_allocation_size_bound stk_sz_pos stk_extra_sz_pos.
          by lia.
        (* the range is inside the new frame *)
        have hb2:
          between rsp (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd))
                  rsp Uptr.
        + apply zbetween_le.
          rewrite hioff /=.
          by have /= := (alloc_stackP ok_m1').(ass_ioff); lia.
        by apply (target_mem_unchanged_store hb1 hb2 ok_m1s).
      rewrite hsemi bind_ret_l.

      (* Function body: we rely on the induction hypothesis [E] *)
      have /ih{}ih : pre_c fn (f_body fd) 2 lbl (P1::P2) lbody Q.
      + split => //.
        + by rewrite /checked_c ok_fd /= chk_body.
        + move => q [L H]; rewrite /P1 /P2 /= /is_label /=.
          by case: (ra_call) => [?|] /=; rewrite orbF; apply/eqP; lia.
      set s1' := {| escs := _ |}.
      set ks1 := (Sv.empty, s1').
      set t1' := (of_estate _ _ _).
      have /ih{}ih : inv_c fn (P1::P2) ks1.2 t1'.
      + split => //.
        + have hle: (wunsigned (top_stack (emem s1)) <= wunsigned (top_stack m0))%Z.
          + by have := MAX _ ok_fd; rewrite EQ /=; lia.
          apply: mm_alloc hle Mi ok_m1'.
        + apply: vm_uincl_kill_vars_set_incl X => //.
          + by rewrite /ra_undef /ra_vm EQ; SvD.fsetdec.
          by rewrite ts_rsp.
        + by rewrite /ks1 /s1' /= Vm.setP_eq vm_truncate_val_eq.
        + move=> pr /=.
          move=> hvalid; apply /orP; move: hvalid.
          rewrite A.(ass_valid).
          move=> /orP [/S /orP [hvalid | hpr] | hb]; [by left | right..].
          + apply: pointer_range_incl_l hpr.
            by have /= := A.(ass_above_limit); lia.
          rewrite pointer_range_between.
          apply: zbetween_trans hb.
          rewrite /zbetween !zify.
          have /= hioff' := A.(ass_ioff).
          have /= habove := A.(ass_above_limit).
          have hrange1 := [elaborate wunsigned_range (top_stack m1')].
          have hrange2 := [elaborate wunsigned_range (top_stack (emem s1))].
          rewrite wunsigned_add; last by lia.
          have := MAX _ ok_fd.
          by rewrite EQ /=; lia.
        move=> fd''; rewrite ok_fd => -[?]; subst fd''.
        have := MAX _ ok_fd.
        rewrite /frame_size EQ /=.
        rewrite (wunsigned_top_stack_after_aligned_alloc stk_sz_pos stk_extra_sz_pos frame_noof sp_aligned ok_m1').
        have := stack_frame_allocation_size_bound stk_sz_pos stk_extra_sz_pos.
        by lia.
      rewrite (mix_ilsteps_split_in_fn (P:=P1::P2) (lc:=lbody) _ ok_body); last by simpl_size;lia.
      apply (xrutt_facts.xrutt_bind ih).
      move=> ks2 ls2 [] [] M2 SC2 X2 hpc2 hfn2 RSP2 S2 Max_sub2 hdisj2 hsub2 K2 hvalid hstable H2 U2.
      apply xrutt_bind_iresult_left; t_xrbindP => _ + <- /=.
      move=> /and3P [] free_ra _ _.
      apply xrutt_bind_iresult_left; t_xrbindP =>  /stack_stableP SS.
      rewrite (mix_ilsteps_split_in_fn (P:=P1 :: P2++ lbody) (lc:=Q) _ ok_body); last by simpl_size; lia.

      (* Final code that jumps back to the return address. The return address
         is read directly from the top of the stack (if ra_return = None),
         or loaded in ra_return before the jump (if ra_return <> None).
         After executing that code, we are in a vmap [vmf], and the value held
         in vrsp depends on ra_return. If ra_return = None, the return address
         is popped from the stack, so we need to subtract [wsize_size Uptr]. *)
      have [vmf hsemf eq_vmf]:
        exists2 vmf,
          (mix_ilsteps p' (pc_between_c fn (P1 :: P2 ++ lbody) Q) ls2) ≈
            Ret (of_estate (with_vm (to_estate ls2) vmf) caller pc.+1) &
          (lvm ls2).[vrsp <- Vword (sp_alloc_ra rsp (fd.(f_extra).(sf_return_address)))]
            =[\ sv_of_option ra_return] vmf.
      + have ok_rsp2: (lvm ls2).[vrsp] = Vword rsp.
        + have := X2 vrsp; rewrite RSP2.
          move=> /get_word_uincl_eq -/(_ (subctype_refl _)) ->.
          have /ss_top_stack /= <- := hstable.
          by rewrite ts_rsp.
        have hreadf: read (lmem ls2) Aligned rsp Uptr = read mi Aligned rsp Uptr.
        * assert (root_range := wunsigned_range (stack_root m1')).
          have top_range := ass_above_limit A.
          have top_stackE := wunsigned_top_stack_after_aligned_alloc stk_sz_pos stk_extra_sz_pos frame_noof sp_aligned ok_m1'.
          have sf_large : (wsize_size Uptr <= stack_frame_allocation_size (f_extra fd))%Z.
          - apply: Z.le_trans; last exact: proj1 (round_ws_range _ _).
            have := ass_ioff A.
            rewrite -hioff; move: (sf_stk_sz _) (sf_stk_extra_sz _) stk_sz_pos stk_extra_sz_pos; lia.
          have rastack_no_overflow : (0 <= wunsigned (top_stack m1'))%Z ∧ (wunsigned (top_stack m1') +  wsize_size Uptr <= wunsigned (stack_root m1'))%Z.
          * assert (top_stack_range := wunsigned_range (top_stack m1')).
            assert (old_top_stack_range := wunsigned_range (top_stack (emem s1))).
            assert (h := wsize_size_pos Uptr).
                  split; first lia.
            rewrite (alloc_stack_top_stack ok_m1') top_stack_after_aligned_alloc // wrepr_opp.
            rewrite -/(stack_frame_allocation_size _) wunsigned_sub; last first.
            - split; last lia.
              rewrite top_stackE; move: (stack_frame_allocation_size _) => n; lia.
            rewrite A.(ass_root).
            etransitivity; last exact: top_stack_below_root.
            rewrite -/(top_stack (emem s1)).
            move: root_range top_range top_stackE sf_large top_stack_range old_top_stack_range h => /=; lia.
          rewrite -!ts_rsp.
          apply: eq_read => al i [] i_lo i_hi; symmetry; rewrite !(read8_alignment Aligned); apply: H2.
          - rewrite addE wunsigned_add /=; lia.
          rewrite (Memory.alloc_stackP ok_m1').(ass_valid).
          apply/orP; case.
          - apply/negP; apply: stack_region_is_free.
            rewrite -/(top_stack _).
            move: (stack_frame_allocation_size _) top_stackE sf_large => n top_stackE sf_large.
            rewrite addE !wunsigned_add; lia.
          rewrite !zify (ass_add_ioff A) -hioff addE.
          rewrite wunsigned_add; lia.
        case: ra_return EQ ra_return_ty @Q ok_body {free_ra ok_fd'}
          => [ra_return|] EQ ra_return_ty Q ok_body.
        + move: ok_body; rewrite catA => ok_body.
          exists (lvm ls2).[ra_return <- Vword retptr].
          + rewrite catA in ok_body.
            rewrite (step_mix_ilsteps ok_body) //=; last by simpl_size;lia.
            set x := (eval_instr _ _ _).
            have -> : x = ok (lnext_pc (lset_vm ls2 (lvm ls2).[(mk_var_i ra_return) <- Vword retptr])).
            + apply: (spec_lload hliparams) => //=.
              * by rewrite /get_var ok_rsp2; reflexivity.
              rewrite wrepr0 GRing.addr0 hreadf.
              exact: hreadi.
            move: ok_body; rewrite /Q -[[:: _; _]]cat1s catA => ok_body.
            rewrite (step_mix_ilsteps ok_body) //=; last first.
            + by simpl_size;lia.
            + by rewrite hpc2; simpl_size; lia.
            rewrite /eval_instr /=.
            rewrite /get_var Vm.setP_eq vm_truncate_val_eq /=;
              last by rewrite (convertible_eval_atype ra_return_ty).
            rewrite truncate_word_u /=.
            have := decode_encode_label small_dom_p' mem_lret.
            rewrite ok_retptr /rdecode_label /= => -> /=.
            rewrite (eval_jumpE ok_cbody) ok_pc /=.
            rewrite mix_ilsteps_0; last first.
            + by rewrite /pc_between /= eq_sym (negbTE hcaller).
            reflexivity.
          rewrite /sp_alloc_ra EQ /=.
          apply eq_ex_set_r; first by case; clear; SvD.fsetdec.
          apply: (eq_ex_set_l _ (eq_ex_refl _)).
          by rewrite ok_rsp2 vm_truncate_val_eq.
        exists (lvm ls2).[vrsp <- Vword (rsp + wrepr _ (wsize_size Uptr))].
        + move: ok_body. rewrite !catA => ok_body.
          rewrite (step_mix_ilsteps ok_body) //=; last first.
          + by rewrite /Q;simpl_size;lia.
          rewrite /eval_instr /= lp_rspE.
          move /eqP in ra_return_ty.
          rewrite /get_var ok_rsp2 /= truncate_word_u /=.
          rewrite hreadf hreadi /=.
          have := decode_encode_label small_dom_p' mem_lret.
          rewrite ok_retptr /rdecode_label /= => -> /=.
          rewrite (eval_jumpE ok_cbody) ok_pc /=.
          rewrite mix_ilsteps_0; last first.
          + by rewrite /pc_between /= eq_sym (negbTE hcaller).
          reflexivity.
        by rewrite /sp_alloc_ra EQ /=.
      rewrite hsemf bind_ret_l.
      rewrite mix_ilsteps_0; last first.
      + by rewrite /in_fn /= (negbTE hcaller).
      apply xrutt.xrutt_Ret.

      move=> body ra' lret'' sp callee_saved'; rewrite /is_linear_of /sp_alloc_ra ok_fd' /= => -[ _ [<-] <-].
      rewrite /is_ra_of /value_of_ra /is_sp_for_call /is_callee_saved_of ok_fd => -[_ [<-] <-].
      rewrite EQ => H.
      move=> [_ [<-]]; rewrite EQ /= => -[? ?].
      move=> [_ [<-]]; rewrite EQ /= => ?; subst sp callee_saved'.
      have ? : lret'' = Some (caller, lret', cbody, pc).
      + move: H; case: (ra_call) ok_ra lret'' =>
          [ra | ] hra [] // [] [] [] caller' lret'' cbody' pc' [] ok_cbody' ok_pc' mem_lret'.
        + rewrite hra => -[retptr'] ok_retptr' [?]; subst retptr'.
          have := decode_encode_label small_dom_p' mem_lret; rewrite ok_retptr.
          have := decode_encode_label small_dom_p' mem_lret'; rewrite ok_retptr' => -> [??]; subst caller' lret'.
          move: (ok_cbody) ok_cbody'; rewrite /is_linear_of => -[fd' ->] h [_] [<-]; rewrite h => ?.
          by subst cbody' => {h fd' mem_lret' ok_retptr'}; move: ok_pc'; rewrite ok_pc => -[?]; subst pc'.
        move=> -[retptr'] ok_retptr' [sp']; rewrite wrepr0 GRing.addr0 ok_rsp => -[?]; subst sp'.
        rewrite hra => -[?]; subst retptr'.
        have := decode_encode_label small_dom_p' mem_lret; rewrite ok_retptr.
        have := decode_encode_label small_dom_p' mem_lret'; rewrite ok_retptr' => -> [??]; subst caller' lret'.
        move: (ok_cbody) ok_cbody'; rewrite /is_linear_of => -[fd' ->] h [_] [<-]; rewrite h => ?.
        by subst cbody' => {h fd' mem_lret' ok_retptr'}; move: ok_pc'; rewrite ok_pc => -[?]; subst pc'.
      subst lret''; split => //.
      + by apply: alloc_free_validw_stable A hstable hvalid (free_stackP ks2.2).
      + subst callee_saved; rewrite {1}/kill_vars /=.
        move: eq_vmf; rewrite /ra_vm_return EQ /= => eq_vmf.
        move => x; rewrite /set_RSP !Vm.setP; case: eqP => ?.
        + subst x.
          rewrite -eq_vmf; first by rewrite Vm.setP_eq.
          case/andP: free_ra => _.
          by case: (ra_return) => [r /andP[] _ /eqP|] /=; clear; SvD.fsetdec.
        rewrite kill_varsE; case: Sv_memP => h.
        + by apply/compat_value_uincl_undef/Vm.getP.
        rewrite -eq_vmf //.
        rewrite Vm.setP_neq //.
        by apply/eqP.
      + apply eq_exT with (lvm ls2).
        + by apply: eq_exI K2; clear; SvD.fsetdec.
        apply: eq_exT (eq_exI _ eq_vmf);
          last by rewrite /ra_vm_return EQ; clear; SvD.fsetdec.
        apply: (eq_ex_set_r _ (eq_ex_refl _)).
        by case; clear; SvD.fsetdec.
      + transitivity mi => //.
        move => a [] a_lo a_hi /negbTE nv.
        have /= [L R] := ass_above_limit A.
        apply: H2.
        * by rewrite (ass_root A) /=; lia.
        rewrite (ass_valid A) nv /= !zify => - [].
        change (wsize_size U8) with 1%Z.
        rewrite (ass_add_ioff A).
        move: (sf_stk_sz _) (sf_stk_ioff _) (sf_stk_extra_sz _) (ass_ioff A) R; lia.
      + exact: mm_free M2.
      by transitivity mi.
    }
  Qed.

  End STACK.

  Definition preF_export (gd:word Uptr) fn (s : estate) (ls : estate) :=
    match get_fundef p.(p_funcs) fn, get_fundef p'.(lp_funcs) fn with
    | Some fd, Some lfd =>
      let vm := evm s in
      let m := emem s in
      let lvm := evm ls in
      let lm := emem ls in
      [/\ lvm.[vid (lp_rsp p')] = Vword (top_stack m)
        , lvm.[vid (lp_rip p')] = Vword gd
        , vm_initialized_on lvm (lfd_callee_saved lfd)
        , (fd.(f_extra).(sf_stk_max) + wsize_size fd.(f_extra).(sf_align) - 1 <= wunsigned (top_stack m))%Z
        , vm <=1 lvm
        , escs s = escs ls
        & match_mem m lm ]
    | _, _ => true
    end.

  Definition postF_export fn (s ls :estate) (s' ls':estate) :=
    match get_fundef p.(p_funcs) fn, get_fundef p'.(lp_funcs) fn with
    | Some fd, Some lfd =>
      let m := emem s in
      let vm' := evm s' in
      let m' := emem s' in
      let lvm' := evm ls' in
      let lm := emem ls in
      let lm' := emem ls' in
      [/\ lvm'.[vid (lp_rsp p')] = Vword (top_stack m)
        , match_mem m' lm'
        , target_mem_unchanged m (align_top_stack (top_stack m) fd.(f_extra)) fd.(f_extra).(sf_stk_max) lm lm'
        & forall res,   get_var_is false  vm' fd.(f_res) = ok res →
          exists2 res', get_var_is false lvm' lfd.(lfd_res) = ok res' &
             List.Forall2 value_uincl res res']
    | _, _ => false
    end.

  Context {E E0: Type -> Type} {wE: with_Error E E0} {rndE0 : RndEvent syscall_state -< E0} {rE0 : EventRels E0}.

  Context (callee_saved_not_arr : forall x, Sv.In x callee_saved -> ~is_aarr (vtype x)).

  Lemma linear_exportcallP gd fn :
    wkequiv_io
      (preF_export gd fn)
      (isem_exportcall_check var_tmps p gd fn)
      (mix_ilsem_exportcall p' fn)
      (postF_export fn).
  Proof.
    move=> s ls; rewrite /preF_export /postF_export.
    rewrite /isem_exportcall_check /mix_ilsem_exportcall.
    case ok_fd: get_fundef => [fd | ] /=; last first.
    + rewrite bind_throw => _.
      apply xrutt.xrutt_CutL.
      by rewrite /core_logics.errcutoff /is_error /subevent /resum /fromErr /= mid12.
    have ok_fd' := get_fundef_p' ok_fd.
    rewrite ok_fd' /= !bind_ret_l /= => -[] vm_rsp vm_rip safe_registers enough_stk VM SC1 M.
    apply xrutt_bind_iresult_left; t_xrbindP.
    move=> /and4P [/is_RAnoneP Export to_save_not_result RSP_not_result /value_eqb_eq hrip].
    rewrite Export /= in safe_registers.
    rewrite Export /= bind_ret_l.
    case ok_m1 : alloc_stack => [m1 | ?] /=; last first.
    + rewrite bind_throw.
      apply xrutt.xrutt_CutL.
      by rewrite /core_logics.errcutoff /is_error /subevent /resum /fromErr /= mid12.
    rewrite bind_ret_l.
(*    set m0 := (emem s). *)
    set sp0 := align_top_stack (top_stack (emem s)) fd.(f_extra).
    set max0 := fd.(f_extra).(sf_stk_max).
    have enough_space : (0 <= max0 <= wunsigned sp0)%Z.
    + have := checked_prog ok_fd.
      rewrite /check_fd; t_xrbindP=> _ _ _ _ ok_stk_sz _ _ _.
      case/and4P: ok_stk_sz => /ZleP stk_sz_pos /ZleP stk_extra_sz_pos /ZltP frame_noof /ZleP stk_frame_le_max.
      rewrite /max0 /sp0; split.
      + by have := frame_size_bound stk_sz_pos stk_extra_sz_pos; lia.
      rewrite /align_top_stack /align_top.
      have: (0 <= sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd) <= wunsigned (top_stack (emem s)))%Z.
      + have := frame_size_bound stk_sz_pos stk_extra_sz_pos.
        have := wsize_size_pos (sf_align (f_extra fd)).
        rewrite /= in enough_stk.
        move: stk_sz_pos stk_extra_sz_pos frame_noof stk_frame_le_max enough_stk => /=.
        lia.
      move=> /(top_stack_after_alloc_bounded (ws:=sf_align (f_extra fd))).
      rewrite wunsigned_add.
      + move: stk_sz_pos stk_extra_sz_pos frame_noof stk_frame_le_max enough_stk => /=.
        lia.
      rewrite -(alloc_stack_top_stack ok_m1).
      have := (alloc_stackP ok_m1).(ass_above_limit).
      have := [elaborate (wunsigned_range (top_stack m1))].
      have := [elaborate (wunsigned_range (top_stack (emem s)))].
      move: stk_sz_pos stk_extra_sz_pos frame_noof stk_frame_le_max enough_stk => /=.
      by lia.
    have sp0_top : (wunsigned sp0 <= wunsigned (top_stack (emem s)))%Z.
    + have := checked_prog ok_fd.
      rewrite /check_fd; t_xrbindP=> _ _ _ _ ok_stk_sz _ _ _.
      case/and4P: ok_stk_sz => /ZleP stk_sz_pos /ZleP stk_extra_sz_pos /ZltP frame_noof /ZleP stk_frame_le_max.
      rewrite /sp0 /align_top_stack /align_top.
      have hass := alloc_stackP ok_m1.
      have [_] := hass.(ass_above_limit).
      rewrite (alloc_stack_top_stack ok_m1).
      rewrite wunsigned_add.
      + move: stk_sz_pos stk_extra_sz_pos => /=; lia.
      rewrite -(alloc_stack_top_stack ok_m1).
      have := hass.(ass_above_limit).
      have := [elaborate (wunsigned_range (top_stack m1))].
      have := [elaborate (wunsigned_range (top_stack (emem s)))].
      move: stk_sz_pos stk_extra_sz_pos frame_noof stk_frame_le_max => /=.
      by lia.
    have C : is_linear_of fn (lfd_body (linear_fd fn fd).2).
    + by rewrite /is_linear_of; eauto.
    have ? : is_ra_of fn RAnone.
    + by rewrite /is_ra_of; eauto.
    have ? : is_sp_for_call fn s (top_stack (emem s)).
    + by rewrite /is_sp_for_call; exists fd => //; rewrite Export.
    have ? : is_callee_saved_of fn [seq i.1 | i <- sf_to_save (f_extra fd)].
    + by rewrite /is_callee_saved_of; exists fd => //; rewrite Export.
    have hpreF : preF s sp0 max0 fn fn s (ls_export_initial (escs ls) (emem ls) (evm ls) fn).
    + split => //.
      + by move=> pr ->.
      + move=> fd'; rewrite ok_fd => -[?]; subst fd'.
        rewrite /= Export /max0 /sp0.
        split; first by apply Z.le_refl.
        split=> //.
        rewrite /align_top_stack /align_top -(alloc_stack_top_stack ok_m1).
        have /= habove := (alloc_stackP ok_m1).(ass_above_limit).
        have := checked_prog ok_fd.
        rewrite /check_fd; t_xrbindP => _ _ _ _ ok_stk_sz _ _ _.
        case/and4P: ok_stk_sz => /= /ZleP stk_sz_pos /ZleP stk_extra_sz_pos /ZltP frame_noof /ZleP stk_frame_le_max.
        rewrite wunsigned_add; first by lia.
        have := [elaborate (wunsigned_range (top_stack m1))].
        have := [elaborate (wunsigned_range (top_stack (emem s)))].
        by lia.
      exists (lfd_body (linear_fd fn fd).2), RAnone, None, (top_stack (emem s)),
        [seq i.1 | i <- sf_to_save (f_extra fd)]; split => //.
      move => x; rewrite !Vm.setP vm_truncate_val_eq //.
      case: eqP => ? /=.
      + by subst x; rewrite lp_rspE in vm_rsp; rewrite vm_rsp.
      apply value_uincl_trans with s.[x] => //.
      apply: vm_uincl_kill_vars.
    have h := [elaborate linear_funP sp0_top enough_space hpreF].
    apply (xrutt_facts.xrutt_bind h).
    move=> ks2 ls2 hpost.
    have [] // := [elaborate
     hpost
        (lfd_body (linear_fd fn fd).2) RAnone None (top_stack (emem s))
        [seq i.1 | i <- sf_to_save (f_extra fd)]].
    move=> SC2 hvalid2 K2 X2 hpc2 hstable2 hpres2 M2 U2.
    apply xrutt_bind_iresult_left; t_xrbindP => /Sv.subset_spec ok_callee_saved.
    have -> /=: (all (λ x : var, value_eqb ls.[x] (lvm ls2).[x]) (Sv.elements callee_saved)).
    + have : (evm ls) =[callee_saved] (lvm ls2).
      + move => r hr; apply: X2.
        rewrite /ra_vm_return /=.
        move: ok_callee_saved hr; clear.
        rewrite sv_of_list_map Sv.diff_spec => S hrC [] hrX; apply.
        by SvD.fsetdec.
      move=> heq; apply/allP => x /Sv_elemsP hx; rewrite heq // value_eqb_refl //.
      move: (lvm ls2).[x] (Vm.getP (lvm ls2) x) (callee_saved_not_arr hx) => [] //.
      by move=> ?? /compat_valE; case: vtype.
    rewrite bind_ret_l; apply xrutt.xrutt_Ret; split => //.
    + have := K2 vrsp; rewrite Vm.setP_eq /= cmp_le_refl /sp_alloc_ra /= => ?.
      by apply get_word_uincl_eq => //=; rewrite lp_rspE.
    + by move: M2; rewrite /match_mem -(ss_top_stack hstable2).
    have vm2_vmo : (evm ks2.2) <=[ (sv_of_list v_var (f_res fd)) ] (lvm ls2).
    - move => r r_in_result.
      have r_not_saved : ¬ Sv.In r (sv_of_list id (map fst fd.(f_extra).(sf_to_save))).
      + apply/Sv_memP.
        rewrite sv_of_listE map_id -sv_of_listE; apply/Sv_memP => K.
        by move/disjointP: to_save_not_result => /(_ _ K).
      apply: value_uincl_trans (K2 r).
      have r_not_rsp : vrsp != r.
      + by apply/eqP => K; move /Sv_memP: RSP_not_result; subst r.
      rewrite Vm.setP_neq // kill_varsE.
      rewrite /killed_by_exit Sv_mem_add /=.
      case: eqP => [ | _]; last by move /Sv_memP: r_not_saved => /negbTE ->.
      have := checked_prog ok_fd.
      rewrite /check_fd; t_xrbindP => _ _ _ _ _ + _ _ /= heq.
      by rewrite Export -heq => /sv_of_listP.
    move=> res; apply: (get_var_is_uincl_on vm2_vmo).
    by move=> x hx; apply/Sv_memP/sv_of_listP/in_map; exists x.
  Qed.

End PROOF.

End WITH_PARAMS.
