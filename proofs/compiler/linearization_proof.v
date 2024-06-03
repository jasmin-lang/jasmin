(* ** Imports and settings *)
From Coq
Require Import Setoid Morphisms Lia.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
Require Import ZArith Utf8.
        Import Relations.

Require sem_one_varmap_facts label.
Import word_ssrZ.
Import ssrring.
Import psem psem_facts sem_one_varmap compiler_util label sem_one_varmap_facts low_memory.
Require Import seq_extra.
Require Import constant_prop constant_prop_proof.
Require Import fexpr fexpr_sem fexpr_facts.
Require Export linearization linear_sem linear_facts.
Import Memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local] Existing Instance withsubword.
#[local] Opaque eval_jump.

Section WITH_PARAMS.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}.

Notation spointer := (sword Uptr) (only parsing).

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

Lemma set_up_sp_register_label_in_lcmd liparams x sf_sz al y tmp:
  label_in_lcmd (set_up_sp_register liparams x sf_sz al y tmp) = [::].
Proof. apply map_li_of_fopn_args_label_in_lcmd. Qed.

Lemma map_li_of_fopn_args_has_label lbl ii args :
  has (is_label lbl) (map (li_of_fopn_args ii) args) = false.
Proof. by elim: args => [|[]]. Qed.

Lemma set_up_sp_register_has_label lbl liparams x sf_sz al y tmp:
  has (is_label lbl) (set_up_sp_register liparams x sf_sz al y tmp) = false.
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
  Lemma cat_while : forall a c e c', Pc c -> Pc c' -> Pr (Cwhile a c e c').
  Proof.
    move=> a c e c' Hc Hc' ii fn lbl l /=.
    case: is_bool => [ [] | ].
    + rewrite Hc' (Hc' _ _ [:: _]) align_bind; f_equal; case: linear_c => lbl1 lc1.
      by rewrite Hc (Hc _ _ (_ ++ _)); case: linear_c => lbl2 lc2; rewrite !catA cats1 -cat_rcons.
    + by apply Hc.
    case: c' Hc' => [ _ | i c' ].
    + by rewrite Hc (Hc _ _ [:: _]) align_bind; case: linear_c => lbl1 lc1; rewrite /= cats1 cat_rcons.
    move: (i :: c') => { i c' } c' Hc'.
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
    by case: sf_return_address => // [ ra ? | ra ra_ofs ? ] _; rewrite cats0 -catA.
  Qed.

  Lemma linear_i_nil fn i lbl tail :
     linear_i fn i lbl tail =
     let: (lbl, lc) := linear_i fn i lbl [::] in (lbl, lc ++ tail).
  Proof.
    exact:
      (instr_Rect cat_mkI cat_skip cat_seq cat_assgn cat_opn cat_syscall cat_if cat_for cat_while cat_call).
  Qed.

  Lemma linear_c_nil fn c lbl tail :
     linear_c (linear_i fn) c lbl tail =
     let: (lbl, lc) := linear_c (linear_i fn) c lbl [::] in (lbl, lc ++ tail).
  Proof.
    exact:
      (cmd_rect cat_mkI cat_skip cat_seq cat_assgn cat_opn cat_syscall cat_if cat_for cat_while cat_call).
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

Arguments disjoint_labels _%positive _%positive _.

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
have : exists (b1 b2:bool), st = sbool /\ sem_pexpr true gd s e1 = ok (Vbool b1) /\ sem_pexpr true gd s e2 = ok (Vbool b2).
+ rewrite h1 h2;case: bp h => ?;subst.
  + have [??]:= truncate_valI htr1;subst st v1.
    by move: htr2; rewrite /truncate_val; t_xrbindP => /= b2 /to_boolI -> ?;eauto.
  have [??]:= truncate_valI htr2;subst st v2.
  by move: htr1; rewrite /truncate_val; t_xrbindP => /= b1 /to_boolI -> ?;eauto.
move=> [b1 [b2 [-> []/dup[]hb1 /he1 -> /dup[]hb2 /he2 ->]]] /=.
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
    (if tmp is Some x then (v_var rspi) <> (v_var x) /\ vtype x = sword Uptr else True)
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
    -> (if tmp is Some x then (v_var rspi) <> (v_var x) /\ vtype x = sword Uptr else True)
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
     [/\ lsem lp ls ls'
       , evm s =[\ Sv.add rspi X ] vm'
       & vm'.[rspi] = ts'
     ].

Lemma sf_correct_1 f op : sf_correct f op -> sf_correct1 f op.
Proof.
  move=> h P Q lp sp_rsp tmp fn s ii ts sz hlin htmp hget.
  have [vm' [h1 h2 h3]] := h sp_rsp tmp s ts sz htmp hget.
  exists vm'; split => //; assert (h4 := sem_fopns_args_lsem h1 hlin).
  by rewrite size_map.
Qed.

Definition allocate_stack_frame_correct :=
  Eval hnf in sf_correct allocate_stack_frame (fun x y => x - y)%R.

Definition free_stack_frame_correct :=
  Eval hnf in sf_correct free_stack_frame (fun x y => x + y)%R.

Definition lmove_correct :=
  forall (xd xs : var_i) w ws (w':word ws) s,
    vtype xd = sword Uptr -> vtype xs = sword Uptr ->
    get_var true (evm s) xs = ok (Vword w') ->
    truncate_word Uptr w' = ok w ->
    sem_fopn_args (lip_lmove liparams xd xs) s = ok (with_vm s (evm s).[xd <- Vword w]).

Definition lstore_correct_aux lip_check_ws lip_lstore :=
  forall (xd xs : var_i) ofs ws (w: word ws) wp s m,
    vtype xs = sword ws ->
    lip_check_ws ws ->
    (get_var true (evm s) xd >>= to_word Uptr) = ok wp ->
    (get_var true (evm s) xs >>= to_word ws) = ok w ->
    write (emem s) Aligned (wp + wrepr Uptr ofs)%R w = ok m ->
    sem_fopn_args (lip_lstore xd ofs xs) s = ok (with_mem s m).

Definition lstore_correct := lstore_correct_aux (lip_check_ws liparams) (lip_lstore liparams).

Definition set_up_sp_register_correct :=
  forall vrsp r tmp ts al sz s,
    let: ts' := align_word al (ts - wrepr Uptr sz) in
    let: lcmd := lip_set_up_sp_register liparams vrsp sz al r tmp in
    let: k := Sv.add (v_var r) (Sv.add tmp (Sv.add vrsp vflags)) in
    get_var true (evm s) vrsp = ok (Vword ts) ->
    vtype vrsp = sword Uptr -> vtype r = sword Uptr -> vtype tmp = sword Uptr ->
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
     Let: ws := if vtype x is sword ws then ok ws else Error ErrType in
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
     Let: ws := if vtype x is sword ws then ok ws else Error ErrType in
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
    spec_lip_lstores : lstores_correct;
    spec_lip_lloads  : lloads_correct;
    spec_lip_tmp     : lip_tmp liparams <> lip_tmp2 liparams;
    spec_lip_check_ws: lip_check_ws liparams Uptr;
  }.

Lemma spec_lip_allocate_stack_frame_1 (h:h_linearization_params) :
   sf_correct1 allocate_stack_frame (fun x y => x - y)%R.
Proof. apply sf_correct_1; apply (spec_lip_allocate_stack_frame h). Qed.

Lemma spec_lip_free_stack_frame_1 (h:h_linearization_params) :
   sf_correct1 free_stack_frame (fun x y => x + y)%R.
Proof. apply sf_correct_1; apply (spec_lip_free_stack_frame h). Qed.

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

Definition lload_correct_aux :=
 forall (xd xs : var_i) ofs s vm top,
    get_var true (evm s) xs >>= to_word Uptr = ok top ->
    (Let: ws := if vtype xd is sword ws then ok ws else Error ErrType in
     Let _ := assert (lip_check_ws ws) ErrType in
     Let w := read (emem s) Aligned (top + wrepr Uptr ofs)%R ws in
     set_var true (evm s) xd (Vword w)) = ok vm ->
    sem_fopn_args (lip_lload xd xs ofs) s = ok (with_vm s vm).

Context (lload_correct : lload_correct_aux).

Definition ladd_imm_correct_aux :=
  forall (x1 x2:var_i) s (w: word Uptr) ofs,
    vtype x1 = sword Uptr -> v_var x1 <> v_var x2 ->
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
      Let ws := if vtype x is sword ws then ok ws else Error ErrType in
      Let _ := assert (lip_check_ws ws) ErrType in
      Let v := Let x := get_var true vm1 x in to_word ws x in write m Aligned (top + wrepr Uptr ofs)%R v) m1 to_save =
    ok m2
  → sem_fopns_args s lcmd = ok (with_mem s m2) .
Proof.
  elim: to_save s => /= [ | [x ofs] to_save ih] s hget.
  + by move=> [<-]; rewrite with_mem_same.
  t_xrbindP; case heq: vtype => [|||ws]// m' _ [<-] hchk w v hgetx htow hw hf.
  have -> := lstore_correct (xd:= rspi) (xs:= VarI x dummy_var_info) heq hchk hget _ hw.
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
  set tmp2 := (VarI {| vtype := sword Uptr; vname := lip_tmp2 |} dummy_var_info).
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
       Let: ws := if vtype x is sword ws then ok ws else Error ErrType in
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
  have /(_ ofs vm1) := lload_correct (xd:= VarI x dummy_var_info) hget.
  rewrite heqt /= hchk /= hread /= hset => -> //=.
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
  have /(_ ofs vm2):= lload_correct (xd:= VarI rspi dummy_var_info) (s:= with_vm s vm1) hget2.
  by rewrite heqt /= hchk /= hread /= => /(_ hset) -> /=; exists vm2.
Qed.

Lemma lloads_imm_dfl_correct :
  lloads_correct_aux lip_check_ws lip_tmp2 (lloads_imm_dfl lip_tmp2 lip_lload lip_add_imm lip_imm_small).
Proof.
  move=> rspi to_rest ofs s top vm2 /= hnin hnin2 hne hget hf.
  rewrite /lloads_imm_dfl; case: ifP => _.
  + by apply: lloads_dfl_correct hnin hnin2 hne hget hf.
  rewrite sem_fopns_args_cat; move: _.2 => ofs0.
  set tmp2 := (VarI {| vtype := sword Uptr; vname := lip_tmp2 |} dummy_var_info).
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
                      | sword ws => ok ws
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
    rewrite hread /= set_var_eq_type //=.
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

  Lemma spec_lmove {lp ls} {x y:var_i} (w : word Uptr) :
    vtype x = sword Uptr ->
    vtype y = sword Uptr ->
    get_var true (lvm ls) (v_var y) = ok (Vword w) ->
    let li := lmove liparams x y in
    let s := to_estate ls in
    eval_instr lp li ls = ok (lnext_pc (lset_estate' ls (with_vm s (evm s).[x <- Vword w]))).
  Proof.
    move=> htx hty hget /=; rewrite -(lset_estate_same ls).
    apply sem_fopn_args_eval_instr.
    by rewrite (spec_lip_lmove hliparams (s:= to_estate ls) htx hty hget (truncate_word_u w)).
  Qed.

  Lemma spec_lstore {lp ls m ofs} {x y:var_i} {wx ws' wy'} {wy : word ws'} :
    vtype y = sword Uptr ->
    get_var true (lvm ls) y = ok (Vword wy) ->
    truncate_word Uptr wy = ok wy' ->
    get_var true (lvm ls) x = ok (Vword wx) ->
    write (lmem ls) Aligned (wx + wrepr Uptr ofs)%R wy' = ok m ->
    let: li := lstore liparams x ofs y in
    eval_instr lp li ls = ok (lnext_pc (lset_mem ls m)).
  Proof.
    move=> hty hgy htr hgx hw /=; rewrite -(lset_estate_same ls).
    apply sem_fopn_args_eval_instr => /=.
    rewrite (spec_lip_lstore hliparams (s:= to_estate ls) hty (spec_lip_check_ws hliparams) _ _ hw) //.
    + by rewrite hgx /= truncate_word_u.
    by rewrite hgy /= htr.
  Qed.

  Lemma set_up_sp_register_ok lp sp_rsp ls r tmp ts al sz P Q :
    let: vrspi := vid sp_rsp in
    let: vrsp := v_var vrspi in
    let: ts' := align_word al (ts - wrepr Uptr sz) in
    let: lcmd := set_up_sp_register liparams vrspi sz al r tmp in
    is_linear_of lp (lfn ls) (P ++ lcmd ++ Q) ->
    lpc ls = size P ->
    get_var true (lvm ls) vrsp = ok (Vword ts) ->
    vtype r = sword Uptr -> vtype tmp = sword Uptr ->
    v_var tmp ≠ vrsp ->
    v_var r ≠ vrsp ->
    v_var r ≠ tmp ->
    exists vm',
      let: ls' := setpc (lset_vm ls vm') (size P + size lcmd) in
      let: k := Sv.add (v_var r) (Sv.add tmp (Sv.add vrsp vflags)) in
      [/\ lsem lp ls ls'
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
    by have := [elaborate sem_fopns_args_lsem hsem hlin]; rewrite -hsize size_map; case: (ls).
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
  Lemma valid_labels_assign (x : lval) (tg : assgn_tag) (ty : stype) (e : pexpr) : Pr (Cassgn x tg ty e).
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
  Lemma valid_labels_while (a : expr.align) (c : cmd) (e : pexpr) (c' : cmd) : Pc c → Pc c' → Pr (Cwhile a c e c').
  Proof.
    move => hc hc' ii fn lbl /=.
    case: is_boolP => [ [] | {e} e ].
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
    cmd_rect valid_labels_MkI valid_labels_nil valid_labels_cons valid_labels_assign valid_labels_opn valid_labels_syscall valid_labels_if valid_labels_for valid_labels_while valid_labels_call.

  Definition linear_has_valid_labels_instr : ∀ i, Pi i :=
    instr_Rect valid_labels_MkI valid_labels_nil valid_labels_cons valid_labels_assign valid_labels_opn valid_labels_syscall valid_labels_if valid_labels_for valid_labels_while valid_labels_call.

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
  Lemma nb_labels_assign (x : lval) (tg : assgn_tag) (ty : stype) (e : pexpr) : Pr (Cassgn x tg ty e).
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
  Lemma nb_labels_while (a : expr.align) (c : cmd) (e : pexpr) (c' : cmd) : Pc c → Pc c' → Pr (Cwhile a c e c').
  Proof.
    move => hc hc' ii fn lbl /=.
    case: is_boolP => [ [] | {e} e ].
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

  Remark label_in_lcmd_push_to_save to_save sp:
    label_in_lcmd (push_to_save liparams p to_save sp) = [::].
  Proof. apply label_in_lcmd_li_of_fopn_args. Qed.

  Remark label_in_lcmd_pop_to_save to_save sp :
    label_in_lcmd (pop_to_save liparams p to_save sp) = [::].
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
    cmd_rect nb_labels_MkI nb_labels_nil nb_labels_cons nb_labels_assign nb_labels_opn nb_labels_syscall nb_labels_if nb_labels_for nb_labels_while nb_labels_call.

  Definition linear_i_nb_labels : ∀ i, Pi i :=
    instr_Rect nb_labels_MkI nb_labels_nil nb_labels_cons nb_labels_assign nb_labels_opn nb_labels_syscall nb_labels_if nb_labels_for nb_labels_while nb_labels_call.

  Lemma linear_body_nb_labels fn e body :
    let: (lbl, lc) := linear_body liparams p fn e body in
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
    case: sf_return_address => [|x _|ra z _].
    + case: sf_save_stack => [|x|z] [<- <- <-] //=.
      + by rewrite set_up_sp_register_label_in_lcmd.

      rewrite !label_in_lcmd_cat.
      rewrite set_up_sp_register_label_in_lcmd /=.
      by rewrite label_in_lcmd_push_to_save label_in_lcmd_pop_to_save /=.

    + by move=> [<- <- <-] /=.
    by move=> [<- <- <-] /=; case: ra => //= r; case: get_label.
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

  Let vgd : var := Var (sword Uptr) (sp_rip (p_extra p)).
  Let vrsp : var := Var (sword Uptr) (sp_rsp (p_extra p)).
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

  Notation sem_I := (sem_one_varmap.sem_I p var_tmp).
  Notation sem_i := (sem_one_varmap.sem_i p var_tmp).
  Notation sem := (sem_one_varmap.sem p var_tmp).

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
    have := ih ((linear_body liparams p f (f_extra fd) (f_body fd)).1)%positive.
    have := ih (lbl + (linear_body liparams p f (f_extra fd) (f_body fd)).1)%positive.
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
    have := linear_body_nb_labels p liparams fn (f_extra f') (f_body f').
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
    + move=> p1 w1 hb /dup[] Hr1.
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
      - by move => al sz x e ihe v /=; t_xrbindP => ?? -> /= -> /= ?? /ihe -> /= -> /= ? /(mm_read_ok M) -> /= ->.
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
    move => M; case: x => /= [ _ ty | x | al ws x e | al aa ws x e | aa ws n x e ].
    - by case/write_noneP; rewrite /write_none => -[-> -> ->] -> ->; exists m1'.
    - rewrite /write_var /=; t_xrbindP =>_ -> -> <- -> /=.
      by exists m1'.
    - t_xrbindP => ?? -> /= -> /= ?? /(match_mem_gen_sem_pexpr M) -> /= -> /= ? -> /= ? /(mm_write M)[] ? -> /= M' <- <- <-.
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

  (* Define where/how the return address is pass by the caller to the callee *)
  Definition value_of_ra
    (m: mem)
    (vm: Vm.t)
    (ra: return_address_location)
    (target: option (remote_label * lcmd * nat))
    : Prop :=
    match ra, target with
    | RAnone, None => True
    | RAreg (Var (sword ws) _ as ra) _, Some ((caller, lbl), cbody, pc) =>
      if (ws == Uptr)%CMP
      then [/\ is_linear_of caller cbody,
            find_label lbl cbody = ok pc,
            (caller, lbl) \in label_in_lprog p' &
            exists2 ptr,
              encode_label (label_in_lprog p') (caller, lbl) = Some ptr &
              vm.[ra] = Vword (zero_extend ws ptr)
           ]
      else False

   | RAstack (Some (Var (sword ws) _ as ra)) _ _ , Some ((caller, lbl), cbody, pc) =>
      if (ws == Uptr)%CMP
      then [/\ is_linear_of caller cbody,
            find_label lbl cbody = ok pc,
            (caller, lbl) \in label_in_lprog p' &
            exists2 ptr,
              encode_label (label_in_lprog p') (caller, lbl) = Some ptr &
              vm.[ra] = Vword (zero_extend ws ptr)
           ]
      else False

    | RAstack None ofs _, Some ((caller, lbl), cbody, pc) =>
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
      move => al sz x e ok_s' ok_t' E X M; subst tscs.
      move: ok_s' => /=; t_xrbindP => a xv ok_xv ok_a ofs ev ok_ev ok_ofs w ok_w m' ok_m' _{s'}.
      move: ok_t' => /=.
      have [ xv' -> /= /of_value_uincl_te h ] := get_var_uincl X ok_xv.
      have {h} /= -> /= := (h (sword _) _ ok_a).
      have /= ok_ev' := match_mem_gen_sem_pexpr M ok_ev.
      have /(_ _ X) := sem_pexpr_uincl _ ok_ev'.
      case => ev' -> /of_value_uincl_te h /=.
      have {h} /= -> /= := (h (sword _) _ ok_ofs).
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


  (* ----------------------------------------------------------------------- *)
  Variant ex2_6 (T1 T2: Type) (A B C D E F : T1 → T2 → Prop) : Prop :=
    Ex2_6 x1 x2 of A x1 x2 & B x1 x2 & C x1 x2 & D x1 x2 & E x1 x2 & F x1 x2.

  Notation "'exists2_6' x y , p0 & p1 & p2 & p3 & p4 & p5" :=
    (ex2_6
       (fun x y => p0)
       (fun x y => p1)
       (fun x y => p2)
       (fun x y => p3)
       (fun x y => p4)
       (fun x y => p5))
    (at level 200, x name, p0 at level 200, right associativity) :
    type_scope.

  Let Pi (k: Sv.t) (s1: estate) (i: instr) (s2: estate) : Prop :=
    ∀ fn lbl,
      checked_i fn i →
      let: (lbli, li) := linear_i fn i lbl [::] in
     ∀ ls m1 vm1 P Q,
       match_mem_gen (top_stack m0) s1 m1 →
       evm s1 <=1 vm1 →
       disjoint_labels lbl lbli P →
       is_linear_of fn (P ++ li ++ Q) →
       lpc ls = size P ->
       lfn ls = fn ->
       ∀ sp,
         s1.(evm).[ vrsp ] = Vword sp →
         source_mem_split s1 sp →
         max_bound_sub fn sp →
         exists2_6 m2 vm2,
           let: ls0 := lset_estate ls (escs s1) m1 vm1 in
           let: ls1 := lset_estate ls (escs s2) m2 vm2 in
           lsem p' ls0 (setpc ls1 (size (P ++ li)))
           & vm1 =[\ k ] vm2
           & s2 <=1 vm2
           & preserved_metadata s1 m1 m2
           & match_mem_gen (top_stack m0) s2 m2
           & target_mem_unchanged m1 m2.

  Let Pi_r (ii: instr_info) (k: Sv.t) (s1: estate) (i: instr_r) (s2: estate) : Prop :=
    ∀ fn lbl,
      checked_i fn (MkI ii i) →
      let: (lbli, li) := linear_i fn (MkI ii i) lbl [::] in
     ∀ ls m1 vm1 P Q,
       match_mem_gen (top_stack m0) s1 m1 →
       evm s1 <=1 vm1 →
       disjoint_labels lbl lbli P →
       is_linear_of fn (P ++ li ++ Q) →
       lpc ls = size P ->
       lfn ls = fn ->
       ∀ sp,
        s1.(evm).[ vrsp ] = Vword sp →
        source_mem_split s1 sp →
        max_bound_sub fn sp →
        exists2_6 m2 vm2,
          let: ls0 := lset_estate ls (escs s1) m1 vm1 in
          let: ls1 := lset_estate ls (escs s2) m2 vm2 in
          lsem p' ls0 (setpc ls1 (size (P ++ li)))
          & vm1 =[\ k ] vm2
          & s2 <=1 vm2
          & preserved_metadata s1 m1 m2
          & match_mem_gen (top_stack m0) s2 m2
          & target_mem_unchanged m1 m2.

  Let Pc (k: Sv.t) (s1: estate) (c: cmd) (s2: estate) : Prop :=
    ∀ fn lbl,
      checked_c fn c →
      let: (lblc, lc) := linear_c fn c lbl [::] in
     ∀ ls m1 vm1 P Q,
       match_mem_gen (top_stack m0) s1 m1 →
       evm s1 <=1 vm1 →
       disjoint_labels lbl lblc P →
       is_linear_of fn (P ++ lc ++ Q) →
       lpc ls = size P ->
       lfn ls = fn ->
       ∀ sp,
        s1.(evm).[ vrsp ] = Vword sp →
        source_mem_split s1 sp →
        max_bound_sub fn sp →
        exists2_6 m2 vm2,
          let: ls0 := lset_estate ls (escs s1) m1 vm1 in
          let: ls1 := lset_estate ls (escs s2) m2 vm2 in
          lsem p' ls0 (setpc ls1 (size (P ++ lc)))
          & vm1 =[\ k ] vm2
          & s2 <=1 vm2
          & preserved_metadata s1 m1 m2
          & match_mem_gen (top_stack m0) s2 m2
          & target_mem_unchanged m1 m2.

  (* Assuming [fn] takes [(scs1, m1, vm1)] to [(scs2, m2, vm2)],
     we need to prove that its compilation has the same behavior, and
     - if it's an export function (that is, [lret] is [None]), we are done.
     - if it's a callee ([lret] carries the caller), we return.
     Note that if it's a calle then we start execution at position 1 (because
     the first instruction is just the label). *)
  Definition pfun_preserved
    (lret : option (remote_label * lcmd * nat))
    ls nbody scs1 m1 vm1 scs2 m2 vm2 :=
    let: ls1 := lset_estate ls scs1 m1 vm1 in
    let: ls2 := lset_estate ls scs2 m2 vm2 in
    if lret is Some ((caller, lbl), _, pc)
    then lsem p' (setpc ls1 1) (setcpc ls2 caller pc.+1)
    else lsem p' (setpc ls1 0) (setpc ls2 nbody).

  Definition killed_on_entry (ra : return_address_location) : Sv.t :=
    match ra with
    | RAnone => var_tmps
    | RAreg x _ => Sv.singleton x
    | RAstack or _ _ => sv_of_option or
    end.

  (* The set of variable killed/written by the execution of the function,
     for export function saved are removed since those variables are restored *)
  Definition killed_on_exit
    (ra : return_address_location) (killed saved : Sv.t) : Sv.t :=
    match ra with
    | RAnone => Sv.diff killed saved
    | RAreg _ _ => killed
    | RAstack _ _ _ => Sv.add vrsp killed
    end.

  (* The set of variable written by the execution of the exit code of function *)
  Definition killed_by_exit
    (ra : return_address_location) (saved : Sv.t) : Sv.t :=
    match ra with
    | RAnone => Sv.add var_tmp2 saved
    | RAreg _ _ => saved
    | RAstack _ _ _ => saved
    end.

  Definition sp_alloc_ra
    (sp : word Uptr) (ra : return_address_location) : word Uptr :=
    if is_RAstack ra then (sp + wrepr _ (wsize_size Uptr))%R else sp.

  Let Pfun (ii: instr_info) (k: Sv.t) (s1: estate) (fn: funname) (s2: estate) : Prop :=
    ∀ ls m1 vm1 body ra lret sp callee_saved,
      match_mem_gen (top_stack m0) s1 m1 →
      (kill_vars (killed_on_entry ra) s1).[vrsp <- Vword sp] <=1 vm1 →
      is_linear_of fn body →
      lfn ls = fn ->
      (* RA contains a safe return address “lret” *)
      is_ra_of fn ra →
      value_of_ra m1 vm1 ra lret →
      (* RSP points to the top of the stack according to the calling convention *)
      is_sp_for_call fn s1 sp →
      (* To-save variables are initialized in the initial linear state *)
      is_callee_saved_of fn callee_saved →
      vm_initialized_on vm1 callee_saved →
      source_mem_split s1 (top_stack (emem s1)) ->
      max_bound fn (top_stack (emem s1)) ->
      (∀ fd, get_fundef (p_funcs p) fn = Some fd ->
        if is_RAnone (sf_return_address (f_extra fd)) then m0 = emem s1 else True) ->
      let: ssaved := sv_of_list id callee_saved in
      exists2_6 m2 vm2,
        pfun_preserved lret ls (size body) (escs s1) m1 vm1 (escs s2) m2 vm2
        & vm1 =[\ killed_on_exit ra k ssaved ] vm2
        & (kill_vars (killed_by_exit ra ssaved) s2).[vrsp <- Vword (sp_alloc_ra sp ra)] <=1 vm2
        & preserved_metadata s1 m1 m2
        & match_mem_gen (top_stack m0) s2 m2
        & target_mem_unchanged m1 m2.

  Local Lemma Hnil : sem_Ind_nil Pc.
  Proof.
    move=> s1 fn lbl _ ls m1 vm1 ?????? hpc _.
    rewrite cats0 -hpc.
    by eexists; first exact: rt_refl.
  Qed.

  Lemma RSP_in_magic :
    Sv.In vrsp (magic_variables p).
  Proof. by rewrite Sv.add_spec Sv.singleton_spec; right. Qed.

  Local Lemma Hcons : sem_Ind_cons p var_tmps Pc Pi.
  Proof.
    move => ki kc s1 s2 s3 i c exec_i hi _ hc.
    move => fn lbl /checked_cI[] chk_i chk_c /=.
    case: (linear_c fn) (valid_c fn c lbl) (hc fn lbl chk_c) => lblc lc [Lc Vc] Sc.
    rewrite linear_i_nil.
    case: linear_i (valid_i fn i lblc) (hi fn lblc chk_i) => lbli li [Li Vi] Si.
    move=> ls m1 vm1 P Q Mc Xc Dc C hpc hfn sp hsp S MAX.

    set ls0 := lset_estate _ _ _ _.
    have D : disjoint_labels lblc lbli P.
    + apply: (disjoint_labels_wL _ Dc); exact: Lc.
    have C' : is_linear_of fn (P ++ li ++ lc ++ Q).
    + by move: C; rewrite !catA.
    have [m2 vm2 Ei Ki Xi Hi Mi Ui] :=
      Si ls0 m1 vm1 P (lc ++ Q) Mc Xc D C' hpc hfn sp hsp S MAX.

    set ls1 := setpc (lset_estate ls (escs s3) m2 vm2) (size (P ++ li)).
    have Di : disjoint_labels lbl lblc (P ++ li).
    + apply: disjoint_labels_cat.
      * apply: (disjoint_labels_wH _ Dc); exact: Li.
      apply: (valid_disjoint_labels Vi); lia.
    have Ci : is_linear_of fn ((P ++ li) ++ lc ++ Q).
    + by move: C; rewrite !catA.
    have hsp': s2.[vrsp] = Vword sp.
    + rewrite -(sem_I_preserved_RSP_GD var_tmps_not_magic exec_i) //.
      by apply RSP_in_magic.
    have S': source_mem_split s2 sp.
    + by move=> pr; rewrite -(sem_I_validw_stable exec_i); apply S.
    have [m3 vm3] := Sc ls1 m2 vm2 (P ++ li) Q Mi Xi Di Ci erefl hfn sp hsp' S' MAX.
    rewrite -!catA => E K X H M U.
    exists m3 vm3 => //.
    + exact: lsem_trans Ei E.
    + apply (@eq_exT _ vm2).
      + apply: eq_exI Ki.
        exact: Sv_Subset_union_left.
      apply: eq_exI K.
      exact: Sv_Subset_union_right.
    + etransitivity; first exact: Hi.
      apply: preserved_metadataE H.
      + exact: sem_I_stack_stable exec_i.
      exact: sem_I_validw_stable exec_i.
    move=> pr hnv hnpr.
    rewrite (Ui pr hnv hnpr).
    by rewrite (U pr hnv hnpr).
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p var_tmps Pi Pi_r.
  Proof.
    move => ii k i s1 s2 ok_fr h _ fn lbl chk.
    move: h => /(_ fn lbl chk); case: linear_i (valid_i fn (MkI ii i) lbl) => lbli li [L V] S.
    move=> ls m1 vm1 P Q M X D C hpc hfn sp hsp SM MAX.
    have {M X} [m2 vm2 E K X H M U] := S _ _ vm1 _ _ M X D C hpc hfn sp hsp SM MAX.
    eexists; by eauto.
  Qed.

  Local Lemma Hasgn : sem_Ind_assgn p Pi_r.
  Proof. by move => ii s1 s2 x tg ty e v v' ok_v ok_v' ok_s2 fn lbl /checked_iE[]. Qed.

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

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move => ii s1 s2 tg op xs es; rewrite /sem_sopn; t_xrbindP => rs vs.
    rewrite p_globs_nil => ok_vs ok_rs ok_s2.
    move => fn lbl /checked_iE[] fd ok_fd.
    rewrite /check_i; t_xrbindP => /check_rexprsP[] qs ok_qs chk_es /check_lexprsP[] ds ok_ds chk_xs.
    rewrite /= ok_ds ok_qs.
    move=> ls m1 vm1 P Q M1 X1 D1 C1 hpc hfn sp hsp1 S1 MAX1.
    have [ vs' /(match_mem_gen_sem_pexprs M1) /chk_es ok_vs' vs_vs' ] := sem_pexprs_uincl X1 ok_vs.
    have [ rs' ok_rs' rs_rs' ] := vuincl_exec_opn vs_vs' ok_rs.
    have [ vm2 /(match_mem_gen_write_lvals M1) [ m2 ok_s2' M2 ] ok_vm2 ] := writes_uincl X1 rs_rs' ok_s2.
    exists m2 vm2 => //.
    + apply: (eval_lsem_step1 C1) => //.
      have {} ok_s2' := chk_xs _ _ _ ok_s2'.
      by rewrite /eval_instr /= ok_vs' /= ok_rs' /= ok_s2' size_cat addn1 -hpc.
    + exact: vrvsP ok_s2'.
    + exact: preserved_metadata_write_lvals ok_s2 ok_s2' _ X1 M1.
    move=> pr hnv hnpr.
    apply (write_lvals_mem_unchanged rs_rs' ok_s2 ok_s2' erefl X1 M1).
    apply /negP => /S1 /orP [//|].
    move=> hpr; apply hnpr.
    apply: pointer_range_incl_l hpr.
    have ?: (wunsigned sp0 - max0 <= wunsigned sp)%Z.
    + have /= := MAX1 _ ok_fd.
      move: (checked_prog ok_fd) => /=; rewrite /check_fd.
      t_xrbindP=> _ _ /and4P [_ _ _ /ZleP /= ?] _ _ _.
      by lia.
    rewrite wunsigned_sub; first by lia.
    by have := wunsigned_range sp; lia.
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
    move=> mm; rewrite /exec_syscall_s; t_xrbindP => -[[scs' m'] t] happ [<- <- <-].
    have h: mk_forall_ex (fun e1 e2 => [/\ e1.1.1 = e2.1.1, e1.2 = e2.2 &  match_mem_gen (top_stack m0) e1.1.2 e2.1.2])
                             (sem_syscall o scs1 m1) (sem_syscall o scs1 m1').
    + case: (o) => _ /= wp len [[scs_ rm] t_].
      rewrite /exec_getrandom_s_core; t_xrbindP => ? /(match_mem_gen_fill_mem mm) [] rm' -> ? -> <- <- /=; by eexists.
    have [[[ _ rm' ] _ ] -> /= [] <- <-]:= mk_forall_exP h happ; by eexists.
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
    t_xrbindP=> _ m1'' hw1 <- /ih{ih}ih _ m2'' hw2 <- /ih{ih}ih pr hnv.
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
    move=> hall hex; have {}:= exec_syscallPs_eq hex hall.
    rewrite /exec_syscall_s; t_xrbindP => -[[scs0 m1''] t0] happ1 [???] -[[scs1 m2''] t1] happ2 [???].
    subst scs1 scs0 m1'' m2'' vs vs'.
    have h : mk_forall2 (fun o1 o2 => forall p, ~~ validw m1 Aligned p U8 -> read m2 Aligned p U8 = read o2.1.2 Aligned p U8)
               (sem_syscall o scs m1) (sem_syscall o scs m2).
    + case: (o) => _ /= ptr bytes ??.
      rewrite /exec_getrandom_s_core; t_xrbindP => ? hf1 ? ? hf2 <- /=.
      by apply: fill_mem_mem_unchanged hf1 hf2.
    by apply: mk_forall2P h happ1 happ2.
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

  Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> ii s1 s2 o xs es scs m ves vs hes ho.
    rewrite p_globs_nil => hw fn lbl /checked_iE [] fd ok_fd chk.
    move=> ls m1 vm1 P Q M1 X1 D1 C1 hpc hfn sp hsp1 S1 MAX1.
    have [ves' hes' uves] := get_vars_uincl X1 hes.
    have [vs' /= ho' uvs]:= exec_syscallP ho uves.
    have [m' {ho'}ho' mm]:= match_mem_gen_exec_syscall M1 ho'.
    have /(_ _ (vm_after_syscall_uincl X1)) := writes_uincl _ uvs hw.
    move=> [] vm2 /= /(match_mem_gen_write_lvals mm) [ m2 /= ok_s2' M2 ] ok_vm2 .
    exists m2 vm2 => //.
    + apply: (eval_lsem_step1 C1) => //.
      by rewrite /eval_instr /= hes' /= ho' /= ok_s2' size_cat addn1 -hpc.
    + apply: (eq_exT (vm2 := vm_after_syscall vm1)).
      + by apply: eq_exI (syscall_killP vm1); SvD.fsetdec.
      by apply: eq_exI; last apply: vrvsP ok_s2'; SvD.fsetdec.
    + transitivity m'; first by apply (preserved_metadata_syscall uves ho ho').
      have [hss hveq] := exec_syscallSs ho.
      apply (preserved_metadataE hss hveq).
      by apply (preserved_metadata_write_lvals uvs hw ok_s2' erefl (vm_after_syscall_uincl X1) mm).
    move=> pr hnv hnpr.
    have hnv1: ~~ validw (emem s1) Aligned pr U8.
    + apply /negP; move=> /S1 /orP [//|].
      move=> hpr; apply hnpr.
      apply: pointer_range_incl_l hpr.
      have ?: (wunsigned sp0 - max0 <= wunsigned sp)%Z.
      + have /= := MAX1 _ ok_fd.
        move: (checked_prog ok_fd) => /=; rewrite /check_fd.
        t_xrbindP=> _ _ /and4P [_ _ _ /ZleP /= ?] _ _ _.
        by lia.
      rewrite wunsigned_sub; first by lia.
      by have := wunsigned_range sp; lia.
    rewrite (exec_syscall_mem_unchanged uves ho ho' hnv1) .
    apply (write_lvals_mem_unchanged uvs hw ok_s2' erefl (vm_after_syscall_uincl X1) mm).
    by rewrite /= -(proj2 (exec_syscallSs ho)).
  Qed.

  (* TODO: move ? *)
  Remark next_lbl_neq (lbl: label) :
    ((lbl + 1)%positive == lbl) = false.
  Proof.
    apply/eqP => k.
    suff : (lbl < lbl)%positive by lia.
    rewrite -{2}k; lia.
  Qed.

  Let Lilabel := linear.Llabel InternalLabel.

  Local Lemma Hif_true : sem_Ind_if_true p var_tmps Pc Pi_r.
  Proof.
    move => ii k s1 s2 e c1 c2; rewrite p_globs_nil => ok_e E1 Hc1 fn lbl /checked_iE[] fd ok_fd /=.
    t_xrbindP => /check_fexprP[] f ok_f chk_c1 _.
    rewrite /to_fexpr ok_f.
    case: c1 E1 Hc1 chk_c1 => [ | i1 c1 ] E1 Hc1 chk_c1; last case: c2 => [ | i2 c2 ].
    + case/semE: E1 => hk ?; subst s2.
      rewrite /= linear_c_nil; case: (linear_c fn) (valid_c fn c2 (next_lbl lbl)) => lbl2 lc2.
      rewrite /next_lbl => - [L V].
      move=> ls m1 vm1 P Q M1 X1 D C1 hpc hfn sp hsp1 S1 MAX1.
      have [ b /(match_mem_gen_sem_pexpr M1) ok_e' /value_uinclE ? ] := sem_pexpr_uincl X1 ok_e; subst b.
      have {} ok_e' := fexpr_of_pexprP ok_f ok_e'.
      exists m1 vm1 => //.
      apply: (eval_lsem_step1 C1) => //.
      rewrite /eval_instr /= hfn (eval_jumpE C1) ok_e' /=.
      rewrite find_label_cat_hd; last by apply: D; lia.
      rewrite find_labelE /= -catA find_label_cat_hd; last first.
      * apply: (valid_has_not_label V); left; rewrite /next_lbl; lia.
      rewrite /= find_labelE /is_label /= eqxx /= /setcpc /= addn0.
      by rewrite size_cat /= size_cat /= !addn1 !addnS -hpc -hfn.
    + rewrite linear_c_nil.
      case: (to_fexpr_snot ok_f) => nf ok_nf.
      rewrite ok_nf.
      case: (linear_c fn) (Hc1 fn (next_lbl lbl)) => lbl1 lc1.
      rewrite /checked_c ok_fd chk_c1 => /(_ erefl) S.
      move=> ls m1 vm1 P Q M1 X1 D C1 hpc hfn sp hsp1 S1 MAX1.
      set P' := rcons P (MkLI ii (Lcond nf lbl)).
      have D' : disjoint_labels (next_lbl lbl) lbl1 P'.
      - rewrite /P' -cats1; apply: disjoint_labels_cat; last by [].
        apply: disjoint_labels_wL _ D; rewrite /next_lbl; lia.
      set Q' := MkLI ii (Lilabel lbl) :: Q.
      have C' : is_linear_of fn (P' ++ lc1 ++ Q').
      - by move: C1; rewrite /P' /Q' -cats1 /= -!catA.

      have {S} [|m2 vm2 E K2 X2 H2 M2 U2] :=
        S (lnext_pc ls) m1 vm1 P' Q' M1 X1 D' C' _ hfn sp hsp1 S1 MAX1.
      - by rewrite /P' /= hpc size_rcons.
      have [ b /(match_mem_gen_sem_pexpr M1) ok_e' /value_uinclE ? ] := sem_pexpr_uincl X1 ok_e; subst b.
      exists m2 vm2 => //.
      apply: (lsem_trans3 _ E).
      - have /= := snot_spec ok_e'.
        rewrite ok_e' => /(fexpr_of_pexprP ok_nf) {} ok_e'.
        apply: (eval_lsem_step1 C1) => //.
        by rewrite /eval_instr /= hfn (eval_jumpE C1) ok_e'.
      rewrite catA in C'.
      apply: (eval_lsem_step1 C') => //.
      by rewrite /P' -cats1 -!catA !size_cat /= size_cat /= !addnS addn0.

    rewrite linear_c_nil.
    case: (linear_c fn) (valid_c fn (i1 :: c1) (next_lbl (next_lbl lbl))) (Hc1 fn (next_lbl (next_lbl lbl))) => lbl1 lc1.
    rewrite /next_lbl => -[L V].
    rewrite /checked_c ok_fd chk_c1 => /(_ erefl) E.
    rewrite linear_c_nil.
    case: (linear_c fn) (valid_c fn (i2 :: c2) lbl1) => lbl2 lc2 [L2 V2].
    move=> ls m1 vm1 P Q M1 X1 D C hpc hfn sp hsp1 S1 MAX1.
    have [ b /(match_mem_gen_sem_pexpr M1) ok_e' /value_uinclE ? ] := sem_pexpr_uincl X1 ok_e; subst b.
    set licond := {| li_i := Lcond _ _; |}.
    set ligoto := {| li_i := Lgoto _; |}.
    set lilabel := {| li_i := Lilabel _; |}.
    set lilabel' := {| li_i := Lilabel _; |}.
    set P' := P ++ licond :: lc2 ++ [:: ligoto; lilabel ].
    set Q' := lilabel' :: Q.

    have D' : disjoint_labels (lbl + 1 + 1) lbl1 P'.
    + apply: disjoint_labels_cat; first by apply: disjoint_labels_w _ _ D; lia.
      apply: disjoint_labels_cat; first by apply: (valid_disjoint_labels V2); lia.
      move => lbl' [A B]; rewrite /= orbF /is_label /=; apply/eqP => ?; subst lbl'; lia.
    have C' : is_linear_of fn (P' ++ lc1 ++ Q').
    + by move: C; rewrite /P' /Q' /= -!catA /= -!catA.
    have {E} [m2 vm2 E K2 X2 H2 M2 U2] :=
      E (setpc ls (size P')) m1 vm1 P' Q' M1 X1 D' C' erefl hfn sp hsp1 S1 MAX1.

    exists m2 vm2 => //.
    apply: (lsem_trans3 _ E).
    - have {} ok_e' := fexpr_of_pexprP ok_f ok_e'.
      apply: (eval_lsem_step1 C) => //.
      rewrite /eval_instr /= hfn (eval_jumpE C) ok_e' /=.
      rewrite find_label_cat_hd; last by apply: D; lia.
      rewrite find_labelE /= -catA find_label_cat_hd; last first.
      * apply: (valid_has_not_label V2); lia.
      rewrite find_labelE /= find_labelE /is_label /= eqxx /=.
      by rewrite /setcpc /= /P' size_cat /= size_cat /= !addnS -hfn.
    rewrite catA in C'.
    apply: (eval_lsem_step1 C') => //.
    rewrite /eval_instr /= /P' /Q' -!catA /= -!catA.
    repeat rewrite !size_cat /=.
    by rewrite !addnS !addn0.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p var_tmps Pc Pi_r.
  Proof.
    move => ii k s1 s2 e c1 c2; rewrite p_globs_nil => ok_e E2 Hc2 fn lbl /checked_iE[] fd ok_fd /=.
    t_xrbindP => /check_fexprP[] f ok_f _ chk_c2.
    rewrite /to_fexpr ok_f.
    case: c1 => [ | i1 c1 ]; last case: c2 E2 Hc2 chk_c2 => [ | i2 c2 ].
    + rewrite linear_c_nil.
      case: (linear_c fn) (Hc2 fn (next_lbl lbl)) => lbl2 lc2.
      rewrite /checked_c ok_fd chk_c2 => /(_ erefl) S.
      move=> ls m1 vm1 P Q M1 X1 D C hpc hfn sp hsp1 S1 MAX1.
      set P' := rcons P (MkLI ii (Lcond f lbl)).
      have D' : disjoint_labels (next_lbl lbl) lbl2 P'.
      - rewrite /P' -cats1; apply: disjoint_labels_cat; last by [].
        apply: disjoint_labels_wL _ D; rewrite /next_lbl; lia.
      set Q' := MkLI ii (Lilabel lbl) :: Q.
      have C' : is_linear_of fn (P' ++ lc2 ++ Q').
      - by move: C; rewrite /P' /Q' -cats1 /= -!catA.
      have {S} [|m2 vm2 E K2 X2 H2 M2 U2] :=
        S (setpc ls (size P')) m1 vm1 P' Q' M1 X1 D' C' _ hfn sp hsp1 S1 MAX1.
      - by rewrite /P' size_rcons.
      have [ b /(match_mem_gen_sem_pexpr M1) ok_e' /value_uinclE ? ] := sem_pexpr_uincl X1 ok_e; subst b.
      exists m2 vm2 => //.
      apply: (lsem_trans3 _ E).
      - have {} ok_e' := fexpr_of_pexprP ok_f ok_e'.
        apply: (eval_lsem_step1 C) => //.
        rewrite /eval_instr /= hfn (eval_jumpE C) ok_e'.
        by rewrite /P' size_rcons -hpc.
      rewrite catA in C'.
      apply: (eval_lsem_step1 C') => //.
      by rewrite /P' -cats1 -!catA !size_cat /= size_cat /= !addnS !addn0 -hpc.
    + case/semE => hk ? _ _; subst s2.
      case: (to_fexpr_snot ok_f) => nf ok_nf.
      rewrite ok_nf.
      rewrite linear_c_nil; case: (linear_c fn) (valid_c fn (i1 :: c1) (next_lbl lbl)) => lbl1 lc1.
      rewrite /next_lbl => - [L V].
      move=> ls m1 vm1 P Q M1 X1 D C hpc hfn.
      have [ b /(match_mem_gen_sem_pexpr M1) ok_e' /value_uinclE ? ] := sem_pexpr_uincl X1 ok_e; subst b.
      exists m1 vm1 => //.
      have /= := snot_spec ok_e'.
      rewrite ok_e' => /(fexpr_of_pexprP ok_nf) {} ok_e'.
      apply: (eval_lsem_step1 C) => //.
      rewrite /eval_instr /= hfn (eval_jumpE C) ok_e' /=.
      rewrite find_label_cat_hd; last by apply: D; lia.
      rewrite find_labelE /= -catA find_label_cat_hd; last first.
      - apply: (valid_has_not_label V); left; rewrite /next_lbl; lia.
      rewrite /= find_labelE /is_label /= eqxx /= addn0.
      by rewrite size_cat /= size_cat /= addn1 -addnS -hfn -hpc.

    rewrite linear_c_nil => _ Hc2 chk_c2.
    case: (linear_c fn) (valid_c fn (i1 :: c1) (next_lbl (next_lbl lbl))) => lbl1 lc1.
    rewrite /next_lbl => -[L V].
    rewrite linear_c_nil.
    case: (linear_c fn) (valid_c fn (i2 :: c2) lbl1) (Hc2 fn lbl1) => lbl2 lc2 [L2 V2].
    rewrite /checked_c ok_fd chk_c2 => /(_ erefl) E.
    move=> ls m1 vm1 P Q M1 X1 D C hpc hfn sp hsp1 S1 MAX1.
    have [ b /(match_mem_gen_sem_pexpr M1) ok_e' /value_uinclE ? ] := sem_pexpr_uincl X1 ok_e; subst b.
    set licond := {| li_i := Lcond _ _; |}.
    set ligoto := {| li_i := Lgoto _; |}.
    set lilabel := {| li_i := Lilabel _; |}.
    set lilabel' := {| li_i := Lilabel _; |}.
    set P' := rcons P licond.
    set Q' := ligoto :: lilabel :: lc1 ++ [:: lilabel' ].

    have D' : disjoint_labels lbl1 lbl2 P'.
    + rewrite /P' -cats1; apply: disjoint_labels_cat; last by [].
      apply: disjoint_labels_wL _ D; lia.
    have C' : is_linear_of fn (P' ++ lc2 ++ Q' ++ Q).
    + by move: C; rewrite /P' /Q' /= -cats1 /= -!catA /= -!catA.
    have {E} [|m2 vm2 E K2 X2 H2 M2 U2] :=
      E (setpc ls (size P')) m1 vm1 P' (Q' ++ Q) M1 X1 D' C' _ hfn sp hsp1 S1 MAX1.
    - by rewrite /P' size_rcons.

    exists m2 vm2 => //.
    apply: (lsem_trans3 _ E).
    + have {} ok_e' := fexpr_of_pexprP ok_f ok_e'.
      apply: (eval_lsem_step1 C) => //.
      rewrite /eval_instr /= hfn (eval_jumpE C) ok_e' /=.
      by rewrite /P' /Q' /= size_rcons -hpc.

    rewrite catA in C'.
    apply: (eval_lsem_step1 C') => //.
    rewrite /eval_instr /= (eval_jumpE C') /P' -cats1.
    rewrite -!catA find_label_cat_hd; last by apply: D; lia.
    rewrite find_labelE /= find_label_cat_hd; last by apply: (valid_has_not_label V2); lia.
    rewrite find_labelE /= find_labelE /is_label /= next_lbl_neq.
    rewrite -catA find_label_cat_hd;
      last by apply: (valid_has_not_label V); lia.
    by rewrite
      find_labelE /is_label /= eqxx /= /Q' !size_cat /= size_cat /= size_cat /=
      !addnS !addnA -hfn.
  Qed.

  Section SKIP.

  Context
    {fn : funname}
    {n : nat}
    {P Q : lcmd}
    {ls ls' : lstate}
    (hpc : lpc ls = size P)
    (hfn : lfn ls = fn)
  .

  Lemma lsem_skip_align ii a :
    let: skipped := add_align ii a [::] in
    let: pc' := (size (P ++ skipped) + n)%nat in
    is_linear_of fn (P ++ skipped ++ Q) ->
    lpc ls' = pc' ->
    lsem p' ls ls' ->
    lsem p' (setpc ls (size (P ++ skipped))) ls'.
  Proof.
    move: a => []; last by rewrite cats0 -hpc setpc_id.
    rewrite size_cat /= addn1.
    move=> hbody hpc' /lsem_split_start [? | [ls0 hsem1 hsem]].
    - subst ls'. move: hpc. rewrite hpc' /addn /addn_rec. lia.
    apply: (lsem_trans _ hsem).
    move: hsem1.
    rewrite /lsem1 /step (find_instr_skip0 hbody) //= -hpc.
    move=> [<-].
    exact: rt_refl.
  Qed.

  Lemma lsem_skip_label lk ii lbl :
    let: skipped := [:: {| li_ii := ii ; li_i := Llabel lk lbl |} ] in
    let: pc' := (size P + n.+1)%nat in
    is_linear_of fn (P ++ skipped ++ Q) ->
    lpc ls' = pc' ->
    lsem p' ls ls' ->
    lsem p' (setpc ls (size P).+1) ls'.
  Proof.
    move=> hbody hpc' /lsem_split_start [? | [ls0 hsem1 hsem]].
    - subst ls'. move: hpc. rewrite hpc' /addn /addn_rec. lia.
    apply: (lsem_trans _ hsem).
    move: hsem1.
    rewrite /lsem1 /step (find_instr_skip0 hbody) //= -hpc.
    move=> [<-].
    exact: rt_refl.
  Qed.

  Lemma lsem_skip_goto lk ii jj lbl R :
    let: pc' := (size P + n.+1)%nat in
    let: ligoto := {| li_ii := ii; li_i := Lgoto (fn, lbl); |} in
    let: lilabel := {| li_ii := jj; li_i := Llabel lk lbl; |} in
    is_linear_of fn (P ++ [:: ligoto ] ++ Q ++ [:: lilabel ] ++ R) ->
    lpc ls' = pc' ->
    ~~ has (is_label lbl) P ->
    ~~ has (is_label lbl) Q ->
    lsem p' ls ls' ->
    lsem p' (setpc ls (size P + size Q).+2) ls'.
  Proof.
    move=> hbody hpc' Dp Dq /lsem_split_start [? | [ls0 hsem1 hsem]].
    - subst ls'. move: hpc. rewrite hpc' /addn /addn_rec. lia.
    apply: (lsem_trans _ hsem).
    move: hsem1.
    rewrite /lsem1 /step (find_instr_skip0 hbody) //=.
    rewrite /eval_instr /= (eval_jumpE hbody) /=.
    rewrite find_label_cat_hd; last exact: Dp.
    rewrite find_labelE /= find_label_cat_hd; last exact: Dq.
    rewrite find_labelE /is_label /= eqxx /= !addn0 addnS -hfn.
    move=> [<-].
    exact: rt_refl.
  Qed.

  Lemma lsem_align_label_id ii a lk lbl :
    let: lcalign := add_align ii a [::] in
    let: lilabel := {| li_ii := ii; li_i := Llabel lk lbl; |} in
    is_linear_of fn (P ++ lcalign ++ lilabel :: Q) ->
    lsem p' ls (setpc ls (size (P ++ lcalign ++ [:: lilabel ]))).
  Proof.
    move=> hbody.
    apply: lsem_step_end; first last.
    - rewrite catA in hbody.
      rewrite catA size_cat /= addn1.
      exact: (eval_lsem1 (ls := setpc ls (size (P ++ _))) hbody).
    case: a hbody => hbody.
    - apply: (eval_lsem_step1 hbody) => //.
      by rewrite /eval_instr /= size_cat /= addn1 -hpc.
    rewrite cats0 -hpc setpc_id.
    exact: rt_refl.
  Qed.

  End SKIP.

  Local Lemma Hwhile_true : sem_Ind_while_true p var_tmps Pc Pi Pi_r.
  Proof.
    red. clear Pfun.
    move => ii k k' krec s1 s2 s3 s4 a c e c' Ec Hc ok_e Ec' Hc' Ew Hw.
    move => fn lbl /checked_iE[] fd ok_fd /=.
    have {Hw} := Hw fn lbl.
    rewrite /checked_i ok_fd /=.
    move: ok_e Ew.
    rewrite p_globs_nil.
    case: is_boolP.
    { (* expression is the “true” literal *)
      (* The context is inconsistent, but well, do the proof nonetheless *)
      case; last by [].
      move => _ Ew Hw.
      t_xrbindP => ok_c ok_c'.
      move: Hw.
      rewrite ok_c ok_c' => /(_ erefl).
      rewrite linear_c_nil.
      move: {Hc'} (Hc' fn (next_lbl lbl)).
      rewrite /checked_c ok_fd ok_c' => /(_ erefl).
      case: (linear_c fn c' (next_lbl lbl) [::]) (valid_c fn c' (next_lbl lbl)) => lblc' lc'.
      rewrite /next_lbl => - [L' V'] Hc'.
      rewrite linear_c_nil.
      move: {Hc} (Hc fn lblc').
      rewrite /checked_c ok_fd ok_c => /(_ erefl).
      case: (linear_c fn c lblc' [::]) (valid_c fn c lblc') => lblc lc [L V] Hc /= Hw.
      rewrite add_align_nil.
      move=> ls m vm P Q M X D C hpc hfn sp hsp S MAX.
      set lcalign := add_align _ _ _.
      set lilabel := {| li_i := Lilabel _; |}.
      set ligoto := {| li_i := Lgoto _; |}.
      set P0 := P ++ lcalign ++ [:: lilabel ].
      set Q0 := lc' ++ [:: ligoto ] ++ Q.

      have {Hc} := Hc (setpc ls (size P0)) m vm P0 Q0 M X _ _ _ _ sp hsp S MAX.
      case=> //.
      - apply: disjoint_labels_cat; last apply: disjoint_labels_cat.
        + apply: disjoint_labels_wL D; lia.
        + subst lcalign. by case: (a).
        move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
      - move: C. by rewrite -!catA /= -!catA cat1s.
      move => m1 vm1 E1 K1 X1 H1 M1 U1.
      have hsp1: s2.[vrsp] = Vword sp.
      + rewrite -(sem_preserved_RSP_GD var_tmps_not_magic Ec) //.
        by apply RSP_in_magic.
      have S1: source_mem_split s2 sp.
      + by move=> pr; rewrite -(sem_validw_stable Ec); apply S.
      set P1 := P0 ++ lc.
      subst P0 Q0.
      set Q1 := [:: ligoto ] ++ Q.
      have {Hc'} :=
        Hc' (setpc ls (size P1)) m1 vm1 P1 Q1 M1 X1 _ _ _ _ sp hsp1 S1 MAX.
      case=> //.
      - repeat apply: disjoint_labels_cat.
        + apply: disjoint_labels_w D; lia.
        + subst lcalign. by case: (a).
        + move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
        apply: (valid_disjoint_labels V); left; lia.
      - by move: C; rewrite /= -!catA /= -!catA.
      move => m2 vm2 E2 K2 X2 H2 M2 U2.
      have hsp2: s3.[vrsp] = Vword sp.
      + rewrite -(sem_preserved_RSP_GD var_tmps_not_magic Ec') //.
        by apply RSP_in_magic.
      have S2: source_mem_split s3 sp.
      + by move=> pr; rewrite -(sem_validw_stable Ec'); apply S1.
      have {Hw} := Hw ls m2 vm2 P Q M2 X2 D _ hpc hfn sp hsp2 S2 MAX.
      case.
      - by rewrite add_align_nil.
      move => m3 vm3 E3 K3 X3 H3 M3 U3.
      exists m3 vm3 => //; cycle 1.
      - transitivity vm2; last (apply: eq_exI K3; SvD.fsetdec).
        transitivity vm1; last (apply: eq_exI K2; SvD.fsetdec).
        apply: eq_exI K1; SvD.fsetdec.
      - etransitivity; first exact: H1.
        apply: preserved_metadataE; last (etransitivity; first exact: H2); last first.
        + apply: preserved_metadataE; last exact: H3.
          * exact: sem_stack_stable Ec'.
          exact: sem_validw_stable Ec'.
        + exact: sem_validw_stable Ec.
        exact: sem_stack_stable Ec.
      - etransitivity; first exact: U1.
        etransitivity; first exact: U2.
        exact: U3.

      (* TODO: This is the same as the case [Lcond true lbl]. *)
      apply: (lsem_trans5 _ E1 E2).
      - (* align; label *)
        rewrite setpc_lset_estate.
        apply: lsem_align_label_id => //.
        rewrite lfn_lset_estate hfn.
        rewrite -!catA cat_cons -!catA in C.
        exact: C.
      - rewrite -cat1s !catA -catA in C.
        apply: (eval_lsem_step1 C) => //.
        + by rewrite !size_cat /= addnA.
        rewrite /eval_instr /= (eval_jumpE C) -!catA.
        rewrite find_label_cat_hd; last by apply: D; lia.
        rewrite find_label_cat_hd; last by case: (a).
        rewrite find_labelE /= /is_label /= eqxx /=.
        rewrite addn0 setpc_lset_estate !setcpc_setpc.
        reflexivity.
      rewrite add_align_nil catA size_cat in E3.
      rewrite -!catA -hfn in C.
      have /(_ _ hpc erefl erefl) {}E3 := lsem_skip_align _ _ C _ E3.
      rewrite !catA -cat1s -!catA catA in C.
      have /(_ _ erefl erefl erefl) := lsem_skip_label _ _ C _ E3.
      by rewrite !size_cat /= !size_cat /= !addnA -hfn.
    }
    (* arbitrary expression *)
    move => {} e ok_e Ew Hw.
    t_xrbindP => /dup[] checked_e /check_fexprP[] f ok_f ok_c ok_c'.
    move: Hw; rewrite checked_e /to_fexpr ok_f => Hw.
    case: c' Ec' Hc' ok_c' Ew Hw => [ | i c' ].
    { (* second body is empty *)
      move => /semE[] ??; subst k' s2 => _ _ Ew.
      rewrite linear_c_nil.
      move: {Hc} (Hc fn (next_lbl lbl)).
      rewrite /checked_c ok_fd ok_c => /(_ erefl).
      case: (linear_c fn c (next_lbl lbl) [::]) (valid_c fn c (next_lbl lbl)) => lblc lc.
      rewrite /next_lbl => - [L V] Hc /= /(_ erefl) Hw.
      rewrite add_align_nil.
      move=> ls m vm P Q M X D C hpc hfn sp hsp S MAX.
      set lcalign := add_align _ _ _.
      set lilabel := {| li_i := Llabel _ _; |}.
      set licond := {| li_i := Lcond _ _; |}.
      set P' := P ++ lcalign ++ [:: lilabel ].
      set Q' := [:: licond ] ++ Q.

      have {Hc} := Hc (setpc ls (size P')) m vm P' Q' M X _ _ _ _ sp hsp S MAX.
      case=> //.
      - apply: disjoint_labels_cat; last apply: disjoint_labels_cat.
        + apply: disjoint_labels_wL D; rewrite /next_lbl; lia.
        + subst lcalign. by case: (a).
        rewrite /next_lbl => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
      - by move: C; rewrite -!catA /= -!catA.
      move => m1 vm1 E1 K1 X1 H1 M1 U1.
      have [ b /(match_mem_gen_sem_pexpr M1) {} ok_e /value_uinclE ? ] := sem_pexpr_uincl X1 ok_e; subst b.
      have hsp1: s3.[vrsp] = Vword sp.
      + rewrite -(sem_preserved_RSP_GD var_tmps_not_magic Ec) //.
        by apply RSP_in_magic.
      have S1: source_mem_split s3 sp.
      + by move=> pr; rewrite -(sem_validw_stable Ec); apply S.
      have {Hw} := Hw ls m1 vm1 P Q M1 X1 D _ hpc hfn sp hsp1 S1 MAX.
      case.
      - by rewrite add_align_nil.
      move => m3 vm3 E3 K3 X3 H3 M3 U3.
      exists m3 vm3 => //; cycle 1.
      - transitivity vm1; last (apply: eq_exI K3; SvD.fsetdec).
        apply: eq_exI K1; SvD.fsetdec.
      - etransitivity; first exact: H1.
        apply: preserved_metadataE; last exact: H3.
        + exact: sem_stack_stable Ec.
        exact: sem_validw_stable Ec.
      - etransitivity; first exact: U1.
        exact: U3.
      apply: (lsem_trans4 _ E1).
      - (* align; label *)
        rewrite setpc_lset_estate.
        apply: lsem_align_label_id => //.
        rewrite lfn_lset_estate hfn.
        rewrite -!catA cat_cons -!catA in C.
        exact: C.
      - rewrite -cat1s !catA -catA in C.
        apply: (eval_lsem_step1 C) => //.
        + by rewrite !size_cat /= addnA.
        have {} ok_e := fexpr_of_pexprP ok_f ok_e.
        rewrite /eval_instr /= ok_e hfn (eval_jumpE C) -!catA /=.
        rewrite find_label_cat_hd; last by apply: D; lia.
        rewrite find_label_cat_hd; last by case: (a).
        rewrite find_labelE /= /is_label /= eqxx /= addn0 /setcpc /=.
        reflexivity.
      rewrite add_align_nil catA size_cat in E3.
      rewrite -!catA -hfn in C.
      have /(_ _ hpc erefl erefl) {}E3 := lsem_skip_align _ _ C _ E3.
      rewrite !catA -cat1s -!catA catA in C.
      have /(_ _ erefl erefl erefl) := lsem_skip_label _ _ C _ E3.
      by rewrite !size_cat /= !size_cat /= !addnA -hfn.
    }
    (* General case *)
    clear Pi Pi_r => Ec' Hc' ok_c' Ew.
    rewrite linear_c_nil.
    move: {Hc} (Hc fn (next_lbl (next_lbl lbl))).
    rewrite /checked_c ok_fd ok_c => /(_ erefl).
    case: (linear_c fn c (next_lbl (next_lbl lbl)) [::]) (valid_c fn c (next_lbl (next_lbl lbl))) => lblc lc.
    rewrite /next_lbl => - [L V] Hc.
    rewrite linear_c_nil.
    move: {Hc'} (Hc' fn lblc).
    rewrite /checked_c ok_fd ok_c' => /(_ erefl).
    case: (linear_c fn (i :: c') lblc [::]) (valid_c fn (i :: c') lblc) => lblc' lc' [L' V'] Hc' /= /(_ erefl) Hw.
    rewrite add_align_nil.
    move => ls m vm P Q M X D C hpc hfn sp hsp S MAX.

    set ligoto := {| li_i := Lgoto _; |}.
    set lcalign := add_align _ _ _.
    set lilabel := {| li_i := Llabel _ lbl; |}.
    set lilabel' := {| li_i := Llabel _ (lbl + 1); |}.
    set licond := {| li_i := Lcond _ _; |}.
    set P' := P ++ ligoto :: lcalign ++ [:: lilabel' ] ++ lc' ++ [:: lilabel ].
    set Q' := [:: licond ] ++ Q.
    have {Hc} := Hc (setpc ls (size P')) m vm P' Q' M X _ _ _ _ sp hsp S MAX.
    case=> //.
    - apply: disjoint_labels_cat; last apply: disjoint_labels_cat.
      + apply: disjoint_labels_w D; lia.
      + subst lcalign. by case: (a).
      apply: disjoint_labels_cat; last apply: disjoint_labels_cat.
      + move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
      + apply: (valid_disjoint_labels V'); left; lia.
      move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
    - move: C. by rewrite /= /P' /Q' -!catA -!cat_cons -!catA.
    move => m1 vm1 E1 K1 X1 H1 M1 U1.

    subst P' Q'.
    set P' := P ++ ligoto :: lcalign ++ [:: lilabel' ].
    set Q' := lilabel :: lc ++ licond :: Q.
    have [ b /(match_mem_gen_sem_pexpr M1) {} ok_e /value_uinclE ? ] := sem_pexpr_uincl X1 ok_e; subst b.
    have hsp1: s2.[vrsp] = Vword sp.
    + rewrite -(sem_preserved_RSP_GD var_tmps_not_magic Ec) //.
      by apply RSP_in_magic.
    have S1: source_mem_split s2 sp.
    + by move=> pr; rewrite -(sem_validw_stable Ec); apply S.
    have {Hc'} := Hc' (setpc ls (size P')) m1 vm1 P' Q' M1 X1 _ _ _ _ sp hsp1 S1 MAX.
    case=> //.
    - apply: disjoint_labels_cat; last apply: disjoint_labels_cat.
      + apply: disjoint_labels_wL D; lia.
      + subst lcalign. by case: (a).
      move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
    - move: C. by rewrite -!catA -!cat_cons -!catA.
    move => m2 vm2 E2 K2 X2 H2 M2 U2.
    have hsp2: s3.[vrsp] = Vword sp.
    + rewrite -(sem_preserved_RSP_GD var_tmps_not_magic Ec') //.
      by apply RSP_in_magic.
    have S2: source_mem_split s3 sp.
    + by move=> pr; rewrite -(sem_validw_stable Ec'); apply S1.
    have {Hw} := Hw ls m2 vm2 P Q M2 X2 D _ hpc hfn sp hsp2 S2 MAX.
    case=> //.
    - by rewrite add_align_nil.
    move => m3 vm3 E3 K3 X3 H3 M3 U3.
    exists m3 vm3 => //; cycle 1.
    - transitivity vm2; last (apply: eq_exI K3; SvD.fsetdec).
      transitivity vm1; last (apply: eq_exI K2; SvD.fsetdec).
      apply: eq_exI K1; SvD.fsetdec.
    - etransitivity; first exact: H1.
      apply: preserved_metadataE; last (etransitivity; first exact: H2); last first.
      + apply: preserved_metadataE; last exact: H3.
        * exact: sem_stack_stable Ec'.
        exact: sem_validw_stable Ec'.
      + exact: sem_validw_stable Ec.
      exact: sem_stack_stable Ec.
    - etransitivity; first exact: U1.
      etransitivity; first exact: U2.
      exact: U3.
    apply: (lsem_trans4 _ E1).
    - apply: (eval_lsem_step1 C) => //.
      rewrite /eval_instr /= (eval_jumpE C).
      rewrite find_label_cat_hd; last by apply: D; lia.
      rewrite -!catA find_labelE /= find_label_cat_hd; last by case: (a).
      rewrite find_labelE /is_label /= eq_sym next_lbl_neq -!catA find_label_cat_hd; last first.
      + apply: (valid_has_not_label V'); left; lia.
      rewrite find_labelE /= /is_label /= eqxx /= -hfn.
      by repeat rewrite size_cat /= !addnS.
     apply: (lsem_trans3 _ E2).
    - rewrite -!cat_cons !catA -(cat1s _ lc') -(cat1s _ lc) !catA -catA in C.
      apply: (eval_lsem_step1 C) => //.
      + rewrite !size_cat /= !size_cat /= !size_cat /=.
        by rewrite !addn1 !addnS !addSn addnA.
      have {} ok_e := fexpr_of_pexprP ok_f ok_e.
      rewrite /eval_instr /= ok_e hfn (eval_jumpE C) -!catA.
      rewrite find_label_cat_hd; last by apply: D; lia.
      rewrite find_labelE /= find_label_cat_hd; last by case: (a).
      rewrite find_labelE /= /is_label /= eqxx /= /setcpc -hfn.
      by repeat rewrite size_cat /= !addnS.
    - rewrite
        -!cat_cons -(cat1s _ lc) -(cat1s _ lc') !catA -catA -catA -catA in C.
      apply: (eval_lsem_step1 C) => //.
      by rewrite !size_cat /= !size_cat /= !addn1 addnS.

    subst P' Q'.
    set Q' :=
      ligoto :: (lcalign ++ lilabel' :: lc') ++ lilabel :: (lc ++ licond :: Q).
    have {}C : is_linear_of fn (P ++ Q').
    - move: C.
      by rewrite /Q' -!cat_cons -!catA -(cat1s _ lc) -(cat1s _ Q) -!catA.
    rewrite size_cat add_align_nil in E3.
    have /(_ _ hpc hfn erefl) := lsem_skip_goto _ _ C _ _ _ E3.
    rewrite -/(size _); repeat rewrite size_cat /=.
    rewrite !addnA !addnS !addn0 addSn.
    apply=> //.
    - apply: D; lia.
    have h : (lbl < lblc)%positive by lia.
    have := @valid_has_not_label _ _ _ _ lbl V' (or_introl h).
    rewrite has_cat /is_label /= eq_sym next_lbl_neq negb_or => ->.
    subst lcalign.
    by case: (a).
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p var_tmps Pc Pi_r.
  Proof.
    move => ii k s1 s2 a c e c' Ec Hc; rewrite p_globs_nil => ok_e fn lbl /checked_iE[] fd ok_fd /=.
    case: is_boolP ok_e; first case; first by [].
    { (* expression is the “false” literal *)
      move => _ ok_c /=.
      move: {Hc} (Hc fn lbl).
      rewrite /checked_c ok_fd ok_c => /(_ erefl).
      case: (linear_c fn c lbl [::]) => lblc lc.
      move => Hc.
      move => ls m vm P Q M X D C hpc hfn sp hsp S MAX.
      have {Hc} [m' vm' E K X' H' M' U'] := Hc ls m vm P Q M X D C hpc hfn sp hsp S MAX.
      by exists m' vm'.
    }
    (* arbitrary expression *)
    t_xrbindP => {} e ok_e /check_fexprP[] f ok_f ok_c ok_c'.
    rewrite /to_fexpr ok_f.
    case: c' ok_c' => [ | i c' ] ok_c'.
    { (* second body is empty *)
      rewrite linear_c_nil.
      move: {Hc} (Hc fn (next_lbl lbl)).
      rewrite /checked_c ok_fd ok_c => /(_ erefl).
      case: (linear_c fn c (next_lbl lbl) [::]) => lblc lc.
      move => Hc.
      rewrite /= add_align_nil.
      move=> ls m vm P Q M X D.
      rewrite -cat1s !catA.
      set prefix := (X in X ++ lc).
      do 2 rewrite -catA.
      set suffix := (X in lc ++ X).
      move=> C hpc hfn sp hsp S MAX.
      have {Hc} [|m' vm' E  K X' H' M'] :=
        Hc (setpc ls (size prefix)) m vm prefix suffix M X _ C erefl hfn sp hsp S MAX.
      - apply: disjoint_labels_cat; first apply: disjoint_labels_cat.
        + apply: disjoint_labels_wL _ D; rewrite /next_lbl; lia.
        + by case: (a).
        clear.
        rewrite /next_lbl => lbl' range.
        rewrite /is_label /= orbF; apply/eqP; lia.
      have [ ] := sem_pexpr_uincl X' ok_e.
      case => // - [] // /(match_mem_gen_sem_pexpr M') {} ok_e _.
      exists m' vm' => //.
      apply: (lsem_trans3 _ E).
      - apply:
          (lsem_trans (s2 := {| lpc := size (P ++ add_align ii a [::]); |})).
        + subst prefix; case: a C {E} => C; last first.
          * rewrite cats0 -hpc. exact: rt_refl.
          rewrite -!catA in C.
          apply: (eval_lsem_step1 C) => //.
          by rewrite /eval_instr /= size_cat addn1 -hpc.
        rewrite -catA in C.
        apply: (eval_lsem_step1 C) => //.
        by rewrite /eval_instr /= /prefix !size_cat /= addn1.
      rewrite catA in C.
      apply: (eval_lsem_step1 C) => //.
      have {} ok_e := fexpr_of_pexprP ok_f ok_e.
      by rewrite /eval_instr /= ok_e /= /prefix !size_cat !addn1 -hpc.
    }
    (* general case *)
    rewrite linear_c_nil.
    move: {Hc} (Hc fn (next_lbl (next_lbl lbl))).
    rewrite /checked_c ok_fd ok_c => /(_ erefl).
    case: (linear_c fn c (next_lbl (next_lbl lbl)) [::]) (valid_c fn c (next_lbl (next_lbl lbl))) => lblc lc.
    rewrite /next_lbl => -[L V] Hc.
    rewrite linear_c_nil.
    case: (linear_c fn (i :: c') lblc [::]) (valid_c fn (i :: c') lblc) => lblc' lc' [L' V'].
    rewrite /= add_align_nil.
    move=> ls m vm P Q M X D.
    rewrite -cat1s -(cat1s _ (lc' ++ _)) -(cat1s _ (lc ++ _)) !catA.
    set prefix := (X in X ++ lc).
    do 2 rewrite -catA.
    set suffix := (X in lc ++ X).
    move=> C hpc hfn sp hsp S MAX.
    have {Hc} [|m' vm' E  K X' H' M' U'] :=
      Hc (setpc ls (size prefix)) m vm prefix suffix M X _ C erefl hfn sp hsp S MAX.
    - subst prefix; move: L' V' D; clear.
      rewrite /next_lbl => L' V' D.
      repeat apply: disjoint_labels_cat; try by [].
      + apply: disjoint_labels_w _ D; lia.
      + by case: (a).
      + move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
      + apply: (valid_disjoint_labels V'); left; lia.
      move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
    have [ ] := sem_pexpr_uincl X' ok_e.
    case => // - [] // /(match_mem_gen_sem_pexpr M') {} ok_e _.
    exists m' vm' => //.
    apply: (lsem_trans3 _ E).
    - (* goto *)
      rewrite -!catA in C.
      apply: (eval_lsem_step1 C) => //.
      rewrite /eval_instr /= (eval_jumpE C) /=.
      rewrite find_label_cat_hd; last by apply: D; lia.
      rewrite find_labelE /= find_label_cat_hd; last by case: (a).
      rewrite find_labelE /is_label /= eq_sym next_lbl_neq.
      rewrite find_label_cat_hd; last by apply: (valid_has_not_label V'); lia.
      rewrite find_labelE /is_label /= eqxx /=.
      by rewrite !size_cat /= !addnS !addn0 !addnA !addSn -hfn.
    (* cond false *)
    rewrite catA in C.
    apply: (eval_lsem_step1 C) => //.
    have {} ok_e := fexpr_of_pexprP ok_f ok_e.
    rewrite /eval_instr /= ok_e /=.
    by rewrite !size_cat /= !size_cat /= !addnS !addnA !addn0 !addSn.
  Qed.

  Lemma find_entry_label fn fd :
    sf_return_address (f_extra fd) ≠ RAnone →
    find_label xH (lfd_body (linear_fd fn fd).2) = ok 0.
  Proof. by rewrite /linear_fd /linear_body; case: sf_return_address. Qed.

  Lemma is_label_lstore lbl x ofs y :
    is_label lbl (lstore liparams x ofs y) = false.
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
    by lia.
  Qed.

  Lemma frame_size_bound e :
    (0 <= sf_stk_sz e)%Z ->
    (0 <= sf_stk_extra_sz e)%Z ->
    (sf_stk_sz e + sf_stk_extra_sz e <= frame_size e)%Z.
  Proof.
    move=> hsz hextra.
    rewrite /frame_size.
    have := stack_frame_allocation_size_bound hsz hextra.
    by case: is_RAnone; lia.
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

  Context (sp0_le : (wunsigned sp0 <= wunsigned (top_stack m0))%Z).

  Local Lemma Hcall : sem_Ind_call p var_tmps Pi_r Pfun.
  Proof.
    move=> ii k s1 s2 res fn' args xargs xres
      ok_xargs ok_xres exec_call ih fn lbl /checked_iE[] fd ok_fd chk_call.
    case linear_eq: linear_i => [lbli li].
    move=> ls m1 vm2 P Q M X D C hpc hfn sp hsp S MAX.
    move: chk_call => /=.
    t_xrbindP => /negbTE fn'_neq_fn.
    case ok_fd': (get_fundef _ fn') => [ fd' | ] //; t_xrbindP => ok_ra ok_align /ZleP ok_max _.
    have := get_fundef_p' ok_fd'.
    set lfd' := linear_fd _ fd'.
    move => ok_lfd'.
    move: linear_eq; rewrite /= ok_fd' fn'_neq_fn.
    move: (checked_prog ok_fd') => /=; rewrite /check_fd /frame_size.
    t_xrbindP=> chk_body ok_to_save ok_stk_sz ok_ret_addr ok_save_stack _ A.
    have ok_body' : is_linear_of fn' (lfd_body lfd'.2).
    - by rewrite /is_linear_of; eauto.
    have {}ih := ih _ _ _ _ _ _ _ _ _ _ ok_body'.
    have lbl_valid : (fn, lbl) \in (label_in_lprog p').
    - clear -A C ok_ra hliparams.
      apply: (label_in_lfundef _ C).
      move: A; rewrite (negbTE ok_ra).
      move=> [_ <-].
      rewrite /label_in_lcmd /=.
      by rewrite !pmap_cat !mem_cat inE eqxx !orbT.

    have h := encode_label_dom small_dom_p' lbl_valid.
    case ok_ptr: encode_label h => [ ptr | // ] _.
    case/sem_callE: (exec_call) => ? m s' k'; rewrite ok_fd' => /Some_inj <- ra_sem ok_ss sp_aligned T ok_m exec_cbody T' s2_eq hk.
    move: ok_stk_sz sp_aligned A {ok_save_stack};
      rewrite /top_stack_aligned (negbTE ok_ra) /= => ok_stk_sz sp_aligned [??]; subst lbli li.
    have s1_rsp : (evm s1).[vrsp] = Vword (top_stack (emem s1)).
    + by move: T; rewrite /valid_RSP /kill_tmp_call /= kill_varsE; case: ifP.
    move: (s1_rsp); rewrite hsp => -[?]; subst sp.
    set rastack_before := is_RAstack_None _.
    set rastack_after  := is_RAstack _.
    set sz := stack_frame_allocation_size _.
    set sz_before := if rastack_before then (sz - wsize_size Uptr)%Z else sz.
    set sz_after := if rastack_after then (sz - wsize_size Uptr)%Z else sz.
    set before :=  allocate_stack_frame _ _ _ _ _ _ rastack_before.
    set after :=  allocate_stack_frame _ _ _ _ _ _ rastack_after.
    move: C; set P' := P ++ _ => C.
    pose Stmp := if tmpi_of_ra (sf_return_address (f_extra fd')) is Some x then Sv.singleton x else Sv.empty.
    have StmpE : Sv.Equal Stmp (tmp_call (f_extra fd')).
    + by rewrite /tmp_call /Stmp /tmpi_of_ra; case: sf_return_address => //= [_ | _ _] [].
    move: (X vrsp); rewrite s1_rsp.
    move=> /get_word_uincl_eq -/(_ (subtype_refl _)) vm2_rsp.
    have vrsp_ne_aux :
      match tmpi_of_ra (sf_return_address (f_extra fd')) with
      | Some x => v_var (vid (sp_rsp (p_extra p))) ≠ v_var x
      | None => True
      end.
    + move: T; rewrite /valid_RSP /kill_tmp_call /= kill_varsE.
      case: Sv_memP => // + _.
      rewrite /tmpi_of_ra /fd_tmp_call /tmp_of_ra /tmp_call ok_fd'.
      by case: sf_return_address => // [_ | _ _] [?|] //=; SvD.fsetdec.
    have [vm2_b [hsem_before heqvm2 hvm2_b_rsp]] :
      exists (vm2_b:Vm.t),
        [/\ lsem p' (Lstate (escs s1) m1 vm2 fn (size P))
              (Lstate (escs s1) m1 vm2_b fn (size P + size before)),
             vm2 =[\ Sv.add vrsp Stmp] vm2_b  &
             vm2_b.[vrsp] = Vword (top_stack (emem s1) -  wrepr Uptr sz_before)].
    + move: C ; rewrite /P' /before /sz_before /rastack_before /allocate_stack_frame /sz.
      case: eqP => [-> | _] C /=.
      + by rewrite addn0 wrepr0 GRing.subr0; exists vm2; split => //; apply rt_refl.
      rewrite -catA in C.
      have := spec_lip_allocate_stack_frame_1 hliparams C.
      move=> /(_ (with_mem (with_vm s1 vm2) m1) (top_stack (emem s1))); apply.
      + case: sf_return_address ok_ret_addr vrsp_ne_aux => //=.
        + by move=> v [x|] //= /andP [] _ /eqP.
        by move=> o z [x|] //= /andP [] /eqP.
      by rewrite /get_var /with_vm /= vm2_rsp.

    set ra := sf_return_address (f_extra fd').
    set o := Some ((fn, lbl), P', (size P + size before).+1).
    set s := (top_stack (emem s1) - wrepr Uptr sz)%R.

    have [m' [vm' [hmatch hvm'_rsp heq_vm' hvalue_of hpres_m1_m' U h2]]] : exists m' vm',
      let: li := MkLI ii (Lcall (ovari_of_ra ra) (fn', 1%positive)) in
      let: ls :=
        {|
          lscs := escs s1;
          lmem := m1;
          lvm := vm2_b;
          lfn := fn;
          lpc := size P + size before;
        |}
      in
      let: ls' :=
        {|
          lscs := escs s1;
          lmem := m';
          lvm := vm';
          lfn := fn';
          lpc := 1;
        |}
      in
      [/\ match_mem_gen (top_stack m0) (kill_tmp_call p fn' s1) m'
        , vm'.[vrsp] = Vword s
        , vm2_b =[\ Sv.add vrsp (killed_on_entry ra) ] vm'
        , value_of_ra m' vm' ra o
        , preserved_metadata (kill_tmp_call p fn' s1) m1 m'
        , target_mem_unchanged m1 m'
        & eval_instr p' li ls = ok ls'
      ].
    + rewrite /eval_instr /= /ra /get_label_after_pc /setpc /=.
      set ls1 := {| lscs := escs s1 |}.
      have -> /= : find_instr p' (lnext_pc ls1) = Some {| li_ii := ii; li_i := linear.Llabel ExternalLabel lbl |}.
      + rewrite /lnext_pc; assert (h := find_instr_skip C).
        have h1 := h ls1 (size before + 1) erefl.
        by rewrite -addn1 -addnA -/before h1 -catA oseq.onth_cat ltnNge addn1 leqnSn /= subSnn.
      rewrite /rencode_label ok_ptr /= (eval_jumpP ok_lfd' (find_entry_label _ _)); last by apply/eqP.
      have hfind : find_label lbl P' = ok (size P + size before).+1.
      + rewrite /P' find_label_cat_hd; last by apply: D; rewrite /next_lbl; lia.
        rewrite -catA find_label_cat_hd; last by apply has_label_allocate_stack_frame.
        by rewrite /find_label /= /is_label /= eqxx /= addn1 addnS.

      rewrite /ra_valid in ra_sem. rewrite /sz_before /rastack_before in hvm2_b_rsp.
      rewrite /Stmp in heqvm2.
      case eq_ra : sf_return_address ok_ra ok_ret_addr ra_sem hvm2_b_rsp heqvm2 => [ | x | [ x | ] ofs] //= _
        ok_ret_addr ra_sem hvm2_b_rsp heqvm2.
      (* RAreg x _ *)
      + exists m1,  vm2_b.[x <- Vword ptr]; split => //.
        + by rewrite Vm.setP_neq ?hvm2_b_rsp //; case/and3P : ra_sem.
        + by move=> /= y hy; rewrite Vm.setP_neq //; apply/eqP; move: hy; clear; SvD.fsetdec.
        + case: (x) ok_ret_addr => /= ? vra /andP []/eqP -> _; rewrite eq_refl; split => //.
          by rewrite ok_ptr; exists ptr => //; rewrite Vm.setP_eq vm_truncate_val_eq // zero_extend_u.
        by rewrite /= set_var_truncate //=; case/andP: ok_ret_addr => /eqP->.
      (* RAstack (Some x) ofs _ *)
      + case/and5P: ok_ret_addr => _ /eqP ok_ret_addr _ _ _.
        exists m1, vm2_b.[x <- Vword ptr]; split => //.
        + by rewrite Vm.setP_neq ?hvm2_b_rsp //; case/andP : ra_sem.
        + by move=> /= y hy; rewrite Vm.setP_neq //; apply/eqP; move: hy; clear; SvD.fsetdec.
        + case: (x) ok_ret_addr => /= ? vra ->; rewrite eq_refl; split => //.
          by rewrite ok_ptr; exists ptr => //; rewrite Vm.setP_eq zero_extend_u vm_truncate_val_eq.
        by rewrite /= set_var_truncate //= ok_ret_addr.
      (* RAstack None ofs _ *)
      move: ok_ret_addr => /and4P [] _ /eqP ? /eqP hioff sf_align_for_ptr; subst ofs.
      have [m' ok_m' M']:
         exists2 m1', write m1 Aligned (top_stack_after_alloc (top_stack (emem (kill_tmp_call p fn' s1))) (sf_align (f_extra fd'))
                   (sf_stk_sz (f_extra fd') + sf_stk_extra_sz (f_extra fd')))%R ptr = ok m1' &
                         match_mem_gen (top_stack m0) (kill_tmp_call p fn' s1) m1'.
      + apply: mm_write_invalid.
        * by have /= := MAX _ ok_fd; lia.
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
          by lia.
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

    set ls1 := setcpc (lset_estate ls (escs s1) m' vm') fn' 1.
    have huincl : (kill_vars (killed_on_entry ra) (kill_tmp_call p fn' s1)).[vrsp <- Vword s] <=1  vm'.
    + move=> x; rewrite Vm.setP; case: eqP => [<- | hne].
      + by rewrite hvm'_rsp /= cmp_le_refl.
      rewrite /kill_tmp_call !kill_varsE; case: Sv_memP.
      + by move=> _; apply/compat_value_uincl_undef/Vm.getP.
      move=> hnin1; case: Sv_memP.
      + by move=> _; apply/compat_value_uincl_undef/Vm.getP.
      rewrite /fd_tmp_call ok_fd' => hnin2.
      apply: (value_uincl_trans (X x)); rewrite heqvm2; last by SvD.fsetdec.
      by rewrite heq_vm' //; SvD.fsetdec.
    have his_ra: is_ra_of fn' ra by exists fd'.
    case: (ih ls1 _ _ _ _ _ [::] hmatch huincl erefl his_ra hvalue_of) => //.
    + by exists fd' => //=; rewrite (negbTE ok_ra).
    + by exists fd' => //=; rewrite (negbTE ok_ra).
    + move=> fd''; rewrite ok_fd' => -[?]; subst fd''.
      rewrite (negbTE ok_ra).
      by move: (MAX _ ok_fd) => /=; lia.
    + by rewrite ok_fd' => _ [<-]; rewrite (negbTE ok_ra).
    move=> m2' vm2' /= h3 heq_vm hsub_vm' hpres hmatch' U'.
    set ts := top_stack (M := Memory.M) s1.
    have vm2'_rsp:
       vm2'.[vrsp] = Vword (s + wrepr Uptr (if rastack_after then wsize_size Uptr else 0%Z)).
    + move: (hsub_vm' vrsp); rewrite /kill_vars /=.
      rewrite Vm.setP_eq /= cmp_le_refl => /get_word_uincl_eq -/(_ (subtype_refl _)).
      rewrite /rastack_after /ra.
      by case sf_return_address => //= *; rewrite wrepr0 GRing.addr0.
    have [vm2'_b [hsem_after heqvm2' hvm2'_b_rsp]] :
      exists (vm2'_b:Vm.t),
        [/\ lsem p' (Lstate (escs s2) m2' vm2' fn (size P + size before).+2)
              (Lstate (escs s2) m2' vm2'_b fn ((size P + size before).+2 + size after)),
             vm2' =[\ Sv.add vrsp Stmp] vm2'_b  &
             vm2'_b.[vrsp] = Vword ts].
    + move: C vm2'_rsp; rewrite /P' /after /rastack_after {-1}/allocate_stack_frame /sz.
      case: eqP => H0 C vm2'_rsp /=.
      + rewrite addn0; exists vm2'; split => //; first by apply rt_refl.
        rewrite vm2'_rsp /s /ts /sz.
        move: H0; case: ifP => _ H.
        + have -> : stack_frame_allocation_size (f_extra fd') = wsize_size Uptr by lia.
          by f_equal; ssrring.ssring.
        by rewrite H wrepr0; f_equal; ssrring.ssring.
      set after' := map (li_of_fopn_args ii) _.
      move: C; rewrite -/before cats0 -/after'.
      have -> :
       (P ++ (before ++
         [:: {| li_ii := ii; li_i := Lcall (ovari_of_ra (sf_return_address (f_extra fd'))) (fn', 1%positive) |},
             {| li_ii := ii; li_i := linear.Llabel ExternalLabel lbl |}
          & after']) ++ Q) =
       ((P ++
       before) ++
         [:: {| li_ii := ii; li_i := Lcall (ovari_of_ra (sf_return_address (f_extra fd'))) (fn', 1%positive) |};
          {| li_ii := ii; li_i := linear.Llabel ExternalLabel lbl |}]) ++ after' ++ Q  by rewrite -!catA.
      move => C; have := spec_lip_free_stack_frame_1 hliparams C.
      move=> /(_ (with_mem (with_vm s2 vm2') m2')).
      move=> /(_  (s + wrepr Uptr (if is_RAstack (sf_return_address (f_extra fd')) then wsize_size Uptr else 0%Z))%R) [].
      + case: sf_return_address ok_ret_addr vrsp_ne_aux => //=.
        + by move=> v [x|] //= /andP [] _ /eqP.
        by move=> ? z [x|] //= /andP [] /eqP.
      + by rewrite /get_var /with_vm /= vm2'_rsp.
      rewrite /= !size_cat /= !addnS addn0 -/after' => vm2'_b [H1 H2 H3]; exists vm2'_b; split => //.
      rewrite H3 /ts /s /sz; f_equal; case: ifP => _; rewrite ?wrepr_sub ?wrepr0; ssrring.ssring.

    apply (Ex2_6 (x1:=m2')(x2:=vm2'_b)).
    + rewrite -hpc -hfn in hsem_before.
      apply/(lsem_trans hsem_before).
      rewrite hpc hfn; apply/lsem_step.
      + rewrite /lsem1 /step.
        set ls1' := {| lscs := escs s1 |}; assert (h := find_instr_skip C).
        by rewrite (h ls1' (size before) erefl) -/before -catA oseq.onth_cat ltnn subnn /= h2.
      apply/(lsem_trans h3).
      rewrite !size_cat /= cats0 addnA -addn2.
      by move: hsem_after; rewrite /setcpc !addSn !addnS addn0 /setpc /= hfn.
    + move => x; rewrite /fd_tmp_call ok_fd' -StmpE => x_notin_k.
      case: (vrsp =P x) => x_neq_rsp.
      + by subst x; rewrite vm2_rsp hvm2'_b_rsp.
      rewrite -heqvm2'; last by move: x_notin_k x_neq_rsp; clear; SvD.fsetdec.
      rewrite -heq_vm; last first.
      + move: x_notin_k x_neq_rsp; rewrite hk /ra_vm /ra /=; clear.
        by case: sf_return_address => [ | r | [ r | ] ?] /=; SvD.fsetdec.
      rewrite heqvm2; last by SvD.fsetdec.
      apply heq_vm'.
      move: x_notin_k x_neq_rsp; rewrite hk /ra_vm /ra /=; clear.
      by case: sf_return_address => [ | r | [ r | ] ?] /=; SvD.fsetdec.
    + have := sem_one_varmap_facts.sem_call_valid_RSP exec_call.
      rewrite /= /valid_RSP /set_RSP => h x /=.
      rewrite kill_varsE; case: Sv_memP => [_ | ].
      + by apply/compat_value_uincl_undef/Vm.getP.
      rewrite /fd_tmp_call ok_fd' -StmpE => hnin.
      have := hsub_vm' x.
      rewrite Vm.setP; case: eqP => [? | ]; first by subst x; rewrite h hvm2'_b_rsp.
      rewrite kill_varsE; case: Sv_memP => //.
      + move: his_ra ok_ra; rewrite /is_ra_of ok_fd' /sv_of_list.
        move=> [_ [<-] <-].
        by case: sf_return_address => //=; clear => *; SvD.fsetdec.
      move=> _ hne H; apply (value_uincl_trans H).
      by rewrite heqvm2' //; move: hnin hne; clear; SvD.fsetdec.
    + by etransitivity; eauto.
    + exact hmatch'.
    by etransitivity; [exact: U | exact: U'].
  Qed.

  Lemma push_to_save_has_no_label lbl m sp:
    ~~ has (is_label lbl) (push_to_save liparams p m sp).
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
          x = {| vtype := sword ws; vname := xname; |}
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
           Let: ws := if vtype x is sword ws then ok ws else Error ErrType in
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
                Let: ws := if vtype x is sword ws then ok ws else Error ErrType in
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
      vtype x = sword ws ->
      (lo <= ofs /\ ofs + wsize_size ws <= hi)%Z.
  Proof.
    elim: to_save lo => //.
    move=> [x1 ofs1] to_save ih lo /all_disjoint_aligned_betweenP.
    move=> [] ofs1' [] ws1' [] [] /=.
    case heq: is_word_type => [ws1 | ] // [??]; subst ofs1' ws1'.
    move=> _ hlo _ _ /dup[] {}/ih ih /all_disjoint_aligned_between_range ?.
    move=> x ofs ws; rewrite in_cons => /orP [/eqP [-> ->] | hin] ht.
    + by move: heq; rewrite ht => -[->].
    have := ih _ _ _ hin ht; have := (@le0_wsize_size ws1); lia.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p var_tmps Pc Pfun.
  Proof.
    red => ii k s1 _ fn fd m1' s2' ok_fd free_ra ok_ss rsp_aligned valid_rsp
      ok_m1' exec_body ih valid_rsp' -> ls m1 vm1 _ ra lret sp callee_saved M
      X [fd' ok_fd' <-] hfn.
    have A := alloc_stackP ok_m1'.
    case; rewrite ok_fd => _ /Some_inj <- ?; subst ra.
    rewrite /value_of_ra => ok_lret.
    case; rewrite ok_fd => _ /Some_inj <- /= ok_sp.
    case; rewrite ok_fd => _ /Some_inj <- /= ok_callee_saved.
    move=> wf_to_save S MAX /(_ _ erefl) ok_m0.
    move: (checked_prog ok_fd); rewrite /check_fd /=.
    t_xrbindP => chk_body ok_to_save ok_stk_sz ok_ret_addr ok_save_stack _.
    case/and4P: ok_stk_sz => /lezP stk_sz_pos /lezP stk_extra_sz_pos /ltzP frame_noof /lezP stk_frame_le_max.
    have ? : fd' = (linear_fd fn fd).2.
    - have := get_fundef_p' ok_fd.
      by rewrite ok_fd' => /Some_inj.
    subst fd'.
    move: ok_fd'; rewrite /linear_fd /linear_body /=.
    rewrite /ra_valid in free_ra.
    rewrite /check_to_save in ok_to_save.
    rewrite /ra_undef_vm in exec_body.
    rewrite /ra_undef_vm in ih.
    rewrite /saved_stack_valid in ok_ss.
    rewrite /ra_vm.
    rewrite /saved_stack_vm.
    case EQ: sf_return_address free_ra ok_to_save ok_callee_saved ok_save_stack ok_ret_addr X ok_lret exec_body ih ok_sp
      =>
      /= [ | ra | ora rastack ] free_ra ok_to_save ok_callee_saved ok_save_stack ok_ret_addr X ok_lret exec_body ih.
    2-3: case => sp_aligned.
    all: move => ?; subst sp.
    - (* Export function *)
    { case: lret ok_lret => // _.
      subst callee_saved.
      case E1: sf_save_stack ok_save_stack ok_ss ok_to_save exec_body ih =>
      [ | saved_rsp | stack_saved_rsp ] /= ok_save_stack ok_ss ok_to_save exec_body ih ok_fd'.
      + (* No need to save RSP *)
      { have {ih} := ih fn xH.
        rewrite /checked_c ok_fd chk_body => /(_ erefl).
        case: (linear_c fn) ok_fd' => lbl lbody /= ok_fd' E.
        have ok_body : is_linear_of fn (lbody ++ [::]).
        + by rewrite /is_linear_of cats0 ok_fd' /=; eexists; reflexivity.
        have hle: (wunsigned (top_stack (emem s1)) <= wunsigned (top_stack m0))%Z.
        + by have := ok_m0; rewrite EQ /= => <-; apply Z.le_refl.
        have M' := mm_alloc hle M ok_m1'.
        case/and4P: ok_save_stack => /eqP to_save_nil /eqP sf_align_1 /eqP stk_sz_0 /eqP stk_extra_sz_0.
        have top_stack_preserved : top_stack m1' = top_stack (s1: mem).
        + rewrite (alloc_stack_top_stack ok_m1') sf_align_1.
          rewrite top_stack_after_aligned_alloc.
          2: exact: is_align8.
          by rewrite stk_sz_0 stk_extra_sz_0 -addE add_0.

        have X' :
          set_RSP p m1' (kill_vars (ra_undef fd var_tmps) s1) <=1 vm1.
        + apply: vm_uincl_kill_vars_set_incl X => //.
          + by rewrite /ra_undef /ra_vm EQ /=; clear; SvD.fsetdec.
          by rewrite top_stack_preserved.
        have hrsp: (set_RSP p m1' (kill_vars (ra_undef fd var_tmps) s1)).[vrsp] = Vword (top_stack m1').
        + by rewrite Vm.setP_eq vm_truncate_val_eq.
        have S': source_mem_split m1' (top_stack m1').
        + move=> pr /=.
          rewrite A.(ass_valid).
          rewrite top_stack_preserved.
          have ->: (sf_stk_sz (f_extra fd) - sf_stk_ioff (f_extra fd) = 0)%Z.
          + have := A.(ass_ioff).
            rewrite stk_sz_0.
            by lia.
          rewrite /between (negbTE (not_zbetween_neg _ _ _ _)) // orbF.
          exact: S.
        have MAX': max_bound_sub fn (top_stack m1').
        + move=> fd''; rewrite ok_fd => -[?]; subst fd''.
          have /= := MAX _ ok_fd.
          rewrite /align_top_stack /align_top -(alloc_stack_top_stack ok_m1').
          rewrite top_stack_preserved.
          rewrite /frame_size EQ /= stk_sz_0 stk_extra_sz_0 /= -addE add_0.
          by move=> [_ [-> ?]]; lia.

        set ls0 := setpc (lset_estate ls (escs s1) m1 vm1) 0.
        have {E} [m2 vm2] :=
          E ls0 m1 vm1 [::] [::] M' X' (fun _ _ => erefl) ok_body erefl hfn _
            hrsp S' MAX'.
        rewrite /= => E K2 X2 H2 M2 U2.
        eexists m2 _; [ exact: E | | | | exact: mm_free M2 | exact: U2 ]; cycle 2.
        + move => a a_range /negbTE nv.
          have [L] := ass_above_limit A.
          rewrite stk_sz_0 => H.
          apply: H2.
          * rewrite (ass_root A); lia.
          rewrite (ass_valid A) nv /= !zify => - [].
          change (wsize_size U8) with 1%Z.
          rewrite (ass_add_ioff A).
          have := ass_ioff A.
          move: (sf_stk_sz _) (sf_stk_extra_sz _) (sf_stk_ioff _) stk_sz_0 stk_extra_sz_0 H.
          lia.
        + apply: eq_exI; last exact: K2.
          by rewrite to_save_nil Sv_diff_empty; clear; SvD.fsetdec.
        have SS : stack_stable m1' s2'.
        + exact: sem_one_varmap_facts.sem_stack_stable exec_body.
        move => x; move: (X2 x); rewrite /set_RSP !Vm.setP kill_varsE Vm.setP.
        case: eqP => ?; subst.
        + by rewrite valid_rsp' -(ss_top_stack SS) top_stack_preserved vm_truncate_val_eq.
        case: Sv.mem =>  // _.
        by apply compat_value_uincl_undef; apply Vm.getP.
      }
      + (* RSP is saved into register “saved_rsp” *)
      { have {ih} := ih fn xH.
        rewrite /checked_c ok_fd chk_body => /(_ erefl).
        move: ok_fd'.
        case: saved_rsp ok_save_stack ok_ss E1 exec_body => stty saved_stack /=.
        set ri := vid saved_stack.
        move=>
          /and3P[]
          /eqP ?
          /eqP to_save_empty
          hnot_saved_stack;
          subst stty.
        move=>
          /and3P[]
          /eqP saved_stack_not_GD
          /eqP saved_stack_not_RSP
          /Sv_memP saved_stack_not_written.
        move => E1 exec_body.
        rewrite linear_c_nil.
        case: (linear_c fn) => lbl lbody /=.
        set P := (X in X ++ lbody ++ _).
        set Q := (X in lbody ++ X).
        move => ok_fd' E.
        set ls0 := setpc (lset_estate ls (escs s1) m1 vm1) 0.
        have ok_body : is_linear_of (lfn ls0) (P ++ lbody ++ Q).
        + by rewrite hfn /is_linear_of ok_fd' /=; eauto.
        have ok_rsp : get_var true vm1 vrsp = ok (Vword (top_stack (emem s1))).
        + move: (X vrsp). rewrite Vm.setP_eq vm_truncate_val_eq // /get_var.
          by move=> /get_word_uincl_eq -/(_ (subtype_refl _)) ->.

        have  [|vm [hsem hvm hgetrsp hgetr hflags]] :=
          set_up_sp_register_ok
            hliparams
            (P := [::])
            ok_body
            erefl
            ok_rsp
            erefl erefl
            hneq_vtmp_vrsp
            saved_stack_not_RSP _.
        + by move=> [h]; move: hnot_saved_stack; rewrite h eqxx.
        have D : disjoint_labels 1 lbl P.
        + move => lbl' _.
          rewrite /P /=.
          by rewrite set_up_sp_register_has_label.

        have hrsp: (set_RSP p m1' (kill_vars (ra_undef fd var_tmps) s1)).[vrsp] = Vword (top_stack m1').
        + by rewrite Vm.setP_eq vm_truncate_val_eq.
        have S': source_mem_split m1' (top_stack m1').
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
        have MAX': max_bound_sub fn (top_stack m1').
        + move=> fd''; rewrite ok_fd => -[?]; subst fd''.
          have := MAX _ ok_fd.
          rewrite /frame_size EQ /= /align_top_stack /align_top -(alloc_stack_top_stack ok_m1').
          move=> [? [-> _]].
          rewrite wunsigned_add; first by lia.
          have /= habove := A.(ass_above_limit).
          have hrange1 := [elaborate wunsigned_range (top_stack m1')].
          have hrange2 := [elaborate wunsigned_range (top_stack (emem s1))].
          by lia.

        set ls1 := setpc (lset_estate ls (escs s1) m1 vm1) (size P).
        rewrite hfn in ok_body.
        have X' : set_RSP p m1' (kill_vars (ra_undef fd var_tmps) s1) <=1 vm.
        + apply: (vm_uincl_after_alloc_stack X EQ _ hgetrsp ok_m1').
          rewrite /= E1 /=.
          rewrite -SvP.MP.add_union_singleton.
          by apply: eq_exI hvm; rewrite /vrsp => /=; clear; SvD.fsetdec.

        have hle: (wunsigned (top_stack (emem s1)) <= wunsigned (top_stack m0))%Z.
        + by have := ok_m0; rewrite EQ /= => <-; apply Z.le_refl.
        have [m2 vm2] :=
          E ls1 m1 vm P Q (mm_alloc hle M ok_m1') X' D ok_body erefl hfn _ hrsp S' MAX'.
        rewrite /= !size_cat /= addn1.
        move=> {}E K2 X2 H2 M2 U2.

        eexists.
        - apply: (lsem_trans hsem).
          apply: lsem_step_end; first exact: E.

          (* Exectute R[rsp] := R[r]; *)
          + rewrite catA in ok_body.
            apply: (eval_lsem1 ok_body) => //=;
              first by rewrite size_cat.
            set ts := @top_stack _ mem _ _ s1.

            have hgetr2 : get_var true vm2 (vid saved_stack) = ok (Vword (top_stack (emem s1))).
            + rewrite  -(get_var_eq_ex _ saved_stack_not_written K2).
              exact: hgetr.
            rewrite (spec_lmove
                 hliparams (lp:= p')
                 (x:= (vid (sp_rsp (p_extra p)))) (y:= vid saved_stack)
                 (ls := (setpc (lset_estate ls1 (escs s2') m2 vm2) (size P + size lbody)))
                 erefl erefl hgetr2) addnS; reflexivity.

        + rewrite to_save_empty Sv_diff_empty. clear - ok_rsp K2 hvm.
          move => x.
          rewrite !Sv.union_spec !Sv.add_spec Sv.singleton_spec Vm.setP.
          move=> /Decidable.not_or[] x_not_k /Decidable.not_or[] /Decidable.not_or[] x_not_tmp x_not_flags x_not_saved_stack.
          case: eqP => x_rsp.
          * by subst; move/get_varP: ok_rsp => [<-]; rewrite vm_truncate_val_eq.
          rewrite -K2; last exact: x_not_k.
          rewrite hvm; first done.
          by move: x_rsp; rewrite /mk_var_i /=; SvD.fsetdec.
        + move => x; rewrite Vm.setP kill_varsE; case: eqP => ?.
          * by subst; rewrite Vm.setP_eq.
          rewrite Vm.setP_neq; last by apply /eqP.
          rewrite /set_RSP Vm.setP_neq; last by apply/eqP.
          case: Sv.mem => //.
          by apply compat_value_uincl_undef; apply Vm.getP.
        + move => a [] a_lo a_hi /negbTE nv.
          have /= [L H] := ass_above_limit A.
          apply: H2.
          * by rewrite (ass_root A); lia.
          rewrite (ass_valid A) nv /= !zify => - [].
          rewrite (ass_add_ioff A).
          change (wsize_size U8) with 1%Z.
          have := ass_ioff A.
          move: (sf_stk_sz _) (sf_stk_extra_sz _) (sf_stk_ioff _) H => ???.
          lia.
        + exact: mm_free.
        exact: U2.
      }
      (* RSP is saved in stack at offset “stack_saved_rsp” *)
      { have {ih} := ih fn xH.
        rewrite /checked_c ok_fd chk_body => /(_ erefl).
        move: ok_fd'.
        rewrite (linear_c_nil).
        case: (linear_c fn) => lbl lbody /=.
        have sz_nz : (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd) == 0)%Z = false.
        + move: ok_save_stack; clear - stk_sz_pos stk_extra_sz_pos; rewrite !zify => - [] [] C [] D _ _.
          apply/eqP.
          by have /= := [elaborate wsize_size_pos Uptr]; lia.

        set cmd_set_up_sp := set_up_sp_register _ _ _ _ _.
        set cmd_push_to_save := push_to_save _ _ _ _.
        set P := cmd_set_up_sp ++ cmd_push_to_save.
        set Q := (X in lbody ++ X).
        move => ok_fd' E.

        have ok_body :
          is_linear_of fn (cmd_set_up_sp ++ cmd_push_to_save ++ lbody ++ Q).
        + by rewrite catA /is_linear_of ok_fd' /=; eauto.

        have ok_rsp : get_var true vm1 vrsp = ok (Vword (top_stack (emem s1))).
        + move: (X vrsp); rewrite Vm.setP_eq /get_var /= cmp_le_refl.
          by move => /get_word_uincl_eq -/(_ (subtype_refl _)) ->.
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

        set ls0 := setpc (lset_estate ls (escs s1) m1 vm1) 0.
        rewrite -hfn in ok_body.
        have [ | vm2 [hsem hvm2 hgetrsp htmp hflags]] :=
          set_up_sp_register_ok
            hliparams
            (ls := ls0)
            (P := [::])
            ok_body
            erefl
            ok_rsp
            erefl erefl
            hneq_vtmp2_vrsp
            hneq_vtmp_vrsp _.
        + by move=> []; apply: (spec_lip_tmp hliparams).

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
            -> is_ok (get_var true vm1 x >>= of_val (vtype x))
            -> is_ok (get_var true vm2 x >>= of_val (vtype x)).
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
        move: hsem => /=; set ls1 := setpc _ _ => hsem.
        have hntosave: ~~ Sv.mem (vid (lip_tmp2 liparams)) (sv_of_list fst to_save).
        + rewrite /to_save; apply /Sv_memP => /sv_of_listP.
          rewrite map_cat mem_cat in_cons in_nil orbF => /orP [].
          + by move=> /sv_of_listP; apply /Sv_memP.
          by move=> /eqP [] /= h; apply (spec_lip_tmp hliparams); rewrite h.
        have hle: (wunsigned (top_stack (emem s1)) <= wunsigned (top_stack m0))%Z.
        + by have := ok_m0; rewrite EQ /= => ->; apply Z.le_refl.
        case: (can_push ok_m1' stk_sz_pos stk_extra_sz_pos hle_rsp spill_unchanged
                  wf_to_save1 ok_to_save1 (m1:= m1) (m2 := m1) _ hle M _ (Z.le_refl _)) => // [m3 [ok_m3 H3 M3' U3]].
        have [] := spec_lip_lstores hliparams (rspi := vrspi) (s:= to_estate ls1) hntosave hneq_vtmp2_vrsp _ ok_m3.
        + by rewrite hgetrsp /= truncate_word_u.
        move=> vm2' hsem_push hvm2'.
        have := [elaborate sem_fopns_args_lsem hsem_push ok_body].
        set ls2 := (of_estate (with_mem _ _) _ _) => {hsem_push} exec_save_to_stack.

        have M3 : match_mem_gen (top_stack m0) m1' m3 := mm_alloc hle M3' ok_m1'.
        rewrite catA hfn in ok_body.
        have hrsp: (set_RSP p m1' (kill_vars (ra_undef fd var_tmps) s1)).[vrsp] = Vword (top_stack m1').
        + by rewrite Vm.setP_eq vm_truncate_val_eq.
        have S': source_mem_split m1' (top_stack m1').
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
        have MAX': max_bound_sub fn (top_stack m1').
        + move=> fd''; rewrite ok_fd => -[?]; subst fd''.
          have := MAX _ ok_fd.
          rewrite /frame_size EQ /= /align_top_stack /align_top -(alloc_stack_top_stack ok_m1').
          move=> [? [-> _]].
          rewrite wunsigned_add; first by lia.
          have /= habove := A.(ass_above_limit).
          have hrange1 := [elaborate wunsigned_range (top_stack m1')].
          have hrange2 := [elaborate wunsigned_range (top_stack (emem s1))].
          by lia.
        have vm2'_get_rsp : get_var true vm2' vrsp = ok (Vword top).
        + rewrite -(get_var_eq_ex _ _ hvm2') //.
          by move=> /Sv.singleton_spec h; apply hneq_vtmp2_vrsp; rewrite h.
        have X' : set_RSP p m1' (kill_vars (ra_undef fd var_tmps) s1) <=1 vm2'.
        + apply: (vm_uincl_after_alloc_stack X EQ _ _ ok_m1').
          + rewrite /savedstackreg E1 Sv_union_empty.
            apply: (eq_exT (vm2:=to_estate ls1)).
            + by apply/eq_exS;apply: eq_exI hvm2'; rewrite /var_tmps /var_tmp2; SvD.fsetdec.
            by apply: eq_exI hvm2; rewrite /var_tmps /= -/var_tmp -/vrsp; SvD.fsetdec.
          by rewrite vm2'_get_rsp /top /top_stack_after_alloc wrepr_opp.
        have [m4 vm4 {}E K4 X4 H4 M4 U4] :=
          E (setpc _ _) m3 vm2' P Q M3 X'  D ok_body erefl hfn _ hrsp S' MAX'.
        have vm4_get_rsp : get_var true vm4 vrsp >>= to_pointer = ok top.
        + rewrite -(get_var_eq_ex _ _ K4).
          + by rewrite vm2'_get_rsp /= truncate_word_u.
          have /disjointP K := sem_RSP_GD_not_written var_tmps_not_magic exec_body.
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
          ∀ (x : var_eqType) (ofs : Z_eqType),
             (x, ofs) \in to_restore ->
             exists2 ws, vtype x = sword ws /\ lip_check_ws liparams ws &
             exists2 w: word ws, read m3 Aligned (top + wrepr Uptr ofs)%R ws = ok w &
                                 read m4 Aligned (top + wrepr Uptr ofs)%R ws = ok w.
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
           Let: ws := if vtype x is sword ws then ok ws else Error ErrType in
           Let _ := assert (lip_check_ws liparams ws) ErrType in
           Let w := read m4 Aligned (top + wrepr Uptr ofs)%R ws in
           set_var true vm x (Vword w)) vm4 to_restore = ok vm5.
        + elim: to_restore (vm4) read_in_spilled => /= [ | [x ofs] to_restore ih] vm4' read_in_spilled; first by eauto.
          have [ws [ht hchk] [w _ hr]] := read_in_spilled _ _ (mem_head _ _).
          rewrite ht /= hchk /= hr /= set_var_eq_type // ?ht //=; apply ih.
          by move=> y yofs hin; apply read_in_spilled; rewrite in_cons hin orbT.
        set ls3 := setpc _ (size (P ++ lbody)) in E.
        have [vm5' sem_op_loads E5]:=
          spec_lip_lloads hliparams (rspi := vrspi) (s:= to_estate ls3) rsp_not_saved tmp2_not_saved hneq_vtmp2_vrsp
            vm4_get_rsp sem_loads.
        move: (ok_body); rewrite -(cats0 Q) /Q /= catA => ok_body'.
        have exec_restore_from_stack := [elaborate sem_fopns_args_lsem sem_op_loads ok_body'].
        have hvm5:
          forall x, if x \in (map fst to_restore) then
                    exists ofs ws w,
                      [/\ vtype x = sword ws
                        , (x, ofs) \in to_restore
                        , read m4 Aligned (top + wrepr Uptr ofs)%R ws = ok w
                        & vm5.[x] = Vword w ]
                     else
                       vm5.[x] = vm4.[x].
        + move=> y; elim: (to_restore) (vm4) sem_loads => /= [ | [x ofs] to_rest ih] vm.
          + by move=> [<-].
          case ht: vtype => [|||ws'] //=; t_xrbindP => vm' hchk w hr /set_varP [_ _ hvm] /ih /=.
          rewrite in_cons; case: ifP => hin.
          + rewrite orbT => -[yofs] [yws] [yw] [h1 h2 h3 h4].
            by exists yofs, yws, yw; split => //; rewrite in_cons h2 orbT.
          rewrite hvm Vm.setP eq_sym => ->.
          case: eqP => /= [-> | //].
          exists ofs, ws', w; split => //; first by apply mem_head.
          by rewrite ht cmp_le_refl.
        have {hvm5} hvm5' :
          forall x, vm5'.[x] = if x == var_tmp2 then vm5'.[x] else
                               if x \in map fst (sf_to_save (f_extra fd)) then vm2.[x]
                               else if x == vrsp then Vword ts else vm4.[x].
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
        exists m4 vm5' => //.
        + have heq1 : (lset_estate (setpc ls (size P)) (escs s1) m3 vm2') = ls2.
          + by rewrite /ls2 /= /P size_cat /cmd_push_to_save /push_to_save size_map.
          rewrite heq1 in E; rewrite -hfn in exec_restore_from_stack.
          have := lsem_trans4 hsem exec_save_to_stack E exec_restore_from_stack.
          by rewrite cats0 !size_cat /pop_to_save size_map.
        + move => x /Sv_memP; rewrite hvm5'.
          rewrite SvP.diff_mem negb_and => /orP[]; last first.
          * move/negbNE; rewrite sv_of_list_map.
            have -> : (id \o fst) = fst by done.
            move=> /dup [hin]; rewrite sv_of_listE => hin'.
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
          case/norP => x_ni_k /norP[] x_neq_tmp2 /norP[] x_neq_tmp x_not_flag.
          rewrite (negbTE x_neq_tmp2).
          case: eqP => heq.
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
        + move => x; rewrite !Vm.setP kill_varsE Vm.setP hvm5' (eq_sym x); case: eqP => x_rsp.
          + subst x. move/eqP/negbTE: hneq_vtmp2_vrsp => ->.
            by rewrite vrsp_to_save /= cmp_le_refl eqxx.
          rewrite Sv_mem_add sv_of_listE map_id eq_sym /=.
          case: eqP.
          + by move=> ?; subst x; apply compat_value_uincl_undef; apply Vm.getP.
          move/eqP/negbTE: x_rsp; rewrite eq_sym => -> _ /=.
          case: ifP => // hin.
          by apply compat_value_uincl_undef; apply Vm.getP.
        + etransitivity; [exact: H3 | ].
          exact: preserved_metadata_alloc ok_m1' H4.
        + exact: mm_free M4.
        etransitivity; [exact: U3 | exact: U4].
      }
    }
    - (* Internal function, return address in register “ra” *)
    { case: ra EQ ok_ret_addr X free_ra ok_lret exec_body ih => // -[] // ws // ra EQ ra_well_typed X /andP[] _ ra_notin_k.
      case: lret => // - [] [] [] caller lret cbody pc.
      case: (ws =P Uptr) => // E.
      subst ws.
      move=> [] ok_cbody ok_pc mem_lret [] retptr ok_retptr ok_ra exec_body ih.
      have {ih} := ih fn 2%positive.
      rewrite /checked_c ok_fd chk_body => /(_ erefl).
      rewrite (linear_c_nil _ _ _ _ _ [:: _ ]).
      case: (linear_c fn) (valid_c fn (f_body fd) 2%positive) => lbl lbody ok_lbl /= E.
      set P := (P in P :: lbody ++ _).
      set Q := (Q in P :: lbody ++ Q).
      move => ok_fd'.
      have ok_body : is_linear_of fn ([:: P ] ++ lbody ++ Q).
      + by rewrite /is_linear_of ok_fd'; eauto.
      have X1 : set_RSP p m1' (kill_vars (ra_undef fd var_tmps) s1) <=1 vm1.
      + apply: vm_uincl_kill_vars_set_incl X => //.
        + by rewrite /ra_undef /ra_vm EQ; SvD.fsetdec.
        rewrite (alloc_stack_top_stack ok_m1') top_stack_after_aligned_alloc;  last by exact: sp_aligned.
        by rewrite wrepr_opp -/(stack_frame_allocation_size fd.(f_extra)).
      have D : disjoint_labels 2 lbl [:: P].
      + by move => q [L H]; rewrite /P /is_label /= orbF; apply/eqP => ?; subst; lia.
      have hrsp: (set_RSP p m1' (kill_vars (ra_undef fd var_tmps) s1)).[vrsp] = Vword (top_stack m1').
      + by rewrite Vm.setP_eq vm_truncate_val_eq.
      have S': source_mem_split m1' (top_stack m1').
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
      have MAX': max_bound_sub fn (top_stack m1').
      + move=> fd''; rewrite ok_fd => -[?]; subst fd''.
        have := MAX _ ok_fd.
        rewrite /frame_size EQ /=.
        rewrite (wunsigned_top_stack_after_aligned_alloc stk_sz_pos stk_extra_sz_pos frame_noof sp_aligned ok_m1').
        have := stack_frame_allocation_size_bound stk_sz_pos stk_extra_sz_pos.
        by lia.

      set ls0 := setpc (lset_estate ls (escs s1) m1 vm1) 1.
      have hle: (wunsigned (top_stack (emem s1)) <= wunsigned (top_stack m0))%Z.
      + by have := MAX _ ok_fd; rewrite EQ /=; lia.
      have {E} [m2 vm2 E K2 ok_vm2 H2 M2 U2] :=
        E ls0 m1 vm1 [:: P] Q (mm_alloc hle M ok_m1') X1 D ok_body erefl hfn _
          hrsp S' MAX'.
      eexists m2 vm2; [ | | | | exact: mm_free M2 | exact: U2 ]; cycle 3.
      + move => a [] a_lo a_hi /negbTE nv.
        have /= [L H] := ass_above_limit A.
        apply: H2.
        * by rewrite (ass_root A); lia.
        rewrite (ass_valid A) nv /= !zify => - [].
        change (wsize_size U8) with 1%Z.
        rewrite (ass_add_ioff A).
        move: (sf_stk_sz _) (sf_stk_ioff _) (sf_stk_extra_sz _) (ass_ioff A) H => *.
        lia.
      + apply: (lsem_step_end E).
        rewrite catA in ok_body.
        apply: (eval_lsem1 ok_body) => //.
        rewrite /eval_instr /= /get_var /=.
        have ra_not_written : vm2.[ Var spointer ra ] = vm1.[ Var spointer ra ].
        * symmetry; apply: K2.
          have /andP [_ ?] := ra_notin_k.
          by apply/Sv_memP.
        rewrite ra_not_written ok_ra /= zero_extend_u truncate_word_u.
        have := decode_encode_label small_dom_p' mem_lret.
        rewrite ok_retptr /rdecode_label /= => -> /=.
        rewrite (eval_jumpE ok_cbody) ok_pc /=.
        reflexivity.
      + apply: eq_exI K2.
        exact: SvP.MP.union_subset_1.
      subst callee_saved; rewrite /kill_vars /=.
      move => ?; rewrite /set_RSP !Vm.setP; case: eqP => // ?.
      subst; move: (ok_vm2 vrsp).
      have SS : stack_stable m1' s2'.
      + exact: sem_one_varmap_facts.sem_stack_stable exec_body.
      rewrite valid_rsp' -(ss_top_stack SS) (alloc_stack_top_stack ok_m1').
      rewrite top_stack_after_aligned_alloc;
        last by exact: sp_aligned.
      by rewrite vm_truncate_val_eq // wrepr_opp.
    }
    (* Internal function, return address in stack at offset “rastack” *)
    {
      case : ora EQ X free_ra ok_ret_addr ok_lret => [ra | ] /= EQ X free_ra ok_ret_addr ok_lret.
      (* Initially path by register and stored on top of the stack, like for ARM *)
      (* TODO : this case and the next one duplicate proof, we should do lemma *)
      + case: ra EQ X free_ra ok_ret_addr ok_lret => // -[] // ws ra EQ X free_ra ok_ret_addr ok_lret.
        case: lret ok_lret => // -[] [] [] caller lret cbody pc.
        case: eqP => // ?; subst ws => - [] ok_cbody ok_pc mem_lret [] retptr ok_retptr ok_ra1.
        have {ih} := ih fn 2%positive.
        rewrite /checked_c ok_fd chk_body => /(_ erefl).
        rewrite (linear_c_nil _ _ _ _ _ [:: _ ]).
        case: (linear_c fn) (valid_c fn (f_body fd) 2%positive) => lbl lbody ok_lbl /= E.
        set P1 := (P in P :: _ :: lbody ++ _).
        set P2 := (P in _ :: P :: lbody ++ _).
        set Q := (Q in P1 :: P2 :: lbody ++ Q).
        move => ok_fd'.
        have ok_body : is_linear_of fn ([:: P1; P2 ] ++ lbody ++ Q).
        + by rewrite /is_linear_of ok_fd'; eauto.
        have := X vrsp; rewrite Vm.setP_eq /= cmp_le_refl.
        move=> /get_word_uincl_eq -/(_ (subtype_refl _)).
        set rsp := (X in Vword X) => ok_rsp.
        case/and5P: ok_ret_addr => _ _ /eqP ? /eqP hioff sf_align_for_ptr; subst rastack.
        have spec_m1' := alloc_stackP ok_m1'.
        have is_align_m1' := ass_align_stk spec_m1'.
        have ts_rsp : top_stack m1' = rsp.
        + rewrite (alloc_stack_top_stack ok_m1') top_stack_after_aligned_alloc; last by exact: sp_aligned.
          by rewrite wrepr_opp -/(stack_frame_allocation_size fd.(f_extra)).
        have := ass_align_stk spec_m1'.
        (* TODO this should be a lemma it is used elsewhere (above)*)
        have [m1s ok_m1s M']: 
           exists2 m1s, write m1 Aligned rsp retptr = ok m1s & match_mem_gen (top_stack m0) s1 m1s.
        + apply: mm_write_invalid.
          * by have := MAX _ ok_fd; rewrite EQ /=; lia.
          * exact: M.
          1-2: cycle -1.
          * by rewrite -ts_rsp; apply: is_align_m sf_align_for_ptr is_align_m1'.
          have := (Memory.alloc_stackP ok_m1').(ass_above_limit).
          rewrite -ts_rsp (alloc_stack_top_stack ok_m1').
          rewrite top_stack_after_aligned_alloc // wrepr_opp.
          have := ass_ioff (alloc_stackP ok_m1'); rewrite -hioff => uptr_sz.
          clear - stk_sz_pos stk_extra_sz_pos frame_noof uptr_sz.
          have := round_ws_range (sf_align (f_extra fd)) (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd)).
          rewrite -/(stack_frame_allocation_size (f_extra fd)) => hround.
          set L := stack_limit (emem s1).
          have L_range := wunsigned_range L.
          move: (stack_frame_allocation_size _) hround frame_noof => SF hround frame_noof.
          move: (top_stack (emem s1)) => T above_limit.
          have SF_range : (0 <= SF < wbase Uptr)%Z.
          - by move: ( sf_stk_sz (f_extra fd)) (sf_stk_extra_sz (f_extra fd)) stk_sz_pos stk_extra_sz_pos hround; lia.
          have X : (wunsigned (T - wrepr Uptr SF) <= wunsigned T)%Z.
          * move: (sf_stk_sz _) stk_sz_pos above_limit => n; lia.
          have {X} TmS := wunsigned_sub_small SF_range X.
          rewrite TmS in above_limit.
          lia.
        have X1 : set_RSP p m1' (kill_vars (ra_undef fd var_tmps) s1) <=1 vm1.
        + apply: vm_uincl_kill_vars_set_incl X => //.
          + by rewrite /ra_undef /ra_vm EQ; SvD.fsetdec.
          by rewrite ts_rsp.
        have D : disjoint_labels 2 lbl [:: P1; P2].
        + move => q [L H]; rewrite /P1 /P2 /= /is_label /= orbF; apply/eqP; lia.
        have hrsp: (set_RSP p m1' (kill_vars (ra_undef fd var_tmps) s1)).[vrsp] = Vword (top_stack m1').
        + by rewrite Vm.setP_eq vm_truncate_val_eq.
        have S': source_mem_split m1' (top_stack m1').
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
        have MAX': max_bound_sub fn (top_stack m1').
        + move=> fd''; rewrite ok_fd => -[?]; subst fd''.
          have := MAX _ ok_fd.
          rewrite /frame_size EQ /=.
          rewrite (wunsigned_top_stack_after_aligned_alloc stk_sz_pos stk_extra_sz_pos frame_noof sp_aligned ok_m1').
          have := stack_frame_allocation_size_bound stk_sz_pos stk_extra_sz_pos.
          by lia.

        set ls0 := setpc (lset_estate ls (escs s1) m1 vm1) 2.
        have hle: (wunsigned (top_stack (emem s1)) <= wunsigned (top_stack m0))%Z.
        + by have := MAX _ ok_fd; rewrite EQ /=; lia.
        have {E} [m2 vm2 E K2 ok_vm2 H2 M2 U2] :=
          E ls0 m1s vm1 [:: P1; P2] Q
          (mm_alloc hle M' ok_m1') X1 D ok_body erefl hfn _ hrsp S' MAX'.
        exists m2 (vm2.[vrsp <- Vword (rsp + wrepr Uptr (wsize_size Uptr))]).
        + apply: (lsem_trans3 _ E).
          + apply: (eval_lsem_step1 (pre := [:: P1 ]) ok_body) => //.
            apply: (spec_lstore hliparams) => //.
            * rewrite /get_var ok_ra1; reflexivity.
            * rewrite truncate_word_u; reflexivity.
            * rewrite /get_var ok_rsp; reflexivity.
            rewrite /= wrepr0 GRing.addr0 zero_extend_u. exact: ok_m1s.
          rewrite catA in ok_body.
          apply: (eval_lsem_step1 ok_body) => //.
          rewrite /eval_instr /= /get_var /=.
          move: (ok_vm2 vrsp).
          rewrite -(sem_preserved_RSP_GD var_tmps_not_magic exec_body); last exact: RSP_in_magic.
          rewrite /= /set_RSP Vm.setP_eq /= lp_rspE -/vrsp cmp_le_refl.
          move=> /get_word_uincl_eq -/(_ (subtype_refl _)) -> /=; rewrite truncate_word_u /=.
          assert (root_range := wunsigned_range (stack_root m1')).
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
            rewrite -/(top_stack (emem s1)); lia.
          have -> : read m2 Aligned (top_stack m1')%R Uptr = read m1s Aligned (top_stack m1')%R Uptr.
          * apply: eq_read => al i [] i_lo i_hi; symmetry; rewrite !(read8_alignment Aligned); apply: H2.
            - rewrite addE wunsigned_add; lia.
            rewrite (Memory.alloc_stackP ok_m1').(ass_valid).
            apply/orP; case.
            - apply/negP; apply: stack_region_is_free.
              rewrite -/(top_stack _).
              move: (stack_frame_allocation_size _) top_stackE sf_large => n top_stackE sf_large.
              rewrite addE !wunsigned_add; lia.
            rewrite !zify (ass_add_ioff A) -hioff addE.
            rewrite wunsigned_add; lia.
          rewrite ts_rsp (writeP_eq ok_m1s) /=.
          have := decode_encode_label small_dom_p' mem_lret.
          rewrite ok_retptr /rdecode_label /= => -> /=.
          by rewrite (eval_jumpE ok_cbody) ok_pc.
        + apply eq_exT with vm2.
          + by apply: eq_exI K2; SvD.fsetdec.
          by move=> ? hx; rewrite Vm.setP_neq //; apply/eqP; SvD.fsetdec.
        + subst callee_saved; rewrite /kill_vars /=.
          by move => ?; rewrite /set_RSP !Vm.setP; case: eqP.
        + etransitivity.
          + apply: (preserved_metadata_store_top_stack ok_m1');
              last by rewrite -hioff; apply Z.le_refl.
            by rewrite top_stack_after_aligned_alloc // wrepr_opp; apply: ok_m1s.
          move => a [] a_lo a_hi /negbTE nv.
          have /= [L R] := ass_above_limit A.
          apply: H2.
          * by rewrite (ass_root A); lia.
          rewrite (ass_valid A) nv /= !zify => - [].
          change (wsize_size U8) with 1%Z.
          rewrite (ass_add_ioff A).
          move: (sf_stk_sz _) (sf_stk_ioff _) (sf_stk_extra_sz _) (ass_ioff A) R; lia.
        + exact: mm_free M2.
        etransitivity; last exact: U2.
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
      (* Directly path on top of the stack *)
      case: lret ok_lret => // - [] [] [] caller lret cbody pc [] ok_cbody ok_pc mem_lret [] retptr ok_retptr [] rsp ok_rsp ok_ra.
      have := X vrsp.
      rewrite Vm.setP_eq vm_truncate_val_eq // ok_rsp => /andP[] _ /eqP /=.
      rewrite zero_extend_u => ?; subst rsp.
      have {ih} := ih fn 2%positive.
      rewrite /checked_c ok_fd chk_body => /(_ erefl).
      rewrite (linear_c_nil _ _ _ _ _ [:: _ ]).
      case: (linear_c fn) (valid_c fn (f_body fd) 2%positive) => lbl lbody ok_lbl /= E.
      set P := (P in P :: lbody ++ _).
      set Q := (Q in P :: lbody ++ Q).
      move => ok_fd'.
      have ok_body : is_linear_of fn ([:: P ] ++ lbody ++ Q).
      + by rewrite /is_linear_of ok_fd'; eauto.
      have X1 : set_RSP p m1' (kill_vars (ra_undef fd var_tmps) s1) <=1 vm1.
      + apply: vm_uincl_kill_vars_set_incl X => //.
        + by SvD.fsetdec.
        rewrite (alloc_stack_top_stack ok_m1') top_stack_after_aligned_alloc;  last by exact: sp_aligned.
        by rewrite wrepr_opp -/(stack_frame_allocation_size fd.(f_extra)).
      have D : disjoint_labels 2 lbl [:: P].
      + by move => q [L H]; rewrite /P /is_label /= orbF; apply/eqP => ?; subst; lia.
      have hrsp: (set_RSP p m1' (kill_vars (ra_undef fd var_tmps) s1)).[vrsp] = Vword (top_stack m1').
      + by rewrite Vm.setP_eq vm_truncate_val_eq.
      have S': source_mem_split m1' (top_stack m1').
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
      have MAX': max_bound_sub fn (top_stack m1').
      + move=> fd''; rewrite ok_fd => -[?]; subst fd''.
        have := MAX _ ok_fd.
        rewrite /frame_size EQ /=.
        rewrite (wunsigned_top_stack_after_aligned_alloc stk_sz_pos stk_extra_sz_pos frame_noof sp_aligned ok_m1').
        have := stack_frame_allocation_size_bound stk_sz_pos stk_extra_sz_pos.
        by lia.

      set ls0 := setpc (lset_estate ls (escs s1) m1 vm1) 1.
      have hle: (wunsigned (top_stack (emem s1)) <= wunsigned (top_stack m0))%Z.
      + by have := MAX _ ok_fd; rewrite EQ /=; lia.
      have {E} [m2 vm2 E K2 ok_vm2 H2 M2 U2] :=
        E ls0 m1 vm1 [:: P ] Q (mm_alloc hle M ok_m1') X1 D ok_body erefl hfn _ hrsp S' MAX'.
      exists m2 (vm2.[vrsp <- Vword
         (top_stack (emem s1) - wrepr Uptr (round_ws (sf_align (f_extra fd)) (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd))) + wrepr Uptr (wsize_size Uptr))]);
         [ | | | | exact: mm_free M2 | exact: U2 ].
      + apply: (lsem_step_end E).
        rewrite catA in ok_body.
        apply: (eval_lsem1 ok_body) => //.
        rewrite /eval_instr /= /get_var.
        move: (ok_vm2 vrsp).
        rewrite -(sem_preserved_RSP_GD var_tmps_not_magic exec_body); last exact: RSP_in_magic.
        rewrite /= /set_RSP Vm.setP_eq /= lp_rspE -/vrsp cmp_le_refl.
        move=> /get_word_uincl_eq -/(_ (subtype_refl _)) -> /=; rewrite truncate_word_u /=.
        case/and4P: ok_ret_addr => _ /eqP hrastack /eqP hioff sf_aligned_for_ptr.
        assert (root_range := wunsigned_range (stack_root m1')).
        have top_range := ass_above_limit A.
        have top_stackE := wunsigned_top_stack_after_aligned_alloc stk_sz_pos stk_extra_sz_pos frame_noof sp_aligned ok_m1'.
        subst rastack.
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
          rewrite -/(top_stack (emem s1)); lia.
        have -> : read m2 Aligned (top_stack m1')%R Uptr = read m1 Aligned (top_stack m1')%R Uptr.
        * apply: eq_read => al i [] i_lo i_hi; symmetry; rewrite !(read8_alignment Aligned); apply: H2.
          - rewrite addE wunsigned_add; lia.
          rewrite (Memory.alloc_stackP ok_m1').(ass_valid).
          apply/orP; case.
          - apply/negP; apply: stack_region_is_free.
            rewrite -/(top_stack _).
            move: (stack_frame_allocation_size _) top_stackE sf_large => n top_stackE sf_large.
            rewrite addE !wunsigned_add; lia.
          rewrite !zify (ass_add_ioff A) -hioff addE.
          rewrite wunsigned_add; lia.
        rewrite (alloc_stack_top_stack ok_m1') top_stack_after_aligned_alloc //.
        move: ok_ra; rewrite wrepr0 GRing.addr0 /stack_frame_allocation_size wrepr_opp => -> /=.
        have := decode_encode_label small_dom_p' mem_lret.
        rewrite ok_retptr /rdecode_label /= => -> /=.
        by rewrite (eval_jumpE ok_cbody) ok_pc.
      + apply eq_exT with vm2.
        + by apply: eq_exI K2; SvD.fsetdec.
        by move=> x hx; rewrite Vm.setP_neq //; apply/eqP; SvD.fsetdec.
      + subst callee_saved; rewrite /kill_vars /=.
        by move => ?; rewrite /set_RSP !Vm.setP; case: eqP.
      move => a [] a_lo a_hi /negbTE nv.
      have /= [L H] := ass_above_limit A.
      apply: H2.
      * by rewrite (ass_root A); lia.
      rewrite (ass_valid A) nv /= !zify => - [].
      change (wsize_size U8) with 1%Z.
      rewrite (ass_add_ioff A).
      move: (sf_stk_sz _) (sf_stk_ioff _) (sf_stk_extra_sz _) (ass_ioff A) H; lia.
    }
  Qed.

  Lemma linear_fdP ii k s1 fn s2 :
    sem_call p var_tmps ii k s1 fn s2 →
    Pfun ii k s1 fn s2.
  Proof.
    exact:
      (sem_call_Ind
         Hnil
         Hcons
         HmkI
         Hasgn
         Hopn
         Hsyscall
         Hif_true
         Hif_false
         Hwhile_true
         Hwhile_false
         Hcall
         Hproc).
  Qed.

  End STACK.

  Lemma linear_exportcallP gd scs m fn args scs' m' res :
    sem_export_call p var_tmps gd scs m fn args scs' m' res →
    ∃ fd lfd,
      [/\
        get_fundef p.(p_funcs) fn = Some fd,
        get_fundef p'.(lp_funcs) fn = Some lfd,
        lfd.(lfd_export) &
      ∀ lm vm args',
        vm.[vid (lp_rsp p')] = Vword (top_stack m) →
        match_mem m lm →
        get_var_is false vm lfd.(lfd_arg) = ok args' →
        List.Forall2 value_uincl args args' →
        vm.[vid p'.(lp_rip)] = Vword gd →
        vm_initialized_on vm (lfd_callee_saved lfd) →
        (fd.(f_extra).(sf_stk_max) + wsize_size fd.(f_extra).(sf_align) - 1 <= wunsigned (top_stack m))%Z ->
        ∃ vm' lm' res',
          [/\
            lsem_exportcall p' scs lm fn vm scs' lm' vm',
            vm'.[vid (lp_rsp p')] = Vword (top_stack m),
            match_mem m' lm',
            target_mem_unchanged m (align_top_stack (top_stack m) fd.(f_extra)) fd.(f_extra).(sf_stk_max) lm lm',
            get_var_is false vm' lfd.(lfd_res) = ok res' &
            List.Forall2 value_uincl res res'
          ]
      ].
  Proof.
    case => fd ok_fd Export to_save_not_result RSP_not_result H.
    exists fd, (linear_fd fn fd).2; split.
    - exact: ok_fd.
    - exact: get_fundef_p' ok_fd.
    - exact: Export.
    rewrite lp_rspE => lm vm args' vm_rsp M ok_args' args_args' vm_rip safe_registers enough_stk.
    have {H}[] := H vm args' ok_args' args_args' vm_rsp.
    - by move: vm_rip; rewrite lp_ripE.
    move => m1 k m2 vm2 res' ok_save_stack ok_callee_saved ok_m1 sexec ok_res' res_res' vm2_rsp ?; subst m'.
    set k' := Sv.union k (Sv.union match fd.(f_extra).(sf_return_address) with RAreg ra _ | RAstack (Some ra) _ _ => Sv.singleton ra | RAstack _ _ _ => Sv.empty | RAnone => Sv.union var_tmps vflags end (if fd.(f_extra).(sf_save_stack) is SavedStackReg r then Sv.singleton r else Sv.empty)).
    set s1 := {| escs := scs; emem := m ; evm := vm |}.
    set s2 := {| escs := scs'; emem := free_stack m2 ; evm := set_RSP p (free_stack m2) vm2 |}.
    have /= hss := sem_stack_stable sexec.
    have {sexec} /linear_fdP : sem_call p var_tmps dummy_instr_info k' s1 fn s2.
    - econstructor.
      + exact: ok_fd.
      + by rewrite /ra_valid; move/is_RAnoneP: Export => ->.
      + exact: ok_save_stack.
      + by rewrite /top_stack_aligned Export.
      + exact: vm_rsp.
      + exact: ok_m1.
      + move: sexec.
        rewrite /ra_undef_vm /ra_undef /ra_undef_vm_none /ra_undef_none /ra_vm.
        move/is_RAnoneP: Export => ->.
        exact.
      + exact: vm2_rsp.
      reflexivity.
    set m0 := m.
    set sp0 := align_top_stack (top_stack m) fd.(f_extra).
    set max0 := fd.(f_extra).(sf_stk_max).
    have enough_space : (0 <= max0 <= wunsigned sp0)%Z.
    + have := checked_prog ok_fd.
      rewrite /check_fd; t_xrbindP=> _ _ ok_stk_sz _ _ _.
      case/and4P: ok_stk_sz => /ZleP stk_sz_pos /ZleP stk_extra_sz_pos /ZltP frame_noof /ZleP stk_frame_le_max.
      rewrite /max0 /sp0; split.
      + by have := frame_size_bound stk_sz_pos stk_extra_sz_pos; lia.
      rewrite /align_top_stack /align_top.
      have: (0 <= sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd) <= wunsigned (top_stack m))%Z.
      + have := frame_size_bound stk_sz_pos stk_extra_sz_pos.
        have := wsize_size_pos (sf_align (f_extra fd)). lia.
      move=> /(top_stack_after_alloc_bounded (ws:=sf_align (f_extra fd))).
      rewrite wunsigned_add; first by lia.
      rewrite -(alloc_stack_top_stack ok_m1).
      have := (alloc_stackP ok_m1).(ass_above_limit).
      have := [elaborate (wunsigned_range (top_stack m1))].
      have := [elaborate (wunsigned_range (top_stack m))].
      by lia.
    set ls0 := ls_export_initial scs lm vm fn.
    case/(_ m0 sp0 max0 _ _ ls0 lm vm (linear_body liparams p fn fd.(f_extra)
        fd.(f_body)).2 RAnone None (top_stack m)
        (map fst fd.(f_extra).(sf_to_save)) M _ _ erefl).
    - exact: enough_space.
    - have := checked_prog ok_fd.
      rewrite /check_fd; t_xrbindP=> _ _ ok_stk_sz _ _ _.
      case/and4P: ok_stk_sz => /ZleP stk_sz_pos /ZleP stk_extra_sz_pos /ZltP frame_noof /ZleP stk_frame_le_max.
      rewrite /m0 /sp0 /align_top_stack /align_top.
      have hass := alloc_stackP ok_m1.
      have [_] := hass.(ass_above_limit).
      rewrite (alloc_stack_top_stack ok_m1).
      rewrite wunsigned_add; first by lia.
      rewrite -(alloc_stack_top_stack ok_m1).
      have := hass.(ass_above_limit).
      have := [elaborate (wunsigned_range (top_stack m1))].
      have := [elaborate (wunsigned_range (top_stack m))].
      by lia.
    - move => x; rewrite !Vm.setP vm_truncate_val_eq //.
      case: eqP => ? /=; first by subst; rewrite vm_rsp.
      by apply vm_uincl_kill_vars.
    - by eexists; first exact: get_fundef_p' ok_fd.
    - eexists; first exact: ok_fd.
      by apply/is_RAnoneP: Export.
    - by [].
    - eexists; first exact: ok_fd.
      by rewrite /= Export.
    - eexists; first exact: ok_fd.
      by rewrite /= Export.
    - by move: safe_registers; rewrite /= Export.
    - by move=> pr ->.
    - move=> fd'; rewrite ok_fd => -[?]; subst fd'.
      rewrite /= Export /max0 /sp0.
      split; first by apply Z.le_refl.
      split=> //.
      rewrite /align_top_stack /align_top -(alloc_stack_top_stack ok_m1).
      have /= habove := (alloc_stackP ok_m1).(ass_above_limit).
      have := checked_prog ok_fd.
      rewrite /check_fd; t_xrbindP => _ _ ok_stk_sz _ _ _.
      case/and4P: ok_stk_sz => /= /ZleP stk_sz_pos /ZleP stk_extra_sz_pos /ZltP frame_noof /ZleP stk_frame_le_max.
      rewrite wunsigned_add; first by lia.
      + have := [elaborate (wunsigned_range (top_stack m1))].
        have := [elaborate (wunsigned_range (top_stack m))].
        by lia.
    - by rewrite ok_fd => _ [<-]; rewrite Export.
    move => lmo vmo texec vm_eq_vmo s2_vmo ? M' U'.
    have vm2_vmo : ∀ r, List.In r (f_res fd) → (value_uincl vm2.[r] vmo.[r]).
    - move => r r_in_result.
      have r_not_saved : ¬ Sv.In r (sv_of_list id (map fst fd.(f_extra).(sf_to_save))).
      + apply/Sv_memP.
        rewrite sv_of_listE map_id -sv_of_listE; apply/Sv_memP => K.
        move/disjointP: to_save_not_result => /(_ _ K).
        by apply; apply/Sv_memP; rewrite sv_of_listE; apply/in_map; exists r.
      apply: value_uincl_trans (s2_vmo r).
      have r_not_rsp : vrsp != r.
      + apply/eqP => K.
        by move: RSP_not_result; rewrite sv_of_listE; apply/negP/negPn/in_map; exists r.
      rewrite Vm.setP_neq // kill_varsE Vm.setP_neq //.
      rewrite /killed_by_exit Sv_mem_add.
      case: eqP => [ | _]; last by move /Sv_memP: r_not_saved => /negbTE ->.
      have := checked_prog ok_fd.
      rewrite /check_fd; t_xrbindP => _ _ _ + _ _ /= heq.
      move/is_RAnoneP: Export => ->; rewrite -heq.
      by case/in_map; exists r.
    have : ∃ lres : values,
        [/\ get_var_is false vmo (f_res fd) = ok lres & List.Forall2 value_uincl res lres ].
    {
      move/mapM_Forall2: ok_res' res_res' vm2_vmo.
      move: res' res (f_res fd).
      elim => [ | r' res' ih ].
      + move => _ _ /List_Forall2_inv_r-> /List_Forall2_inv_r -> _.
        by exists [::].
      move => _ _ /List_Forall2_inv_r[] d [] ds [] -> [] ok_r' ok_res' /List_Forall2_inv_r[] r [] res [] -> [] r_r' res_res' vm2_vmo.
      have := vm2_vmo d (or_introl _ erefl).
      move: ok_r'; rewrite {1}/get_var /= => -[?] v_v'; subst r'.
      move: ih => /(_ _ _ ok_res' res_res') [].
      + by move => x hx; apply: vm2_vmo; right.
      move => lres [] -> /= res_lres.
      eexists; split; first reflexivity.
      constructor => //.
      by apply: value_uincl_trans r_r' v_v'.
    }
    case => lres [] ok_lres res_lres.
    exists vmo, lmo, lres; split.
    - econstructor; first exact: get_fundef_p' ok_fd.
      + exact: Export.
      + exact: texec.
      move => r hr; apply: vm_eq_vmo.
      subst k'.
      move: ok_callee_saved hr; clear.
      rewrite -/(ra_vm _ _) -/(saved_stack_vm _).
      move: (Sv.union k _) => X.
      clear.
      rewrite sv_of_list_map Sv.diff_spec => S hrC [] hrX; apply.
      apply: S.
      by rewrite Sv.inter_spec.
    - have := s2_vmo vrsp; rewrite Vm.setP_eq /= cmp_le_refl => ?.
      by apply get_word_uincl_eq.
    - move: M'.
      rewrite /m0.
      by have /ss_top_stack -> :=
        alloc_free_stack_stable (alloc_stackP ok_m1) hss (free_stackP m2).
    - exact: U'.
    - by rewrite /= Export.
    exact: res_lres.
  Qed.

End PROOF.

End WITH_PARAMS.
