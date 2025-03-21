(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
(* Require Export psem. *)
Require Import expr.

Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.
(* Open Scope vm_scope. *)

(*Lemma Z_eqP : Equality.axiom Z.eqb.
Proof. apply: Z.eqb_spec. Qed.

HB.instance Definition _ := hasDecEq.Build Z Z_eqP.
Section TYPE.
  *)

(* Local Existing Instance nosubword. *)

(* Context
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}. *)

(* Section EXPR.

(* Context (gd : glob_decls). *)

Definition gvtype (x:gvar) :=
  Let _ := assert (is_lvar x || is_ok (get_global gd (gv x))) tt in
  ok (vtype (gv x)).

Fixpoint etype (e : pexpr) : result unit stype :=
  match e with
  | Pconst _ => ok sint
  | Pbool _ => ok sbool
  | Parr_init len => ok (sarr len)
  | Pvar x => gvtype x
  | Pget al aa ws x e =>
    Let tx := gvtype x in
    Let te := etype e in
    Let _ := assert [&& is_sarr tx & subtype sint te] tt in
    ok (sword ws )
  | Psub aa ws len x e =>
    Let tx := gvtype x in
    Let te := etype e in
    Let _ := assert [&& is_sarr tx & subtype sint te] tt in
    ok (sarr (Z.to_pos (arr_size ws len)))
  | Pload al ws x e =>
    let tx := (vtype x) in
    Let te := etype e in
    Let _ := assert [&& subtype (sword Uptr) tx & subtype (sword Uptr) te] tt in
    ok (sword ws)
  | Papp1 op e1 =>
    Let te := etype e1 in
    let (tin, tout) := type_of_op1 op in
    Let _ := assert (subtype tin te) tt in
    ok tout
  | Papp2 op e1 e2 =>
    Let te1 := etype e1 in
    Let te2 := etype e2 in
    let: ((tin1, tin2), tout) := type_of_op2 op in
    Let _ := assert [&& subtype tin1 te1 & subtype tin2 te2] tt in
    ok tout
  | PappN op es =>
    Let tes := mapM etype es in
    let (tins, tout) := type_of_opN op in
    Let _ := assert (all2 subtype tins tes) tt in
    ok tout
  | Pif ty e e1 e2 =>
    Let te := etype e in
    Let te1 := etype e1 in
    Let te2 := etype e2 in
    Let _ := assert [&& subtype sbool te, subtype ty te1 & subtype ty te2] tt in
    ok ty
  end. *)

(* Inductive safe_cond :=
  | Is_var_init of var                  (* Is_var_init x : the variable is initialized *)
  | Is_arr_init of var & pexpr & pexpr  (* Is_arr_init x e1 e2 : the array is initialized between e1 and e2 *)
  | Is_mem_init of pexpr & pexpr        (* Is_mem_init e1 e2 : the memory is initialized between e1 and e2 *)
(*  | In_range of pexpr & pexpr & pexpr   (* In_range lo hi e : e in [lo; li] *) *)
  | Is_aligned of wsize & pexpr         (* Aligned sz e : wsize_size sz | e *)
  | LT of pexpr & pexpr                 (* LT e1 e2 : e1 < e2 *)
  | LE of pexpr & pexpr                 (* LE e1 e2 : e1 <= e2 *)
  | EQ of pexpr & pexpr                 (* EQ e1 e2 : e1 = e2 *)
  | Not of safe_cond                    (* Not sc : !sc *)
  | And of safe_cond & safe_cond        And sc1 sc2 : sc1 && sc2
  .*)
Section EXPR.
Context {pd: PointerData}.



Definition emin_signed sz := Pconst (wmin_signed sz).
Definition emax_signed sz := Pconst (wmax_signed sz).
Definition ezero := Pconst 0.
Definition emax_unsigned sz := Pconst (wmax_unsigned sz).

(* Definition eint_of_wint sg sz e := Papp1 (Owi1 sg (WIint_of_word sz)) e. *)

Definition eint_of_word (sg:signedness) sz e := Papp1 (Oint_of_word sz) e.

Definition emuli e1 e2 :=
  Papp2 (Omul Op_int) e1 e2.

Definition eaddi e1 e2 :=
  Papp2 (Oadd Op_int) e1 e2.

Definition sc_lt e1 e2 := Papp2 (Olt Cmp_int) e1 e2.
Definition sc_le e1 e2 := Papp2 (Ole Cmp_int) e1 e2.
Definition sc_eq e1 e2 := Papp2 (Oeq Op_int) e1 e2.
Definition sc_not sc := Papp1 Onot sc.
Definition sc_neq e1 e2 := Papp2 (Oneq Op_int) e1 e2.
Definition sc_and sc1 sc2 :=  Papp2 Oand sc1 sc2.

Definition sc_in_range lo hi e := sc_and (sc_le lo e) (sc_le e hi).

Definition sc_uint_range sz e := sc_in_range ezero (emax_unsigned sz) e.

Definition sc_sint_range sz e := sc_in_range (emin_signed sz) (emax_signed sz) e.

(* Definition sc_wi_range sg sz e := signed (sc_uint_range sz) (sc_sint_range sz) sg e. *)

Definition sc_op1 (op1 : sop1) (e : pexpr) : seq pexpr :=
  [::].
  (* match op1 with
  | Owi1 sg o =>
    match o with
    | WIword_of_int sz => [:: sc_wi_range sg sz e]
    | WIint_of_word sz => [::]
    | WIword_of_wint sz => [::]
    | WIwint_of_word sz => [::]
    | WIword_ext szo szi => [::]
    | WIneg sz =>
        signed  [::sc_eq (eint_of_wint sg sz e) ezero ]
                [::sc_neq (eint_of_wint sg sz e) (emin_signed sz)] sg
    end
  | _ => [::]
  end. *)
(* 
Definition sc_wi_range_op2 sg sz op e1 e2 :=
  sc_wi_range sg sz (Papp2 op (eint_of_wint sg sz e1) (eint_of_wint sg sz e2)). *)

Definition sc_divmod sg sz e1 e2 :=
 let sc := if sg is Unsigned then [::]
           else [:: sc_not (sc_and (sc_eq e1 (emin_signed sz)) (sc_eq e2 (Pconst (-1)))) ] in
 [::sc_neq e2 ezero & sc].

(* Definition sc_wiop2 sg sz o e1 e2 :=
  match o with
  | WIadd => [:: sc_wi_range_op2 sg sz (Oadd Op_int) e1 e2]
  | WImul => [:: sc_wi_range_op2 sg sz (Omul Op_int) e1 e2]
  | WIsub => [:: sc_wi_range_op2 sg sz (Osub Op_int) e1 e2]
  | WIdiv => sc_divmod sg sz (eint_of_wint sg sz e1) (eint_of_wint sg sz e2)
  | WImod => sc_divmod sg sz (eint_of_wint sg sz e1) (eint_of_wint sg sz e2)
  | WIshl => [:: sc_wi_range sg sz (Papp2 (Olsl Op_int) (eint_of_wint sg sz e1) (eint_of_wint Unsigned U8 e2)) ]
  | WIshr => [::]
  | WIeq | WIneq | WIlt | WIle | WIgt | WIge  => [::]
  end. *)

Definition sc_op2 (o : sop2) e1 e2 :=
  match o with
  (* | Owi2 sg sz o => sc_wiop2 sg sz o e1 e2 *)
  | Odiv (Cmp_w sg sz) => sc_divmod sg sz (eint_of_word sg sz e1) (eint_of_word sg sz e2)
  | Omod (Cmp_w sg sz) => sc_divmod sg sz (eint_of_word sg sz e1) (eint_of_word sg sz e2)
  | _ => [::]
  end.

Definition sc_var_init (x:var_i) :=
  if is_sarr (vtype x) then [::]
  else [:: Pis_var_init x].

Definition sc_gvar_init x :=
  if is_lvar x then sc_var_init (gv x)
  else [::].

Definition eeq e1 e2 := Papp2 (Oeq Op_int) e1 e2.

Definition emod e1 e2 := Papp2 (Omod Cmp_int) e1 e2.

Definition ewsize sz := Pconst(wsize_size sz).

Definition eaddptr e1 e2 := Papp2 (Oadd (Op_w Uptr)) e1 e2.

Definition eis_aligned e sz :=
  let sc_align := emod e (ewsize sz) in
  eeq sc_align (Pconst 0).

Definition sc_is_aligned_if al aa sz e :=
  if (al == Unaligned) || (aa == AAscale) then [::]
  else 
  [:: eis_aligned e sz].

Definition emk_scale aa sz e :=
  if aa == AAdirect then e
  else emuli e (Pconst (wsize_size sz)).

Definition sc_in_bound ty aa sz elen e :=
  match ty with
  | sarr len =>
    let i := emk_scale aa sz e in
    [:: eand (sc_le ezero i) (sc_le (eaddi i elen) (Pconst len))]
  | _ => [::] (* assert false *)
  end.


Definition sc_arr_init (x:gvar) aa sz e :=
  if is_lvar x then
    let lo := emk_scale aa sz e in
   [:: Pis_arr_init x.(gv) lo (Pconst (wsize_size sz))]
  else [::].

Definition sc_arr_get (x:gvar) al aa sz e :=
  sc_is_aligned_if al aa sz e ++
  sc_in_bound (vtype (gv x)) aa sz (Pconst (wsize_size sz)) e ++
  sc_arr_init x aa sz e .


Definition sc_arr_set (x:var_i) al aa sz e :=
  sc_is_aligned_if al aa sz e ++
  sc_in_bound (vtype x) aa sz (Pconst (wsize_size sz)) e.

Definition sc_is_aligned_if_m al sz e :=
  if (al == Unaligned) then [::]
  else
  [:: eis_aligned (eint_of_word Unsigned Uptr e) sz].

Definition i_to_ptr i := Papp1 (Oword_of_int Uptr) (Pconst i).


Definition sc_mem_valid (e: pexpr) sz :=
  [:: Pis_mem_init e (wsize_size sz)].

Fixpoint sc_e (e : pexpr) : seq pexpr :=
  match e with
  | Pconst _ | Pbool _  | Parr_init _ => [::]
  | Pvar x => sc_gvar_init x
  | Pget al aa ws x e =>
    let sce := sc_e e in
    let sc_arr := sc_arr_get x al aa ws e in
    sce ++ sc_arr

  | Psub aa ws len x e =>
    let sce := sc_e e in
    let sc_arr := sc_in_bound (vtype (gv x)) aa ws (Pconst (arr_size ws len)) e in
    sce ++ sc_arr

  | Pload al ws x e =>
    let scx := sc_var_init x in
    let sce := sc_e e in
    let plo :=  eaddptr (Plvar x) e in
    let sca := sc_is_aligned_if_m al ws plo in
    let sc_load := sc_mem_valid plo ws in

    scx ++ sce ++ sca ++ sc_load

  | Papp1 op e1 =>
    let sce1 := sc_e e1 in
    let sco := sc_op1 op e1 in
    sce1 ++ sco

  | Papp2 op e1 e2 =>
    let sce1 := sc_e e1 in
    let sce2 := sc_e e2 in
    let sco := sc_op2 op e1 e2 in
    sce1 ++ sce2 ++ sco

  | PappN op es =>
    let scs := map sc_e es in
    flatten scs

  | Pif ty e e1 e2 =>
    let sce := sc_e e in
    let sce1 := sc_e e1 in
    let sce2 := sc_e e2 in
    sce ++ sce1 ++ sce2
  | Pbig idx op var e1 e2 e3  =>
    let scidx := sc_e idx in
    let sce1 := sc_e e1 in
    let sce2 := sc_e e2 in
    let sce3 := sc_e e3 in
    scidx ++ sce1 ++ sce2 ++ sce3 
  | Pis_var_init _ | Pis_arr_init _ _ _ | Pis_mem_init _ _ => [::e]
  end.

Definition sc_lval (lv : lval) : seq pexpr :=
  match lv with
  | Lnone _ _ => [::]
  | Lvar x => [::]
  | Lmem al ws x e =>
    let scx := sc_var_init x in
    let sce := sc_e e in
    let plo:= eaddptr (Plvar x) e in
    let sca := sc_is_aligned_if_m al ws plo in
    let sc_load := sc_mem_valid plo ws in
    scx ++ sce ++ sca ++ sc_load
  | Laset al aa ws x e =>
    let sce := sc_e e in
    let sc_arr := sc_arr_set x al aa ws e in
    sce ++ sc_arr
  | Lasub aa ws len x e =>
    let sce := sc_e e in
    let sc_arr := sc_in_bound (vtype x) aa ws (Pconst (arr_size ws len)) e in
    sce ++ sc_arr
  end.

Section ASM_OP.

Context `{asmop:asmOp}.
Context {pT: progT}.

Definition e_to_assert (e:pexpr) : instr_r := Cassert Assert Cas e.

Definition instrr_to_instr (ii: instr_info) (ir: instr_r) : instr :=
  MkI ii ir.

Definition sc_e_to_instr (sc_e : pexprs) (ii : instr_info) : seq instr :=
  map (fun e => instrr_to_instr ii (e_to_assert e)) sc_e.


Fixpoint sc_instr (i : instr) : cmd :=
  let: (MkI ii ir) := i in
  match ir with
  | Cassgn lv _ _ e =>
    let sc_lv := sc_lval lv in
    let sc_e := sc_e e in
    sc_e_to_instr (sc_lv ++ sc_e) ii ++ [::i]
  | Copn lvs _ o es  => (*FIXME - Add safety conditions for o*)  
    let sc_lvs := conc_map sc_lval lvs in
    let sc_es := conc_map sc_e es in
    sc_e_to_instr (sc_lvs ++ sc_es) ii ++ [::i]
  | Csyscall lvs _ es
  | Ccall lvs _ es =>
    let sc_lvs := conc_map sc_lval lvs in
    let sc_es := conc_map sc_e es in
    sc_e_to_instr (sc_lvs ++ sc_es) ii ++ [::i]
  | Cif e c1 c2 =>
    let sc_e := sc_e e in
    let sc_c1 := conc_map sc_instr c1 in
    let sc_c2 := conc_map sc_instr c2 in
    let i := instrr_to_instr ii (Cif e sc_c1 sc_c2) in
    sc_e_to_instr (sc_e) ii ++ [::i]
  | Cfor x (d,e1,e2) c =>
    let sc_c := conc_map sc_instr c in    
    let sc_e := sc_e e1 ++ sc_e e2 in
    let i := instrr_to_instr ii (Cfor x (d,e1,e2) sc_c) in
    sc_e_to_instr (sc_e) ii ++ [::i]
  | Cwhile a c1 e ii_w c2 => 
    let sc_e := sc_e_to_instr (sc_e e) ii in
    let sc_c1 := conc_map sc_instr c1 ++ sc_e in
    let sc_c2 := conc_map sc_instr c2 in
    let i := instrr_to_instr ii (Cwhile a sc_c1 e ii_w sc_c2) in
    [::i]
  | Cassert _ _ e =>
    let sc_e := sc_e e in
    sc_e_to_instr (sc_e) ii ++ [::i]
  end.

Definition sc_cmd (c : cmd) : cmd := conc_map sc_instr c.

Definition sc_func (f:_ufundef): _ufundef :=
  let sc_body := sc_cmd f.(f_body) in
  let es := conc_map (fun e => sc_var_init e) f.(f_res) in
  let sc_res := sc_e_to_instr es dummy_instr_info  in (*FIXME - Fix instruction info*)
  let sc_body := sc_body ++ sc_res in
  {|
    f_info   := f.(f_info) ;
    f_contra := f.(f_contra) ;
    f_tyin   := f.(f_tyin) ;
    f_params := f.(f_params) ;
    f_body   := sc_body ;
    f_tyout  := f.(f_tyout) ;
    f_res    := f.(f_res) ;
    f_extra  := f.(f_extra) ;
  |}.

Definition sc_prog (p:_uprog) : _uprog :=
  let sc_funcs := map (fun f => 
    match f with
     |(fn,fd) => (fn,(sc_func fd))
    end) p.(p_funcs) in
  {| p_globs := p.(p_globs) ;
     p_funcs := sc_funcs ;
     p_abstr := p.(p_abstr) ;
     p_extra := p.(p_extra) ;
  |}.
  
  
End ASM_OP.
End EXPR.
(* 


(*Section ETYPE.

Context (s : estate).

(* Interpretation of safety conditions*)
Fixpoint sem_sc_err sc :=
  match sc with
  | Is_var_init x => ok (is_defined (evm s).[x])

  | Is_mem_init lo hi =>
    Let wlo := sem_pexpr true gd s lo >>= to_word Uptr in
    Let whi := sem_pexpr true gd s hi >>= to_word Uptr in
    let lo := wunsigned wlo in
    let hi := wunsigned whi in
    let n :=
      if (lo <=? hi) then (hi - lo + 1)
      else (wbase Uptr - lo) + hi + 1 in
    ok (all (fun i => is_ok (get (emem s) (wlo + wrepr Uptr i)%R))
            (ziota 0 n))
  | Is_arr_init x lo hi =>
    Let (n, t):= true, s.[x] in
    Let lo := sem_pexpr true gd s lo >>= to_int in
    Let hi := sem_pexpr true gd s hi >>= to_int in
    ok (all (fun i => WArray.is_init t i) (ziota lo (hi - lo + 1)))

  | Is_aligned ws e =>
    Let i := sem_pexpr true gd s e >>= to_int in
    ok ((i mod (wsize_size ws)) =? 0)%Z

  | LT e1 e2 =>
    Let i1 := sem_pexpr true gd s e1 >>= to_int in
    Let i2 := sem_pexpr true gd s e2 >>= to_int in
    ok (i1 <? i2)%Z

  | LE e1 e2 =>
    Let i1 := sem_pexpr true gd s e1 >>= to_int in
    Let i2 := sem_pexpr true gd s e2 >>= to_int in
    ok (i1 <=? i2)%Z

  | EQ e1 e2 =>
    Let i1 := sem_pexpr true gd s e1 >>= to_int in
    Let i2 := sem_pexpr true gd s e2 >>= to_int in
    ok (i1 =? i2)%Z

  | Not sc =>
    Let b := sem_sc_err sc in
    ok (~~ b)

  | And sc1 sc2 =>
    Let b1 := sem_sc_err sc1 in
    Let b2 := sem_sc_err sc2 in
    ok (b1 && b2)
  end.

Definition sem_scs_err := mapM sem_sc_err.

Definition sem_sc sc :=
  match sem_sc_err sc with
  | Ok b => b
  | _ => false
  end.

Definition sem_scs scs :=
  match sem_scs_err scs with
  | Ok bs => all id bs
  | _ => false
  end.

Fixpoint valid_scs (scs : seq safe_cond) :=
  match scs with
  | [::] => True
  | sc :: scs => is_ok (sem_sc_err sc) /\ (sem_sc sc -> valid_scs scs)
  end. *)

Lemma scs_err_cat sc1 sc2 :
  is_ok (sem_scs_err (sc1 ++ sc2)) = is_ok (sem_scs_err sc1) && is_ok (sem_scs_err sc2).
Proof.
  rewrite /sem_scs_err mapM_cat.
  case: (mapM _ sc1) => //= b1.
  case: (mapM _ sc2) => //= b2.
Qed.

Lemma sem_scs_cat sc1 sc2 :
  sem_scs (sc1 ++ sc2) = (sem_scs sc1) && (sem_scs sc2).
Proof.
  rewrite /sem_scs /sem_scs_err mapM_cat.
  case: (mapM _ sc1) => //= b1.
  case: (mapM _ sc2) => //= b2.
  + by rewrite all_cat.
  by rewrite andbF.
Qed.

Lemma sem_scs_cons sc scs :  sem_scs (sc :: scs) = sem_sc sc && sem_scs scs.
Proof.
  rewrite /sem_scs /sem_sc /=.
  case: sem_sc_err => //= b; case: sem_scs_err => //=.
  by rewrite andbF.
Qed.

Lemma valid_scs_cat scs1 scs2 :
  valid_scs scs1 ->
  (sem_scs scs1 -> valid_scs scs2) ->
  valid_scs (scs1 ++ scs2).
Proof.
  elim: scs1 => [|sc1 scs1 hrec] /=.
  + by move=> _ /(_ (erefl true)).
  move=> [h1 h2] h; split => // hsc1.
  apply hrec.
  + by apply h2.
  by move=> hscs1; apply h; rewrite sem_scs_cons hsc1 hscs1.
Qed.

Lemma valid_scs_cat' scs1 scs2 :
  valid_scs scs1 ->
  valid_scs scs2 ->
  valid_scs (scs1 ++ scs2).
Proof. by move=> h1 h2; apply valid_scs_cat. Qed.


Let P e :=
  forall ty, etype e = ok ty ->
  let sc := sc_e e in
  (* safety conditions are sufficiant *)
  (sem_scs sc -> exists (v:sem_t ty), sem_pexpr true gd s e = ok (to_val v)).

Let Q es :=
  forall tys, mapM etype es = ok tys ->
  let sc := flatten (map sc_e es) in
  (sem_scs sc ->
   List.Forall2 (fun e ty => exists (v:sem_t ty), sem_pexpr true gd s e = ok (to_val v)) es tys).

Opaque wsize_size.

Lemma is_def_type_of v :
  is_defined v →
  ∃ v' : sem_t (type_of_val v), v = (to_val v').
Proof. case: v => //=; eauto. Qed.

Lemma vtypeP x :
  valid_scs (sc_var_init x)
  ∧ (sem_scs (sc_var_init x) → ∃ v : sem_t (vtype x), get_var true (evm s) x = ok (to_val v)).
Proof.
  rewrite /get_var /sc_var_init.
  case: ifP.
  + move=> /is_sarrP [len h]; rewrite h; split => // _.
    by have := Vm.getP (evm s) x; rewrite h => /compat_valEl [? ->] /=; eauto.
  rewrite /sem_scs /= andbT => _; split => // hd /=.
  have := Vm.getP (evm s) x; rewrite /compat_val /= /compat_type /= hd.
  move=> /eqP <- /=.
  have [v -> ] := is_def_type_of hd.
  rewrite type_of_to_val; eauto.
Qed.

Lemma gvtypeP x ty :
  gvtype x = ok ty →
  [/\ ty = vtype (gv x)
    , valid_scs (sc_gvar_init x)
    & sem_scs (sc_gvar_init x) → ∃ v : sem_t ty, get_gvar true gd (evm s) x = ok (to_val v)].
Proof.
  rewrite /gvtype /sc_gvar_init /get_gvar; t_xrbindP => + <-.
  case: is_lvar => [_ | /= hget].
  + have [??] := vtypeP (gv x); split => //.
  split => // _.
  case heq: get_global hget => [v| //] _.
  rewrite -(type_of_get_global heq).
  have [v' -> ] := is_def_type_of (get_global_defined heq).
  rewrite type_of_to_val; eauto.
Qed.

Lemma  gvar_init_arr x len :
  vtype (gv x) = sarr len ->
  sem_scs (sc_gvar_init x).
Proof. by move=> h; rewrite /sc_gvar_init /sc_var_init h; case: ifP. Qed.

Lemma sc_is_aligned_ifP (i : sem_t sint) al aa sz e :
  sem_pexpr true gd s e = ok (to_val i) ->
  sem_scs (sc_is_aligned_if al aa sz e) ->
  is_aligned_if (Pointer := WArray.PointerZ) al (i * mk_scale aa sz) sz.
Proof.
  rewrite /sc_is_aligned_if /is_aligned_if => hi.
  case: al => //=.
  case: aa => /=.
  + by rewrite Z.mul_1_r /sem_scs /= hi /= andbT /is_align => /Z.eqb_spec ->.
  by move=> _; apply WArray.is_align_scale.
Qed.

Lemma in_ziotaP i n m : reflect (n <= i < n + m)%Z (i \in ziota n m).
Proof.
  rewrite in_ziota.
  case: (ZleP n i) => /=.
  + case: (ZltP i (n + m)); constructor; Lia.lia.
  move=> ?; constructor; Lia.lia.
Qed.

Lemma sc_in_boundP len (i ilen : sem_t sint) aa sz (elen e : pexpr) :
  sem_pexpr true gd s elen = ok (to_val ilen) ->
  sem_pexpr true gd s e = ok (to_val i) ->
  sem_scs (sc_in_bound (sarr len) aa sz elen e) ->
  (0 <= i * mk_scale aa sz /\ i * mk_scale aa sz + ilen <= len)%Z.
Proof.
  rewrite /sc_in_bound /sem_scs /= /emk_scale /emuli => helen he.
  case: aa => /=; rewrite helen he /= andbT => /andP [/ZleP h1 /ZleP h2]; Lia.lia.
Qed.

Lemma sc_in_boundP_all len (t : sem_t (sarr len)) (i : sem_t sint) aa sz e :
  sem_pexpr true gd s e = ok (to_val i) ->
  sem_scs (sc_in_bound (sarr len) aa sz (Pconst (wsize_size sz)) e) ->
  all (fun j => WArray.in_bound t (i * mk_scale aa sz + j)) (ziota 0 (wsize_size sz)).
Proof.
  move=> he hscs.
  have helen : sem_pexpr true gd s (Pconst (wsize_size sz)) = ok (to_val (t:=sint) (wsize_size sz)) by done.
  have [h1 h2] := sc_in_boundP helen he hscs.
  apply /allP => j /in_ziotaP ?; apply/WArray.in_boundP; Lia.lia.
Qed.

Axiom ziota_add : forall p n, ziota p n = map (fun j => p + j) (ziota 0 n).

(* FIXME : this require a check *)
Axiom get_global_arr_init :
   forall x len (t:WArray.array len) ,
   get_global gd x = ok (Varr t) →
   all (λ j : Z, WArray.is_init t j) (ziota 0 len).

Lemma sc_arr_initP len (t : sem_t (sarr len)) (i : sem_t sint) x aa sz e :
  sem_pexpr true gd s e = ok (to_val i) ->
  get_gvar true gd (evm s) x = ok (to_val t) ->
  sem_scs (sc_arr_init x aa sz e) ->
  all (fun j => WArray.in_bound t (i * mk_scale aa sz + j)) (ziota 0 (wsize_size sz)) ->
  all (fun j => WArray.is_init t (i * mk_scale aa sz + j)) (ziota 0 (wsize_size sz)).
Proof.
  rewrite /sc_arr_init /get_gvar /sem_scs /emk_scale /emuli /= => hi.
  case: ifP => /= hloc.
  + move=> -> /= + _.
    by case: aa => /=; rewrite hi /= andbT; set n := (x in ziota _ x);
      (have -> : n = wsize_size sz by rewrite /n; ring);
      rewrite ziota_add all_map; apply sub_all => j //; rewrite Z.mul_1_r.
  move=> /get_global_arr_init /allP hinit _ /allP hbound.
  apply/allP => j h; have /in_ziotaP ? := h.
  apply/hinit/in_ziotaP. have /WArray.in_boundP := hbound j h; Lia.lia.
Qed.

Axiom subtype_of_val :
  forall ty1 ty2 (v : sem_t ty2),
    subtype ty1 ty2 ->
    exists2 v', of_val ty1 (to_val v) = ok v' & value_uincl (to_val v') (to_val v).

Lemma sc_wi_rangeP (i : sem_t sint) sg sz e :
  sem_pexpr true gd s e = ok (to_val i) ->
  sem_scs [:: sc_wi_range sg sz e] ->
  wint_of_int sg sz (Vint i) = ok (wrepr sz i).
Proof.
  rewrite /sem_scs/sc_wi_range /= /wint_of_int.
  by case: sg => /= -> /=; rewrite andbT /in_sint_range /in_uint_range => ->.
Qed.

Lemma of_val_int i : of_val sint (Vint i) = ok i.
Proof. done. Qed.

Opaque of_val value_uincl subtype.

Lemma sc_divmodP_w ety1 ety2 e1 e2 sg (ve1 : sem_t ety1) (ve2 : sem_t ety2) w o:
  sem_pexpr true gd s e1 = ok (to_val ve1) ->
  sem_pexpr true gd s e2 = ok (to_val ve2) ->
  subtype (sword w) ety1 ->
  ∀ ve1' : word w,
  of_val (sword w) (to_val ve1) = ok ve1' ->
  value_uincl (Vword ve1') (to_val ve1) ->
  subtype (sword w) ety2 ->
  ∀ ve2' : word w,
  of_val (sword w) (to_val ve2) = ok ve2' ->
  value_uincl (Vword ve2') (to_val ve2) ->
  sem_scs (sc_divmod sg w (eint_of_word sg w e1) (eint_of_word sg w e2)) ->
  ∃ v : word w,
  Let r := mk_sem_divmod sg o ve1' ve2' in ok (Vword r) = ok (Vword v).
Proof.
  rewrite /sem_scs /sc_divmod /=.
  move=> he1 he2 /subtypeEl [sz1 [? hle1]]; subst ety1.
  move=> ve1' hof1 /value_uinclE [sz1'] [w1] [] /Vword_inj [?]; subst sz1' => /= ? hu1; subst w1.
  move=> /subtypeEl [sz2 [? hle2]]; subst ety2.
  move=> ve2' hof2 /value_uinclE [sz2'] [w2] [] /Vword_inj [?]; subst sz2' => /= ? hu2; subst w2.
  rewrite he2 /= /sem_sop1 /= hof2 /=.
  rewrite /mk_sem_divmod; case: sg => /=; last first.
  + rewrite andbT orbF => /ZeqbP => h.
    case: eqP => /= ?; last by eauto.
    by subst ve2'.
  rewrite he1 he2 /= /sem_sop1 /= hof1 hof2 /= andbT => /andP[]/ZeqbP h1 /andP h2.
  case: orP => /=; last by eauto.
  move=> [/eqP ? | /andP[] /eqP h3 /eqP h4].
  + by subst ve2'; elim h1; rewrite wsigned0.
  by subst ve2'; elim h2; rewrite h3 wsignedN1 !Z.eqb_refl.
Qed.

Lemma sc_divmodP_wi ety1 ety2 e1 e2 sg (ve1 : sem_t ety1) (ve2 : sem_t ety2) w o:
  sem_pexpr true gd s e1 = ok (to_val ve1) ->
  sem_pexpr true gd s e2 = ok (to_val ve2) ->
  subtype (sword w) ety1 ->
  ∀ ve1' : word w,
  of_val (sword w) (to_val ve1) = ok ve1' ->
  value_uincl (Vword ve1') (to_val ve1) ->
  subtype (sword w) ety2 ->
  ∀ ve2' : word w,
  of_val (sword w) (to_val ve2) = ok ve2' ->
  value_uincl (Vword ve2') (to_val ve2) ->
  sem_scs (sc_divmod sg w (eint_of_wint sg w e1) (eint_of_wint sg w e2)) ->
  ∃ v : word w,
  Let r := mk_sem_divmod sg o ve1' ve2' in ok (Vword r) = ok (Vword v).
Proof.
  rewrite /sem_scs /sc_divmod /=.
  move=> he1 he2 /subtypeEl [sz1 [? hle1]]; subst ety1.
  move=> ve1' hof1 /value_uinclE [sz1'] [w1] [] /Vword_inj [?]; subst sz1' => /= ? hu1; subst w1.
  move=> /subtypeEl [sz2 [? hle2]]; subst ety2.
  move=> ve2' hof2 /value_uinclE [sz2'] [w2] [] /Vword_inj [?]; subst sz2' => /= ? hu2; subst w2.
  rewrite he2 /= /sem_sop1 /= hof2 /=.
  rewrite /mk_sem_divmod; case: sg => /=; last first.
  + rewrite andbT orbF => /ZeqbP => h.
    case: eqP => /= ?; last by eauto.
    by subst ve2'.
  rewrite he1 he2 /= /sem_sop1 /= hof1 hof2 /= andbT => /andP[]/ZeqbP h1 /andP h2.
  case: orP => /=; last by eauto.
  move=> [/eqP ? | /andP[] /eqP h3 /eqP h4].
  + by subst ve2'; elim h1; rewrite wsigned0.
  by subst ve2'; elim h2; rewrite h3 wsignedN1 !Z.eqb_refl.
Qed.

Lemma sc_wi_range_op2P ety1 ety2 e1 e2  (ve1 : sem_t ety1) (ve2 : sem_t ety2) sg w o zo:
  (forall i1 i2, sem_sop2 o (Vint i1) (Vint i2) = ok (Vint (zo i1 i2))) →
  sem_pexpr true gd s e1 = ok (to_val ve1) →
  sem_pexpr true gd s e2 = ok (to_val ve2) →
  subtype (sword w) ety1 →
  ∀ ve1' : word w,
  of_val (sword w) (to_val ve1) = ok ve1' →
  value_uincl (Vword ve1') (to_val ve1) →
  subtype (sword w) ety2 →
  ∀ ve2' : word w,
  of_val (sword w) (to_val ve2) = ok ve2' →
  value_uincl (Vword ve2') (to_val ve2) →
  sem_scs [:: sc_wi_range_op2 sg w o e1 e2] →
  ∃ v : word w, Let r := mk_sem_wiop2 sg zo ve1' ve2' in ok (Vword r) = ok (Vword v).
Proof.
  rewrite /sc_wi_range_op2 /=.
  move=> ho he1 he2 /subtypeEl [sz1 [? hle1]]; subst ety1.
  move=> ve1' hof1 /value_uinclE [sz1'] [w1] [] /Vword_inj [?]; subst sz1' => /= ? hu1; subst w1.
  move=> /subtypeEl [sz2 [? hle2]]; subst ety2.
  move=> ve2' hof2 /value_uinclE [sz2'] [w2] [] /Vword_inj [?]; subst sz2' => /= ? hu2 h; subst w2.
  rewrite /mk_sem_wiop2  (sc_wi_rangeP _ h) /=; first by eauto.
  by rewrite he1 he2 /= /sem_sop1 /= hof1 hof2 /= ho.
Qed.


Lemma wmin_signed_neg ws : (wmin_signed ws < 0)%Z.
Proof. rewrite /wmin_signed; have := half_modulus_pos ws; Lia.lia. Qed.

Lemma wmax_signed_pos ws : (0 < wmax_signed ws)%Z.
Proof. by case: ws. Qed.

Lemma etypeP_aux : (forall e, P e) /\ (forall es, Q es).
Proof.
  apply: pexprs_ind_pair; subst P Q; split => //=; t_xrbindP => //.
  + by move=> _ <- _; constructor.
  + move=> e he es hes ? te /he{}he tes /hes {}hes <-.
    by rewrite sem_scs_cat => /andP[]/he{}he /hes{}hes; constructor.
  1-2: by move=> > <-; eauto.
  + by move=> len _ <-; exists (WArray.empty len).
  + by move=> x ty /gvtypeP[???].
  (* Array access *)
  + move=> al aa sz x e he ? tx /gvtypeP [htx' okx hx] te /he{}he /andP[]/is_sarrP [len htx] /eqP ? <-.
    subst tx te.
    rewrite /sc_arr_get !(sem_scs_cat, scs_err_cat) => /and4P [hsce hal hbound hinit].
    have /hx := gvar_init_arr htx.
    rewrite htx => -[t ht]; have [i hi] := he hsce.
    rewrite ht /= hi /= /WArray.get /read /=.
    have -> /= := sc_is_aligned_ifP hi hal.
    move: hbound; rewrite htx => /(sc_in_boundP_all t hi) hbound.
    have {}hinit := sc_arr_initP hi ht hinit hbound.
    have : exists l, mapM (λ k : Z, WArray.get8 t (add (i * mk_scale aa sz) k)) (ziota 0 (wsize_size sz)) = ok l;
     last first.
    + by move=> [l -> /=]; eauto.
    elim: (ziota 0 (wsize_size sz)) hbound hinit => //=; eauto.
    move=> j js hrec /andP [h1 h2] /andP [h3 h4].
    rewrite {2}/WArray.get8 WArray.addE h1 /= h3 /=.
    by have [l -> /=] := hrec h2 h4; eauto.

  (* Subarray access *)
  + move=> aa sz len' x e he ? tx /gvtypeP [htx' okx hx] te /he{}he /andP []/is_sarrP [len htx] /eqP ? <-.
    subst tx te.
    rewrite /sc_arr_get !(sem_scs_cat, scs_err_cat) => /andP [hsce hbound].
    have /hx := gvar_init_arr htx.
    rewrite htx => -[t ht]; have [i hi] := he hsce.
    rewrite ht /= hi /=.
    have helen : sem_pexpr true gd s (Pconst (arr_size sz len')) = ok (to_val (t:=sint) (arr_size sz len')) by done.
    move: hbound; rewrite htx => /(sc_in_boundP helen hi) []/ZleP h1 /ZleP h2.
    by rewrite /WArray.get_sub h1 h2 /=; eauto.

  (* Memory read *)
  + move=> al sz x e he ty te /he{}he /andP [hsubx hsube] <-.
    rewrite /sc_arr_get !(sem_scs_cat, scs_err_cat) => /and4P [hscx /he[ve{}he] hal hinit].
    have [_ /(_ hscx) [vx hvx]]:= vtypeP x.
    have [vx' hofx _]:= subtype_of_val vx hsubx.
    move/of_val_typeE: (hofx) => [wsx] [wx] [htox htrx].
    have [ve' hofe _]:= subtype_of_val ve hsube.
    move/of_val_typeE: (hofe) => [wse] [we] [htoe htre].
    rewrite hvx he /= htox htoe /= htrx htre /=.
    rewrite /read /=.
    have -> /= : is_aligned_if al (vx' + ve')%R sz.
    + move: hal; rewrite /sc_is_aligned_if_m /sem_scs; case: al => //=.
      rewrite /get_gvar /= hvx he /= /sem_sop2 /sem_sop1 /= hofx hofe /= of_val_to_val /= andbT => /ZeqbP h.
      by rewrite /is_align /= p_to_zE h.
    suff : [elaborate exists l, mapM (λ k : Z, get (emem s) (add (vx' + ve')%R k)) (ziota 0 (wsize_size sz)) = ok l].
    + by move=> [l -> /=]; eauto.
Opaque Z.sub.
    move: hinit; rewrite /sem_scs /=.
    rewrite /get_gvar /= hvx he /= /sem_sop2 /sem_sop1 /= hofx hofe /= truncate_word_u /=.
    rewrite !of_val_to_val /= of_val_to_val /= truncate_word_u /=.
    set wlo := (vx' + ve')%R; set n := wsize_size sz - 1.
    have ? : 0 <= n < wbase U8 by rewrite /n; case sz.
    have ? := wunsigned_range wlo.
    have ? : wbase U8 <= wbase Uptr by apply wbase_m.
    have hn : wunsigned (wrepr Uptr n) = n.
    + rewrite wunsigned_repr_small // /n.
      have := @le0_wsize_size sz.
      Lia.lia.
    set k := (k in ziota _ k).
    have -> : k = wsize_size sz.
    + by rewrite /k wunsigned_add_if; case: ZltP; rewrite hn => ?; case: ZleP => ?; Lia.lia.
    rewrite andbT => {k}.
    elim: ziota => [|k ks hrec] /=; first by eauto.
    by move=> /andP [] /is_okP [w ->] /hrec [l ->]; exists (w::l).
Transparent Z.sub.

  (* Unary operator *)
  + move=> op e he ty ety; case heq: type_of_op1 => [tin tout].
    move=> /he{}he; t_xrbindP => hsub <-.
    rewrite /sc_arr_get !(sem_scs_cat, scs_err_cat) => /andP [hsce hop].
    have [ve {}he /=] := he hsce; rewrite he /=.
    have [??]: tin = (type_of_op1 op).1 /\ tout = (type_of_op1 op).2 by rewrite heq.
    subst; rewrite /sem_sop1.
    have [ve' hve' huincl] := subtype_of_val ve hsub.
    rewrite hve' /= => {heq}.
    case: op hsub ve' hve' huincl hop => /=; try by eauto.
    + by move=> [] /=; eauto.
    move=> sg [] /=; try by eauto.
    + move=> sz /subtypeEl ?; subst ety.
      move=> ve' _ /= /value_uinclE [?] hscs; subst ve'.
      by rewrite (sc_wi_rangeP he hscs) /=; eauto.
    move=> sz /subtypeEl [sz' [? hle]]; subst ety.
    move=> ve' hof /= /value_uinclE [sz2] [w2] [] /Vword_inj [h]; subst sz2 => /= ? hu; subst w2.
    rewrite /sem_scs /=; case: sg => /=;
    rewrite he /= /sem_sop1 /= hof /= andbT /wint_of_int /= => /ZeqbP h.
    + rewrite /in_sint_range.
      suff : (wmin_signed sz <=? - wsigned ve') && (- wsigned ve' <=? wmax_signed sz).
      + by move=> -> /=; eauto.
      have := wsigned_range ve'; rewrite /wmin_signed /wmax_signed in h |- * => ?.
      by apply/andP; split;apply /ZleP; Lia.lia.
    by rewrite /in_uint_range h /=; eauto.

  (* Binary operator *)
  + move=> op e1 he1 e2 he2 ty ety1 /he1{}he1 ety2 /he2{}he2.
    case heq: type_of_op2 => [[tin1 tin2] tout].
    t_xrbindP => /andP[hsub1 hsub2] <-.
    rewrite /sc_arr_get !(sem_scs_cat, scs_err_cat) => /and3P [hsce1 hsce2 hop].
    have [ve1 {}he1 /=] := he1 hsce1; rewrite he1 /=.
    have [ve2 {}he2 /=] := he2 hsce2; rewrite he2 /=.
    have [???]: [/\ tin1 = (type_of_op2 op).1.1
                 , tin2 = (type_of_op2 op).1.2
                 & tout = (type_of_op2 op).2] by rewrite heq.
    subst; rewrite /sem_sop2.
    have [ve1' hve1' huincl1] := subtype_of_val ve1 hsub1.
    have [ve2' hve2' huincl2] := subtype_of_val ve2 hsub2.
    rewrite hve1' hve2' /= => {heq}.
    case: op hsub1 ve1' hve1' huincl1 hsub2 ve2' hve2' huincl2 hop => /=;
      try ((by eauto) || (by case => /=; eauto)).
    1-2: by move=> sg [] /=; first eauto;
         move=> w hsub1 ve1' hof1 hu1 hsub2 ve2'; apply: sc_divmodP_w; eauto.
    move=> sg w [] /=; rewrite /sem_wiop2_typed /=; try by eauto.
    1-3: by apply: sc_wi_range_op2P; eauto.
    1-2: by move=> hsub1 ve1' hof1 hu1 hsub2 ve2'; apply: sc_divmodP_wi; eauto.
    + move=> /subtypeEl [sz1 [? hle1]]; subst ety1.
      move=> ve1' hof1 /value_uinclE [sz1'] [w1] [] /Vword_inj [?]; subst sz1' => /= ? hu1; subst w1.
      move=> /subtypeEl [sz2 [? hle2]]; subst ety2.
      move=> ve2' hof2 /value_uinclE [sz2'] [w2] [] /Vword_inj [?]; subst sz2' => /= ? hu2 h; subst w2.
      rewrite /mk_sem_wishift (sc_wi_rangeP _ h) /=; first by eauto.
      by rewrite he1 he2 /= /sem_sop1 /= hof1 hof2 /= /sem_sop2 /= !of_val_int /=.
    move=> /subtypeEl [sz1 [? hle1]]; subst ety1.
    move=> ve1' hof1 /value_uinclE [sz1'] [w1] [] /Vword_inj [?]; subst sz1' => /= ? hu1; subst w1.
    move=> /subtypeEl [sz2 [? hle2]]; subst ety2.
    move=> ve2' hof2 /value_uinclE [sz2'] [w2] [] /Vword_inj [?]; subst sz2' => /= ? hu2 _; subst w2.
    rewrite /mk_sem_wishift /wint_of_int.
    have -> /=: in_wi_range sg w (zasr (int_of_word sg ve1') (int_of_word Unsigned ve2')) = ok tt; last eauto.
    rewrite /in_wi_range /in_sint_range /in_uint_range.
    have [??]:= wunsigned_range ve2'.
    case: sg => /=.
    + have -> // : (wmin_signed w <=? zasr (wsigned ve1') (wunsigned ve2')) &&
                   (zasr (wsigned ve1') (wunsigned ve2') <=? wmax_signed w).
      rewrite /zasr /zlsl.
      have [h1 h2] := wsigned_range ve1'.
      case: (wunsigned ve2' =P 0) => [-> /= | ?].
      + by rewrite Z.mul_1_r; apply/andP; split; apply/ZleP.
      have -> : (0 <=? -wunsigned ve2') = false.
      + by apply/negbTE/ZleP; Lia.lia.
      rewrite Z.opp_involutive.
      have ? := wmin_signed_neg w.
      have ? := wmax_signed_pos w.
      have ? : (0 < 2 ^ wunsigned ve2')%Z by Lia.nia.
      apply/andP;split;apply/ZleP.
      + apply Z.div_le_lower_bound => //; Lia.nia.
      by apply Z.div_le_upper_bound => //; Lia.nia.
    have -> // : (0 <=? zasr (wunsigned ve1') (wunsigned ve2')) &&
                 (zasr (wunsigned ve1') (wunsigned ve2') <=? wmax_unsigned w).
    rewrite /zasr /zlsl.
    have [h1 h2] := wunsigned_range ve1'.
    have ? : wmax_unsigned w = wbase w - 1 by done.
    case: (wunsigned ve2' =P 0) => [-> /= | ?].
    + rewrite Z.mul_1_r; apply/andP; split; apply/ZleP; Lia.lia.
    have -> : (0 <=? -wunsigned ve2') = false.
    + by apply/negbTE/ZleP; Lia.lia.
    rewrite Z.opp_involutive.
    have ? : 1 <= wmax_unsigned w.
    + by case w.
    have ? : (0 < 2 ^ wunsigned ve2')%Z by Lia.nia.
    apply/andP;split;apply/ZleP.
    + apply Z.div_le_lower_bound => //; Lia.nia.
    by apply Z.div_le_upper_bound => //; Lia.nia.

  (* N-anry opertors *)
  + move=> op es hes ty tys.
    case heq : type_of_opN => [tins tout]; t_xrbindP.
    move=> /hes{}hes hsubs <- /hes{}hes.
    have [??] : tins = (type_of_opN op).1 /\ tout = (type_of_opN op).2.
    + by rewrite heq.
    subst tins tout => {heq ty}.
    rewrite /sem_opN /sem_opN_typed.
    have := [elaborate sem_prod_ok_ok (sem_opN_typed_aux op)].
    move: (type_of_opN op) tys es (sem_prod_ok _ (sem_opN_typed_aux op)) hes hsubs.
    case => + tout /=.
    elim => [| tin tins hrec] [|ty tys] //= [|e es] o /List_Forall2_inv //=.
    + by move=> _ _ [? ->] /=; eauto.
    move=> [] [v hv] hall /andP [hsub hsubs] hok.
    rewrite hv /=.
    have [v' hv' _]:= subtype_of_val v hsub.
    have [r]:= hrec _ _ (o v') hall hsubs (hok v').
    t_xrbindP => vs -> r' happ _ /=.
    rewrite hv' /= happ /=; eauto.

  (* Conditional expression *)
  move=> t e he e1 he1 e2 he2 ty te /he{}he te1 /he1{}he1 te2 /he2{}he2.
  move=> /and3P[] /subtypeEl ? hsub1 hsub2 ?; subst te t.
  rewrite /sc_arr_get !(sem_scs_cat, scs_err_cat) => /and3P[].
  move=> {}/he [ve ->] /= {}/he1 [v1 ->] /= {}/he2 [v2 ->] /=.
  rewrite /truncate_val.
  have [v1' -> _]:= subtype_of_val v1 hsub1.
  have [v2' -> _ /=]:= subtype_of_val v2 hsub2.
  case: ve; eauto.
Qed.

Lemma etypeP : forall e, P e.
Proof. by case etypeP_aux. Qed.

Let Pv e :=
  forall ty, etype e = ok ty ->
  let sc := sc_e e in
  valid_scs sc.

Let Qv es :=
  forall tys, mapM etype es = ok tys ->
  let sc := flatten (map sc_e es) in
  valid_scs sc.

Lemma sc_wi_rangeP_safe sg sz e (ve : sem_t sint) :
  sem_pexpr true gd s e = ok (to_val ve) ->
  is_ok (sem_sc_err (sc_wi_range sg sz e)).
Proof.
  by move=> he; rewrite /sc_wi_range /sc_uint_range /sc_sint_range; case: sg => /=; rewrite he.
Qed.

Lemma etypePv_aux : (forall e, Pv e) /\ (forall es, Qv es).
Proof.
  apply: pexprs_ind_pair; subst Pv Qv; split => //=; t_xrbindP => //.
  + by move=> e he es hes ? te {}/he he tes {}/hes/=hes _; apply valid_scs_cat.
  + by move=> x ty /= /gvtypeP[???].
  (* Array access *)
  + move=> al aa sz x e he ty tx /gvtypeP [htx' okx hx] te hte.
    have {}he := he _ hte.
    move=> /andP[]/is_sarrP [len htx] /subtypeEl ??; subst tx te ty.
    apply valid_scs_cat => // {}he.
    have [? {}he /=] := etypeP hte he.
    rewrite /sc_arr_get; apply valid_scs_cat'; last apply valid_scs_cat'.
    + rewrite /sc_is_aligned_if; case: ifP => _ //=; split => //.
      by rewrite he.
    + rewrite /sc_in_bound htx /sc_le /emk_scale /emuli /eaddi /ezero /=.
      by case: ifP => _ /=; rewrite he /= /sem_sop2 /= !of_val_to_val /=.
    have /hx := gvar_init_arr htx.
    rewrite /get_gvar /sc_arr_init; case: ifP => //= _.
    rewrite htx => -[vx] ->; rewrite /emk_scale /emuli /eaddi /=.
    by case: ifP => //= _; rewrite he /sem_sop2 /= !of_val_to_val.

  (* Subarray access *)
  + move=> aa sz len' x e he ty tx /gvtypeP [htx' okx hx] te hte.
    have {}he := he _ hte.
    move=> /andP []/is_sarrP [len htx] /subtypeEl ??; subst tx te ty.
    apply valid_scs_cat => // {}he.
    have [? {}he /=] := etypeP hte he.
    by rewrite /sc_in_bound htx /sc_le /emk_scale /emuli /eaddi /=; case: ifP => _ /=;
       rewrite he /= /sem_sop2 /= !of_val_to_val.

  (* Memory read *)
  + move=> al sz x e he ty te hte /andP [hsubx hsube] ?; have {}he := he _ hte.
    have [hvx hx]:= vtypeP x.
    apply valid_scs_cat => // {}/hx [vx hx].
    have [vx' hofx _]:= subtype_of_val vx hsubx.
    move/of_val_typeE: (hofx) => [wsx] [wx] [htox htrx].
    apply valid_scs_cat => //.
    move=> /(etypeP hte) [ve {}he].
    have [ve' hofe _]:= subtype_of_val ve hsube.
    move/of_val_typeE: (hofe) => [wse] [we] [htoe htre].
    apply valid_scs_cat' => /=.
    + rewrite /sc_is_aligned_if_m; case: ifP => //= _.
      by rewrite /get_gvar /= hx he /= /sem_sop2 /sem_sop1 /= hofx hofe /= of_val_to_val /=.
    rewrite /get_gvar /= hx he /= /sem_sop2 /sem_sop1 /= hofx hofe /= truncate_word_u /=.
    by rewrite !of_val_to_val /= of_val_to_val /= truncate_word_u.

  (* Unary operator *)
  + move=> op e he ty ety; case heq: type_of_op1 => [tin tout].
    move=> hte; t_xrbindP => hsub ?; subst ty.
    have {}he := he _ hte; apply valid_scs_cat => // /(etypeP hte) [ve {}he].
    have [??]: tin = (type_of_op1 op).1 /\ tout = (type_of_op1 op).2 by rewrite heq.
    subst => {heq}.
    have [ve' hve' huincl] := subtype_of_val ve hsub.
    case: op hsub ve' hve' huincl => //=.
    move=> sg [] //=.
    + move=> sz /subtypeEl ?; subst ety.
      move=> ve' _ /= /value_uinclE [?]; subst ve'; split => //.
      by apply: sc_wi_rangeP_safe he.
    move=> sz /subtypeEl [sz' [? hle]]; subst ety.
    move=> ve' hof /= /value_uinclE [sz2] [w2] [] /Vword_inj [h]; subst sz2 => /= ? hu; subst w2.
    by case: sg => /=; rewrite he /= /sem_sop1 /= hof.

  (* Binary operator *)
  + move=> op e1 he1 e2 he2 ty ety1 hte1 ety2 hte2.
    case heq: type_of_op2 => [[tin1 tin2] tout].
    t_xrbindP => /andP[hsub1 hsub2] ?; subst ty.
    have [???]: [/\ tin1 = (type_of_op2 op).1.1
                 , tin2 = (type_of_op2 op).1.2
                 & tout = (type_of_op2 op).2] by rewrite heq.
    have {}he1 := he1 _ hte1; apply valid_scs_cat => // /(etypeP hte1) [ve1 {}he1].
    have {}he2 := he2 _ hte2; apply valid_scs_cat => // /(etypeP hte2) [ve2 {}he2].
    subst => {heq}.
    have [ve1' hve1' huincl1] := subtype_of_val ve1 hsub1.
    have [ve2' hve2' huincl2] := subtype_of_val ve2 hsub2.
    case: op hsub1 ve1' hve1' huincl1 hsub2 ve2' hve2' huincl2 => //=.
    1-2: by move=> sg [] //=;
         move=> w hsub1 ve1' hof1 hu1 hsub2 ve2' hof2 hu2; split;
         [ rewrite he2 /sem_sop1 /= hof2
         | move=> _; case: sg => //=; rewrite he1 he2 /sem_sop1 /= hof1 hof2].
    move=> sg sz [] //= hsub1 ve1' hof1 hu1 hsub2 ve2' hof2 hu2; split => //.
    1-3, 8: by apply: sc_wi_rangeP_safe; rewrite /= he1 he2 /sem_sop1 /sem_sop2 /= hof1 hof2 /= !of_val_to_val /=.
    1,3 : by rewrite he2 /sem_sop1 /= hof2.
    1,2: by move=> _; case: sg => //=;rewrite he1 he2 /sem_sop1 /= hof1 hof2 /=.
  + by move=> op es hes ty tys /hes.
  move=> ty e he e1 he1 e2 he2 ty' te /he{}he te1 /he1{}he1 te2 /he2{}he2 _ _.
  by apply valid_scs_cat' => //; apply valid_scs_cat'.
Qed. *)


(*
On rajoute les asserts de safety.
   c  : code d'origine
   cs : code avec condition de safety
La semantique log les conditions de safety.

on montre que si Final (fun r => sc r) (sem cs)
alors Final (fun r => Normal r) (sem c)


 *)
