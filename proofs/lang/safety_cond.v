(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Export psem.
Require Import expr compiler_util safety_util.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

Section PEXP_SC.
Context {pd: PointerData}.


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

Definition sc_mem_valid (e: pexpr) sz := [:: Pis_mem_init e (wsize_size sz)].

Definition safe_cond_to_e vs sc: pexpr :=
  match sc with
  | NotZero ws k =>
      match List.nth_error vs k with
      | Some x => sc_neq x ezero 
      | None => Pbool true
      end
  | InRangeMod32 ws i j k =>
      match List.nth_error vs k with
      | Some x =>
         let e := emod x (Pconst 32) in
         let e1 := sc_lt (Pconst i) e in
         let e2 := sc_lt e (Pconst j) in
         eand e1 e2
      | None => Pbool true
      end
  | ULt ws k z =>
      match List.nth_error vs k with
      | Some x => sc_lt x (Pconst z)
      | None => Pbool true
      end
  | UGe ws z k =>
      match List.nth_error vs k with
      | Some x => sc_le (Pconst z) x
      | None => Pbool true
      end
  | UaddLe ws k1 k2 z =>
      match List.nth_error vs k1 with
      | Some x => 
          match List.nth_error vs k1 with
          | Some y => sc_le (eaddi x y) (Pconst z)
          | None => Pbool true
          end
      | None => Pbool true
      end
  | AllInit ws p k =>
      match List.nth_error vs k with
      | Some (Pvar x) => Pis_arr_init x.(gv) (Pconst 0) (Pconst (arr_size ws p)) 
      | _ => Pbool true
      end
  | X86Division sz sign =>
    match (List.firstn 3 vs),sign with
      | [:: hi; lo; dv],Signed =>
        sc_neq dv ezero 
       (*   
            let dd := wdwords hi lo in
            let dv := wsigned dv in
            let q  := (Z.quot dd dv)%Z in
            let r  := (Z.rem  dd dv)%Z in
            let ov := (q <? wmin_signed sz)%Z || (q >? wmax_signed sz)%Z in
            ~((dv == 0)%Z || ov)*)
      | [:: hi; lo; dv],Unsigned =>
        sc_neq dv ezero
               (*
        let dd := wdwordu hi lo in
        let dv := wunsigned dv in
        let q  := (dd  /  dv)%Z in
        let r  := (dd mod dv)%Z in
        let ov := (q >? wmax_unsigned sz)%Z in
        ~( (dv == 0)%Z || ov)
        *)
      | _,_ => Pbool true 
    end
  | ScFalse => Pbool false
  end.

Fixpoint sc_e (e : pexpr) : seq pexpr :=
  match e with
  | Pconst _ | Pbool _  | Parr_init _ => [::]
  | Parr_init_elem e _ => sc_e e
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
    let plo := eaddptr (Plvar x) e in
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
  | Pis_var_init _ => [::]
  | Pis_arr_init _ e1 e2 => sc_e e1 ++ sc_e e2
  | Pis_barr_init _ e1 e2 => sc_e e1 ++ sc_e e2
  | Pis_mem_init e1 e2 => sc_e e1 ++ sc_e e2
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

End PEXP_SC.

Section CMD_SC.
Context `{asmop:asmOp} {pd: PointerData} {pT: progT} {msfsz : MSFsize}.

Definition get_sopn_safe_conds (es: pexprs) (o: sopn) :=
  let instr_descr := get_instr_desc o in
  map (safe_cond_to_e es) instr_descr.(i_safe).

Fixpoint sc_instr (i : instr) : cmd :=
  let: (MkI ii ir) := i in
  match ir with
  | Cassgn lv _ _ e =>
    let sc_lv := sc_lval lv in
    let sc_e := sc_e e in
    sc_e_to_instr (sc_lv ++ sc_e) ii ++ [::i]
  | Copn lvs _ o es  =>
    let sc_lvs := conc_map sc_lval lvs in
    let sc_es := conc_map sc_e es in
    let sc_op := get_sopn_safe_conds es o in
    sc_e_to_instr (sc_lvs ++ sc_es ++ sc_op) ii ++ [::i]
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
  | Cassert _ _ e => [::i] (*patch*)
  end.

Definition sc_cmd (c : cmd) : cmd := conc_map sc_instr c.

Definition sc_func (f:ufundef): ufundef :=
  let sc_body := sc_cmd f.(f_body) in
  let es := conc_map (fun e => sc_var_init e) f.(f_res) in
  let sc_res := sc_e_to_instr es dummy_instr_info  in
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
  map_prog sc_func p.

End CMD_SC.

Section GLOB_DECLS.
Context {gd: glob_decls}.

Section ETYPE.
Local Existing Instance nosubword.
#[local] Existing Instance allow_init.
Context
  {asm_op syscall_state: Type}
  {ep: EstateParams syscall_state}
  {spp: SemPexprParams}
  (s: estate).

Definition gvtype (x:gvar) :=
  Let _ := assert (is_lvar x || is_ok (get_global gd (gv x))) tt in
  ok (vtype (gv x)).

Fixpoint etype (e : pexpr) : result unit stype :=
  match e with
  | Pconst _ => ok sint
  | Pbool _ => ok sbool
  | Parr_init len => ok (sarr len)
  | Parr_init_elem e len =>
    Let te := etype e in
    Let _ := assert (subtype (sword U8) te) tt in
    ok (sarr len)
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
    let (tins, tout) := type_of_opNA op in
    Let _ := assert (all2 subtype tins tes) tt in
    ok tout
  | Pif ty e e1 e2 =>
    Let te := etype e in
    Let te1 := etype e1 in
    Let te2 := etype e2 in
    Let _ := assert [&& subtype sbool te, subtype ty te1 & subtype ty te2] tt in
    ok ty
      
  | Pbig idx op x body start len =>
    Let tidx := etype idx in
    Let tbody := etype body in
    Let tstart := etype start in
    Let tlen := etype len in
    let: ((tin1, tin2), tout) := type_of_op2 op in
    Let _ := assert [&& subtype sint tstart, subtype sint tlen,
    subtype tin2 tbody, subtype tout tidx & subtype tin1 tout] tt in
    ok tout
                                                               
  | Pis_var_init x =>
     ok sbool
  | Pis_arr_init x e1 e2 =>
    Let te1 := etype e1 in
    Let te2 := etype e2 in
    ok sbool
  | Pis_barr_init x e1 e2 =>
    Let te1 := etype e1 in
    Let te2 := etype e2 in
    ok sbool
  | Pis_mem_init e1 e2 =>
    Let te1 := etype e1 in
    Let te2 := etype e2 in
    ok sbool
  end.

Definition sem_sc_err (sc : pexpr) :=
  match sc with
  | Pis_var_init x =>
    ok (is_defined (evm s).[x])
  | Pis_arr_init x lo len =>           
    Let (n, t) := true, s.[x] in
    Let lo := sem_pexpr true gd s lo >>= to_int in
    Let len := sem_pexpr true gd s len >>= to_int in
    ok (all (fun i => WArray.is_init t i) (ziota lo len ))
  | Pis_barr_init x lo len =>           
    Let (n, t) := true, s.[x] in
    Let lo := sem_pexpr true gd s lo >>= to_int in
    Let len := sem_pexpr true gd s len >>= to_int in
    ok (all (fun i => WArray.is_init t i) (ziota lo len))  
  | Pis_mem_init lo len =>
    Let wlo := sem_pexpr true gd s lo >>= to_word Uptr in
    Let ilen := sem_pexpr true gd s len >>= to_int in
    ok (all (fun i => is_ok (get (emem s) (wlo + wrepr Uptr i)%R)) (ziota 0 ilen))

  | _ => ok false
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

Fixpoint valid_scs (scs : seq pexpr) :=
  match scs with
  | [::] => True
  | sc :: scs => is_ok (sem_sc_err sc) /\ (sem_sc sc -> valid_scs scs)
  end.

(* ----- Scs management lemmas ----- *)
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

(* ----- Aux Lemmas ----- *)
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

Lemma gvar_init_arr x len :
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
  case: aa => //=.
  by move=> _; apply WArray.is_align_scale.
Qed.

Lemma sc_in_boundP len (i ilen : sem_t sint) aa sz (elen e : pexpr) :
  sem_pexpr true gd s elen = ok (to_val ilen) ->
  sem_pexpr true gd s e = ok (to_val i) ->
  sem_scs (sc_in_bound (sarr len) aa sz elen e) ->
  (0 <= i * mk_scale aa sz /\ i * mk_scale aa sz + ilen <= len)%Z.
Proof. by[]. Qed.

Lemma sc_in_boundP_all len (t : sem_t (sarr len)) (i : sem_t sint) aa sz e :
  sem_pexpr true gd s e = ok (to_val i) ->
  sem_scs (sc_in_bound (sarr len) aa sz (Pconst (wsize_size sz)) e) ->
  all (fun j => WArray.in_bound t (i * mk_scale aa sz + j)) (ziota 0 (wsize_size sz)).
Proof. by[]. Qed.

Axiom ziota_add : forall p n, ziota p n = map (fun j => p + j) (ziota 0 n).

(* FIXME : this require a check *)
Axiom get_global_arr_init :
   forall x len (t:WArray.array len) ,
   get_global gd x = ok (Varr t) →
   all (λ j : Z, WArray.is_init t j) (ziota 0 len).

Lemma in_ziotaP i n m : reflect (n <= i < n + m)%Z (i \in ziota n m).
Proof.
  rewrite in_ziota.
  case: (ZleP n i) => /=.
  + case: (ZltP i (n + m)); constructor; Lia.lia.
  move=> ?; constructor; Lia.lia.
Qed.

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
  move: ve1 ve2; case: ety1 ; case: ety2 => //=.
  move=> w1 w2 ve1 ve2 he1 he2 hle1 ve1' hof1 hu hle2 ve2' hof2 hu2.
  by rewrite /mk_sem_divmod; case: sg.
Qed.

(* Safety Lemma: pexpr *)
Let Pe e :=
  forall ty, etype e = ok ty ->
  let sc := sc_e e in
  (sem_scs sc -> exists (v:sem_t ty), sem_pexpr true gd s e = ok (to_val v)).

Let Qe es :=
  forall tys, mapM etype es = ok tys ->
  let sc := flatten (map sc_e es) in
  (sem_scs sc ->
   List.Forall2 (fun e ty => exists (v:sem_t ty), sem_pexpr true gd s e = ok (to_val v)) es tys).

Lemma etypeP_aux : (forall e, Pe e) /\ (forall es, Qe es).
Proof.
  apply: pexprs_ind_pair; subst Pe Qe; split => //=; t_xrbindP => //.
  + by move=> _ <- _; constructor.
  + move=> e he es hes ? te /he{}he tes /hes {}hes <-.
    by rewrite sem_scs_cat => /andP[]/he{}he /hes{}hes; constructor.
  1-2: by move=> z ? <- _; exists z.
  + by move=> len _ <-; exists (WArray.empty len).

  (* Parr_init_elem *)
  + move=> e n He ty te etyok sub <- semsce. admit.
    
  (* Gvar *)
  + by move=> x ty /gvtypeP[???].
    
  (* Array access *)
  + move=> al aa sz x e he sty tx /gvtypeP [htx' okx hx] te /he{}he /andP[]/is_sarrP [len htx] /eqP ? <-.
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
    have [ve' hofe _]:= subtype_of_val  ve hsube.
    move/of_val_typeE: (hofe) => [wse] [we] [htoe htre].
    rewrite hvx he /= htox htoe /= htrx htre /=.
    rewrite /read /=.
    have -> /= : is_aligned_if al (vx' + ve')%R sz.
    + move: hal; rewrite /sc_is_aligned_if_m /sem_scs; case: al => //=.
    suff : [elaborate exists l, mapM (λ k : Z, get (emem s) (add (vx' + ve')%R k)) (ziota 0 (wsize_size sz)) = ok l].
    + by move=> [l -> /=]; eauto.
    move: hinit; rewrite /sem_scs /=. admit.
    
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
    case => //=. move=> _ ve1' _ _ _ ve2' _ _ _. by exists (ve1' / ve2').
    move=> sg [] w hsub1 ve1' hof1 hu1 hsub2 ve2'; apply: sc_divmodP_w; eauto.
    case => //=. move=> _ ve1' _ _ _ ve2' _ _ _. by exists (ve1' mod ve2').
    move=> sg [] w hsub1 ve1' hof1 hu1 hsub2 ve2'; apply: sc_divmodP_w; eauto.
   
  (* N-ary opertors *)
  + admit.

  (* Conditional expression *)
 + move=> t e he e1 he1 e2 he2 ty te /he{}he te1 /he1{}he1 te2 /he2{}he2.
   move=> /and3P[] /eqP ? hsub1 hsub2 ? ; subst.
   rewrite /sc_arr_get !(sem_scs_cat, scs_err_cat) => /and3P[].
   move=> {}/he [ve ->] /= {}/he1 [v1 ->] /= {}/he2 [v2 ->] /=.
   rewrite /truncate_val.
   have [v1' -> _]:= subtype_of_val v1 hsub1.
   have [v2' -> _ /=]:= subtype_of_val v2 hsub2.
   by case: ve; eauto.

 (* Big expression *)
 + move=> e He op vi e1 He1 e2 He2 e3 He3 ty te /He{}He te1 /He1{}He1 te2 /He2{}He2 te3 /He3{}He3.
   case heq: type_of_op2 => [[tin1 tin2] tout]. t_xrbindP=> /andP[hsub1 hsub2] <-.
   rewrite /sc_arr_get !(sem_scs_cat, scs_err_cat) =>
     /and4P[] {}/He [semte ->] {}/He1 [semte1 h1] {}/He2 [semte2 ->] {}/He3 [semte3 ->] /=.
   admit.
 (* Init expressions *)
 (* Pis_var_init *)
 (* Pis_arr_init *)
 + admit.
  
 + admit.
 + admit.
Admitted.

Lemma etypeP : forall e, Pe e.
Proof. by case etypeP_aux. Qed.

Let Pev e :=
  forall ty, etype e = ok ty ->
  let sc := sc_e e in
  valid_scs sc.

Let Qev es :=
  forall tys, mapM etype es = ok tys ->
  let sc := flatten (map sc_e es) in
  valid_scs sc.

(* Validity Lemma: pexpr *)
Lemma etypePv_aux : (forall e, Pev e) /\ (forall es, Qev es).
Proof.
  apply: pexprs_ind_pair; subst Pev Qev; split => //=; t_xrbindP => //.

  (* z::z0 *)
  + by move=> e he es hes ? te {}/he he tes {}/hes/=hes _; apply valid_scs_cat.
  (* Parr_init_elem *)
  + by move=> e n H > /H{}H ?.
  (* Gvar *)
  + by move=> x ty /= /gvtypeP[???].

  (* Array access *)
  + move=> al aa sz x e he ty tx /gvtypeP [htx' okx hx] te hte.
    have {}he := he _ hte.
    move=> /andP[]/is_sarrP [len htx] /subtypeEl ??; subst tx te ty.
    apply valid_scs_cat => // {}he.
    have [? {}he /=] := etypeP hte he.
    rewrite /sc_arr_get; apply valid_scs_cat'; last apply valid_scs_cat'.
    + by rewrite /sc_is_aligned_if ; case: ifP.
    + by rewrite /sc_in_bound htx /sc_le /emk_scale /emuli /eaddi /ezero /=; split. 
    have /hx := gvar_init_arr htx.
    rewrite /get_gvar /sc_arr_init; case: ifP => //= _.
    rewrite htx => -[vx] ->; rewrite /emk_scale /emuli /eaddi /=.
    by case: ifP => //= _; rewrite he /sem_sop2 /=.
    
  (* Subarray access *)
  + move=> aa sz len' x e he ty tx /gvtypeP [htx' okx hx] te hte.
    have {}he := he _ hte.
    move=> /andP []/is_sarrP [len htx] /subtypeEl ??; subst tx te ty.
    apply valid_scs_cat => // {}he.
    have [? {}he /=] := etypeP hte he.
    by rewrite /sc_in_bound htx /sc_le /emk_scale /emuli /eaddi /=; split.
    
  (* Memory read *)
  + move=> al sz x e he ty te hte /andP [hsubx hsube] ?; have {}he := he _ hte.
    have [hvx hx]:= vtypeP x.
    apply valid_scs_cat => // {}/hx [vx hx].
    have [vx' hofx _]:= subtype_of_val vx hsubx.
    move/of_val_typeE: (hofx) => [wsx] [wx] [htox htrx].
    apply valid_scs_cat => //.
    move=> /(etypeP hte) [ve {}he].
    have [ve' hofe _]:= subtype_of_val ve hsube.
    move/of_val_typeE: (hofe) => [wse] [we] [htoe htre]. Print sc_mem_valid.
    apply valid_scs_cat'.
  - by rewrite /sc_is_aligned_if_m; case: ifP => //=.
    admit.
    
  (* Unary operator *)
  + move=> op e he ty ety; case heq: type_of_op1 => [tin tout].
    move=> hte; t_xrbindP => hsub ?; subst ty.
    by have {}he := he _ hte; apply valid_scs_cat => // /(etypeP hte) [ve {}he].
    
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
    by case. by case.
    
  (* N-ary opertors *)
  + by move=> op es hes ty tys /hes.

  (* Conditional expression *)
  move=> ty e he e1 he1 e2 he2 ty' te /he{}he te1 /he1{}he1 te2 /he2{}he2 _ _.
  by apply valid_scs_cat' => //; apply valid_scs_cat'.

  (* Big expression *)
 + move=> e he op vi e1 he1 e2 he2 e3 he3 ty te /he{}he te1 /he1{}he1 te2 /he2{}he2 te3 /he3{}he3.
   case heq: type_of_op2 => [[tin1 tin2] tout]. t_xrbindP=> /andP[sub1 sub2 touteq].
   by repeat apply valid_scs_cat'.
  
  (* Init expressions *)
 + move=> vi e1 e2 he1 he2 ty te /he1{}he1 te2 /he2{}he2 _. admit.
 + admit.
 + admit.    
Admitted.

Definition ltype (l : lval) : result unit stype := (*TODO: Re-check this with Pl proof*)
  match l with
  | Lnone vinf sty => ok sty
  | Lvar vi => ok (vtype vi)
  | Lmem al ws x e =>
     let tx := vtype x in
     Let te := etype e in
     Let _ := assert [&& subtype (sword Uptr) tx & subtype (sword Uptr) te] tt in
     ok (sword ws)
  | Laset al aa ws x e =>
    let tx := vtype x in
    Let te := etype e in
    Let _ := assert [&& is_sarr tx & subtype sint te] tt in
    ok (sword ws)
  | Lasub aa ws len x e =>
    let tx := vtype x in
    Let te := etype e in
    Let _ := assert [&& is_sarr tx & subtype sint te] tt in
    ok (sarr (Z.to_pos (arr_size ws len)))
  end.
Definition ltypes := mapM ltype.

Lemma DB_to_val ty (v : sem_t ty) wdb : DB wdb (to_val v).
Proof. by case: ty v; rewrite /DB /= orbT. Qed.

Lemma compat_val_to_val ty (v : sem_t ty) : compat_val ty (to_val v).
Proof. by case: ty v => *; rewrite /compat_val /= eq_refl. Qed.

Let Pl l :=
  forall ty, ltype l = ok ty ->
  let: sc := sc_lval l in
  (sem_scs sc ->
   forall (v:sem_t ty), exists (s':estate), write_lval true gd l (to_val v) s = ok s').

Lemma ltypePl : forall l, Pl l.
Proof.
  subst Pl => /=.
  move=> [vi tynone ty | x ty | al ws x e ty | al aa ws x e ty | aa ws pos x e ty] /=.
  + (* Lnone *)
    move=> [->] _ v; exists s.
    by rewrite /write_none DB_to_val /= compat_val_truncatable // compat_val_to_val.
  + (* Lvar *)
    move=> [<-] _ v; rewrite /write_var /set_var DB_to_val /= compat_val_truncatable.
    by exists (with_vm s (evm s).[x <- to_val (t:=vtype x) v]).
    by apply compat_val_to_val.
  + (* Lmem *)
    t_xrbindP => z etyok /andP[sub1 sub2] <-. repeat rewrite sem_scs_cat.
    move=> /andP[varinit /andP[sce /andP[isalign memval]]] semt.
    rewrite /write. rewrite /get_var. exists s. admit.
  + (* Laset *)
    t_xrbindP => z etyok /andP[isarr sub2] <-.
    rewrite sem_scs_cat => /andP[semsce]. rewrite /sc_arr_set.
    rewrite /on_arr_var /get_var. exists s. move=> //=.
    admit.
  + (* Lasub *)
    admit.
Admitted.

Let Plv l :=
  forall ty, ltype l = ok ty ->
  let sc := sc_lval l in
  valid_scs sc.

Lemma ltypePlv : forall l, Plv l.
Proof.
  rewrite /Plv /ltype => l ty H.
  case l as [vinf sty | vi | al ws x e | al aa ws x e | aa ws len x e] eqn:leq => //.
  move: H. t_xrbindP.
  (*Lmem*)
  have [hvx hx]:= vtypeP x.
  move=> ty2 etyok /andP[sub1 sub2] wordty.
Admitted.

End ETYPE.

Section CTYPE.
Local Existing Instance nosubword.
#[local] Existing Instance allow_init.
Context
  `{asmop:asmOp}
  {syscall_state: Type}
  {ep: EstateParams syscall_state}
  {spp: SemPexprParams}
  (s: estate).
  
Section ctype_aux.
Variable itype : instr -> result unit unit.
Fixpoint ctype_aux (c : cmd) : result unit unit :=
  match c with
  | [::] => ok tt
  | i :: cs =>
    Let _ := itype i in
    Let _ := ctype_aux cs in
    ok tt
  end.
End ctype_aux.

Fixpoint itype (i : instr) : result unit unit :=
  match i with
  | MkI ii ir => irtype ir
  end
with irtype (ir : instr_r) : result unit unit :=
  match ir with
  | Cassgn x tag ty e =>
      Let tx := ltype x in
      Let t := etype e in
      Let _ := assert (subtype ty t) tt in
      Let _ := assert (subtype tx ty) tt in
      ok tt
  | Copn xs t op es =>
      Let _ := ltypes xs in (* lvals compatible with the return type of op *)
      Let _ := mapM etype es in
      Error tt (* Never safe *)
  | Csyscall xs o es =>
      Let _ := ltypes xs in
      Let _ := mapM etype es in
      Error tt (* Never safe *)
  | Cif e c1 c2 =>
      Let t := etype e in
      Let _ := assert (is_sbool t) tt in
      Let _ := ctype_aux itype c1 in
      Let _ := ctype_aux itype c2 in            
      ok tt
  | Cfor i (d, lo, hi) c =>
      let _ := vtype i in
      Let _ := etype lo in
      Let _ := etype hi in
      Let _ := ctype_aux itype c in
      ok tt
  | Cwhile a c e ei c' => (* non termination? *)
      Let t := etype e in
      Let _ := assert (is_sbool t) tt in
      Let _ := ctype_aux itype c in
      Let _ := ctype_aux itype c' in
      ok tt
  | Ccall xs fn es => (* TODO: check that fn is safe *)
      Let _ := ltypes xs in
      Let _ := mapM etype es in
      Error tt (* until we check that fn is safe *)
  | Cassert ak ap e =>
      Let _ := etype e in
      ok tt
  end.

(* Auxiliary Lemmas
 --------------------------- *)
Lemma ctype_aux_inversion i c :
  ctype_aux itype (i :: c) = ok tt ->
  itype i = ok tt
  /\ ctype_aux itype c = ok tt.
Proof.
  move=> //= H.
  case: (itype i) H => [Hi|] H; [|discriminate].
  case: (ctype_aux itype c) H => [Hc|] H; [|discriminate].
  split.
  move: H; case: Hi; by [].
  move: H; case: Hc; by [].
Qed.

(* ----------- Instruction Validation ----------- *)

(*
Let Piv i :=
  itype i = ok tt ->
  let sc := sc_instr i in
  valid_scs sc.

Let Pcv c :=
  ctype c = ok tt ->
  let sc := sc_c c in
  valid_scs sc.


Lemma Pmkv ir ii: Prv ir -> Piv (MkI ii ir).
Proof.
  by move=> HPr.
Qed.

Lemma Pnilv : Pcv [::].
Proof.
  by [].
Qed.

Lemma Pconsv i c:  Piv i -> Pcv c -> Pcv (i::c).
Proof.
  rewrite /Pcv /Piv /ctype => Hiv Hcv Hok.
  have aux := ctype_aux_inversion Hok.
  case: aux => Hi Hc. move: (Hiv Hi) (Hcv Hc).
  apply valid_scs_cat'.
Qed.

Lemma Pasgnv l tag ty e : Prv (Cassgn l tag ty e).
Proof.
  subst Prv; rewrite /irtype.
  case (etype e) as [ety|] eqn: eok;
  case (ltype l) as [lty|] eqn: lok =>//=.
  have Hev := etypePv eok. have Hlv := ltypePlv lok.
  by move=> _; apply valid_scs_cat.
Qed.

Lemma Popnv xs t o es: Prv (Copn xs t o es).
Proof.
  by rewrite /irtype.
Qed.

Lemma Psyscallv xs o es: Prv (Csyscall xs o es).
Proof.
  by rewrite /irtype.
Qed.

Lemma Pifv e c1 c2: Pcv c1 -> Pcv c2 -> Prv (Cif e c1 c2).
Proof.
  rewrite /Pcv /Prv /ctype /irtype => Hc1 Hc2.
  case (etype e) as [ety|] eqn: eok =>//=;
  case ety eqn:eeq;
  case (ctype_aux itype c1) as [c1ty|] eqn:c1ok =>//=;
  case (ctype_aux itype c2) as [c2ty|] eqn:c2ok =>//=;
  try case c1ty eqn:c1eq; try case c2ty eqn:c2eq.
  have Hev := etypePv eok.
  move: (Hc1 Logic.eq_refl) (Hc2 Logic.eq_refl) => H1 H2.  
  by repeat (move=> _; apply valid_scs_cat).
  by rewrite c1ok c2ok.
  by rewrite c1ok.
  by rewrite c1ok.
Qed.

Lemma Pforv v dir lo hi c: Pcv c -> Prv (Cfor v (dir,lo,hi) c).
Proof.
  rewrite /Pcv /Prv /ctype /irtype => Hc.
  case (etype lo) as [loty|] eqn: look;
  case (etype hi) as [hity|] eqn: hiok;
  case (ctype_aux itype c) as [cty|] eqn:cok =>//=;
  try case cty eqn:ceq.
  have [hvx hx]:= vtypeP v;
  have Hlov := etypePv look; have Hhiv := etypePv hiok.
  move: (Hc Logic.eq_refl) => H.
  by repeat (move=> _; apply valid_scs_cat).
  by rewrite cok.
Qed.

Lemma Pwhilev a c e ei c': Pcv c -> Pcv c' -> Prv (Cwhile a c e ei c').
Proof.
  rewrite /Pcv /Prv /ctype /irtype =>  Hc Hc'.
  case (etype e) as [ety|] eqn: eok =>//=; case ety eqn:eeq;
  case (ctype_aux itype c) as [cty|] eqn:cok =>//=;
  case (ctype_aux itype c') as [c'ty|] eqn:c'ok =>//=;
  try case cty eqn:ceq; try case c'ty eqn:c'eq.
  have Hev:= etypePv eok.
  move: (Hc Logic.eq_refl) (Hc' Logic.eq_refl) => H1 H2.
  by repeat (move=> _; apply valid_scs_cat =>//=).
  by rewrite cok c'ok.
  by rewrite cok.
  by rewrite cok.
Qed.

Lemma Pcallv xs f es: Prv (Ccall xs f es).
Proof.
  rewrite /Prv /irtype.
  by case (mapM etype es) as [esty|] eqn: estyok;
  case (ltypes xs) as [lsty|] eqn: lstyok.
Qed.


(* ----------- Instruction Safety ----------- *)
Context
  {sCP: semCallParams}.
Variable ev : extra_val_t.

Let Pr ir :=
      forall ii, Pi (MkI ii ir).
   
Let Pi i :=
      itype i = ok tt ->
      let sc := sc_instr i in
      (sem_scs sc -> forall s, exists s', sem_I prog ev s i s').

Let Pc c :=
      ctype c = ok tt ->
      let sc := sc_c c in
      (sem_scs sc -> forall s, exists s', sem prog ev s c s').

Lemma Pmk ir ii: Pr ir -> Pi (MkI ii ir).
Proof.
  rewrite /Pr /Pi; move=> HPr Hitype s1 Hsemscs;
  specialize (HPr Hitype s1 Hsemscs) as [s2 Hs'];
  exists s2; by apply: EmkI.
Qed.

Lemma Pnil : Pc [::].
Proof.
  rewrite /Pc => Hctype Hsc s1; exists s1; by apply Eskip.
  Qed.

Lemma Pcons i c:  Pi i -> Pc c -> Pc (i::c).
Proof.
  rewrite /Pi /Pc. clear Pr Pi Pc. move=> HPi HPc Hctype Hsemscs s1.
  move: Hsemscs Hctype. rewrite /ctype.
  rewrite sem_scs_cat. move/andP => [Hsemsci Hsemscc].
  pose proof ctype_aux_inversion as aux. specialize (aux i c).
  move=> /aux [Hityok Hctyok].
  specialize (HPi Hityok Hsemsci s1) as [s2 H1].
  specialize (HPc Hctyok Hsemscc s2) as [s3 H2].
  exists s3. move: H1 H2; apply Eseq.
Qed.  
  
Lemma Pasgn l tag ty e: Pr (Cassgn l tag ty e).
Proof.
  rewrite /Pr. clear Pr Pi Pc.
  case (etype e) as [ety|] eqn:Hetyok.
  case: (ltype l) => [lty|] //=.
  case (assert (subtype ety ty) tt) => [asser|] //=. move=>_ {asser}.
  case (sc_l l). rewrite cat0s => H2.
  move=> s1. pose proof etypeP as HPaux.
  specialize (HPaux e ety Hetyok H2) as [semt_esty Hsem1].
  
  (* Should be able to solve like this:
  Exists (write_lval true gd lv v' s0). apply sem_Ind_mkI. sem_Ind_assgn.
  apply Eassgn. *)
Admitted.
  
Lemma Popn xs t o es: Pr (Copn xs t o es).
Proof.
  by subst Pr; rewrite /irtype;
  case (ltypes xs) as [lty|] eqn:ltyok;
  case (mapM etype es) as [esty|] eqn:estyok;
  try case lty eqn:ltyeq =>//=;
  try case esty eqn:esyeq =>//=.
Qed.

Lemma Psyscall xs o es: Pr (Csyscall xs o es).
Proof.
  by subst Pr; rewrite /irtype;
  case (ltypes xs) as [lty|] eqn:ltyok;
  case (mapM etype es) as [esty|] eqn:estyok;
  try case lty eqn:ltyeq =>//=;
  try case esty eqn:esyeq =>//=.
Qed.

Lemma Pif e c1 c2: Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
Proof.
  rewrite /Pc /Pr /ctype /sc_c. clear Pr Pi Pc.

  (* Induction on e. This line could be done later *)
  case (etype e) as [ety|] eqn:Hetyok => //=.

  (* Destruct H2 first *)
  move=> HPc1 HPc2 H1 + s1. (**)
  rewrite !sem_scs_cat;
  move/andP => [Hsemsce Hsem_aux];
               move/andP: Hsem_aux => [Hsemsc1 Hsemsc2].
  (* Use it on H1 *)
  move: H1. rewrite /assert; rewrite /is_sbool.
  rewrite Hetyok => //=.
  case ety eqn:etyeq => //=; rewrite <- etyeq in Hetyok.
  
  (* Getting Paux *)
  pose proof etypeP as HPaux.
  specialize (HPaux e ety Hetyok Hsemsce) as [v HPaux].
  
  (* TRYING: c1 *)
  case (ctype_aux itype c1) as [c1ty|] eqn:Hc1tyok.
  case c1ty eqn:c1tyis. subst (* Careful *).
  have okttrefl : ok tt = ok tt by [reflexivity]; specialize (okttrefl unit) (* Weird *). 
  specialize (HPc1 okttrefl Hsemsc1 s1) as [s2 HPc1].
  move=> _; exists s2.

  (* Final step of C1 *)
  move: HPaux HPc1.
  move: v; rewrite /sem_t => //=. move=> v; case: v.
  (* FAILS: gd and s are not the same. s should be s1.*)
  (* p_globs function to fix gd? *)

  (* TRYING: c2 *) (* TODO *)
  case (ctype_aux itype c2) as [c2ty|] eqn:Hc2tyok.
  case c2ty eqn:c2tyis; subst.  
Admitted.

Lemma Pfor v dir lo hi c: Pc c -> Pr (Cfor v (dir,lo,hi) c).
Proof.
Admitted.

Lemma Pwhile a c e ei c': Pc c -> Pc c' -> Pr (Cwhile a c e ei c').
Proof.
Admitted.

Lemma Pcall xs f es: Pr (Ccall xs f es).
Proof.
Admitted.

 *)
End CTYPE.
End GLOB_DECLS.
