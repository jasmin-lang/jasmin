(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Export psem.
Require Import expr compiler_util.

Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

Section PEXP_SC.
Context {pd: PointerData}.

(* Transforms an init_cond to an equivalent pexpr *)
Fixpoint ic_to_e vs ic: pexpr :=
  match ic with
  | IBool b => Pbool b
  | IConst c => Pconst c
  | IVar n => 
    match List.nth_error vs n with
    | Some x => x
    | None => Pbool false
    end
  | IOp1 op e1 => Papp1 op (ic_to_e vs e1)
  | IOp2 op e1 e2 => Papp2 op (ic_to_e vs e1) (ic_to_e vs e2)
  end.

Definition emin_signed sz := Pconst (wmin_signed sz).
Definition emax_signed sz := Pconst (wmax_signed sz).
Definition ezero := Pconst 0.
Definition emax_unsigned sz := Pconst (wmax_unsigned sz).

(* Definition eint_of_wint sg sz e := Papp1 (Owi1 sg (WIint_of_word sz)) e. *)

Definition eint_of_word (sg:signedness) sz e := Papp1 (Oint_of_word sz) e.

Definition emuli e1 e2 := Papp2 (Omul Op_int) e1 e2.
Definition eaddi e1 e2 := Papp2 (Oadd Op_int) e1 e2.

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
  | Pconst _ | Pbool _  | Parr_init _ | Parr_init_elem _ _ => [::]
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
  | Pis_var_init _ | Pis_arr_init _ _ _ | Pis_barr_init _ _ _ | Pis_mem_init _ _ => [::e]
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

Definition e_to_assert (e:pexpr) t : instr_r := Cassert t Cas e.

Definition instrr_to_instr (ii: instr_info) (ir: instr_r) : instr :=
  MkI ii ir.

Definition sc_e_to_instr (sc_e : pexprs) (ii : instr_info): seq instr :=
  map (fun e => instrr_to_instr ii (e_to_assert e Assert)) sc_e.

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
  | Cassert _ _ e => [::i]
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

Definition sc_prog (p:uprog) : uprog :=
  map_prog sc_func p.

End CMD_SC.

Section ETYPE.
Local Existing Instance nosubword.
