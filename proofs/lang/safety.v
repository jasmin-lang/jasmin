From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Export compiler_util safety_shared. 
Require Import psem.

Section SAFETY.
Context `{asmop:asmOp} {pd: PointerData} {msfsz : MSFsize}.

Definition sc_var (x:var_i) :=
  if is_sarr (vtype x) then [::]
  else [:: Pis_var_init x].

Definition sc_gvar x :=
  if is_lvar x then sc_var (gv x)
  else [::].

Definition sc_is_aligned_if al aa sz e :=
  if (al == Unaligned) || (aa == AAscale) then [::]
  else [:: eis_aligned e sz].

Definition sc_in_bound ty aa sz e elen :=
  match ty with
  | sarr len =>
    let i := emk_scale aa sz e in
    [:: eand (elei ezero i) (elei (eaddi i elen) (Pconst len))]
  | _ => [::]
  end.

Definition sc_arr_init (x:gvar) aa sz e :=
  if is_lvar x then
    let lo := emk_scale aa sz e in
   [:: Pis_arr_init x.(gv) lo (Pconst (wsize_size sz))]
  else [::].

Definition sc_arr_get (x:gvar) al aa sz e :=
  sc_is_aligned_if al aa sz e ++
  sc_in_bound (vtype (gv x)) aa sz e (Pconst (wsize_size sz)) ++
  sc_arr_init x aa sz e.

Definition sc_mem_valid (e: pexpr) sz := [:: Pis_mem_init e (wsize_size sz)].

(* Req: Pointer Data*)
Definition eint_of_word (sg:signedness) sz e := Papp1 (Oint_of_word sg sz) e.

Definition sc_is_aligned_if_m al sz e :=
  if (al == Unaligned) then [::]
  else
  [:: eis_aligned (eint_of_word Unsigned Uptr e) sz].
(* Req: Pointer Data*)

Definition sc_in_bound' ty e1 e2 :=
  match ty with
  | sarr len =>
    [:: eand (elei ezero e1) (elei (eaddi e1 e2) (Pconst len))]
  | _ => [::]
  end.

Definition sc_barr_init (x: var_i) e1 e2 := [:: Pis_arr_init x e1 e2].           

Definition sc_barr_get (x:var_i) e1 e2 :=
  sc_in_bound' (vtype x) e1 e2 ++
  sc_barr_init x e1 e2.

Definition sc_op2_safe (o : sop2) :=
  match o with
  | Odiv sg (Op_w sz) => false
  | Omod sg (Op_w sz) => false
  | Owi2 _ _ o' =>
      match o' with
      | WIadd | WImul | WIsub | WIdiv | WImod
      | WIshl => false
      | WIshr | WIeq | WIneq | WIlt | WIle
      | WIgt | WIge => true
      end
  | _ => true (*TODO: add all the pattern*)
  end.

Definition sc_pexprs (sc_pexpr: pexpr -> safety_cond) (es:pexprs) : safety_cond :=
  flatten (map sc_pexpr es).

Fixpoint sc_pexpr (e : pexpr) : safety_cond :=
  match e with
  | Pconst _ | Pbool _  | Parr_init _ => [::]
  | Pvar x => sc_gvar x

  | Pget al aa ws x e =>
    let sc_e := sc_pexpr e in
    let sc_arr := sc_arr_get x al aa ws e in
    sc_e ++ sc_arr

  | Psub aa ws len x e =>
    let sc_e := sc_pexpr e in
    let sc_arr := sc_in_bound (vtype (gv x)) aa ws e (Pconst (arr_size ws len)) in
    sc_e ++ sc_arr

  | Pload al ws e =>
    let sc_e := sc_pexpr e in
    let sc_al := sc_is_aligned_if_m al ws e in
    let sc_load := sc_mem_valid e ws in
    sc_e ++ sc_al ++ sc_load

  | Papp1 op e =>
    let sc_e := sc_pexpr e in
    let sc_op := sc_op1 op e in
    sc_e ++ sc_op

  | Papp2 op e1 e2 =>
    let sce1 := sc_pexpr e1 in
    let sce2 := sc_pexpr e2 in
    let sco := sc_op2 op e1 e2 in
    sce1 ++ sce2 ++ sco

  | PappN op es =>
    let scs := sc_pexprs sc_pexpr es in
    scs

  | Pif ty e e1 e2 =>
    let sc_e := sc_pexpr e in
    let sc_e1 := sc_pexpr e1 in
    let sc_e2 := sc_pexpr e2 in
    sc_e ++ sc_e1 ++ sc_e2

  | Pbig idx op x body start len  =>
    let scidx := sc_pexpr idx in
    let scstart := sc_pexpr start in
    let sclen := sc_pexpr len in
    let scbody := sc_pexpr body in
    let scbody := Pbig true Oand x (eands scbody) start len in
    let scop := Pbool (sc_op2_safe op) in
    scstart ++ sclen ++ scidx ++ [:: scop ; scbody]

  | Parr_init_elem e _ => sc_pexpr e

  | Pis_var_init x => [::]

  | Pis_arr_init x e1 e2 =>
    let sc_e1 := sc_pexpr e1 in
    let sc_e2 := sc_pexpr e2 in
    sc_e1 ++ sc_e2
                                    
  | Pis_barr_init x e1 e2 =>
    let sc_barr := sc_barr_get x e1 e2 in
    let sc_e1 := sc_pexpr e1 in
    let sc_e2 := sc_pexpr e2 in
    sc_e1 ++ sc_e2 ++ sc_barr
      
  | Pis_mem_init e1 e2 =>
    let sc_e1 := sc_pexpr e1 in
    let sc_e2 := sc_pexpr e2 in
    sc_e1 ++ sc_e2
  end.

Definition sc_arr_set (x:var_i) al aa sz e :=
  sc_is_aligned_if al aa sz e ++
  sc_in_bound (vtype x) aa sz e (Pconst (wsize_size sz)).

Definition sc_lval (lv : lval) : safety_cond :=
  match lv with
  | Lnone _ _ => [::]
  | Lvar x => [::]
  | Lmem al ws x e =>
    let sc_e := sc_pexpr e in
    let sc_al := sc_is_aligned_if_m al ws e in
    let sc_load := sc_mem_valid e ws in
    sc_e ++ sc_al ++ sc_load
  | Laset al aa ws x e =>
    let sc_e := sc_pexpr e in
    let sc_arr := sc_arr_set x al aa ws e in
    sc_e ++ sc_arr
  | Lasub aa ws len x e =>
    let sc_e := sc_pexpr e in
    let sc_arr := sc_in_bound (vtype x) aa ws e (Pconst (arr_size ws len)) in
    sc_e ++ sc_arr
  end.

Definition sc_lvals (lvs:lvals) : safety_cond := flatten (map sc_lval lvs).

Definition safe_cond_to_e vs sc: pexpr :=
  match sc with
  | NotZero ws k =>
      match List.nth_error vs k with
      | Some x => eneqi x ezero 
      | None => Pbool true
      end
  | InRangeMod32 ws i j k =>
      match List.nth_error vs k with
      | Some x =>
         let e := emodi x (Pconst 32) in
         let e1 := elti (Pconst i) e in
         let e2 := elti e (Pconst j) in
         eand e1 e2
      | None => Pbool true
      end
  | ULt ws k z =>
      match List.nth_error vs k with
      | Some x => elti x (Pconst z)
      | None => Pbool true
      end
  | UGe ws z k =>
      match List.nth_error vs k with
      | Some x => elei (Pconst z) x
      | None => Pbool true
      end
  | UaddLe ws k1 k2 z =>
      match List.nth_error vs k1 with
      | Some x => 
          match List.nth_error vs k1 with
          | Some y => elei (eaddi x y) (Pconst z)
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
        eneqi dv ezero 
       (*   
            let dd := wdwords hi lo in
            let dv := wsigned dv in
            let q  := (Z.quot dd dv)%Z in
            let r  := (Z.rem  dd dv)%Z in
            let ov := (q <? wmin_signed sz)%Z || (q >? wmax_signed sz)%Z in
            ~((dv == 0)%Z || ov)*)
      | [:: hi; lo; dv],Unsigned =>
        eneqi dv ezero
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

Definition get_sopn_safe_conds (es: pexprs) (o: sopn) :=
  let instr_descr := get_instr_desc o in
  map (safe_cond_to_e es) instr_descr.(i_safe).

Fixpoint sc_instr (i : instr) : cmd :=
  let: (MkI ii ir) := i in
  match ir with
  | Cassgn lv _ _ e =>
    let sc_lv := sc_lval lv in
    let sc_e := sc_pexpr e in
    safe_assert ii (sc_lv ++ sc_e) ++ [::i]
  | Copn lvs _ o es  =>
    let sc_lvs := conc_map sc_lval lvs in
    let sc_es := conc_map sc_pexpr es in
    let sc_op := get_sopn_safe_conds es o in
    safe_assert ii (sc_lvs ++ sc_es ++ sc_op) ++ [::i]
  | Csyscall lvs _ es
  | Ccall lvs _ es =>
    let sc_lvs := conc_map sc_lval lvs in
    let sc_es := conc_map sc_pexpr es in
    safe_assert ii (sc_lvs ++ sc_es) ++ [::i]
  | Cif e c1 c2 =>
    let sc_e := sc_pexpr e in
    let sc_c1 := conc_map sc_instr c1 in
    let sc_c2 := conc_map sc_instr c2 in
    let i := MkI ii (Cif e sc_c1 sc_c2) in
    safe_assert ii sc_e ++ [::i]
  | Cfor x (d,e1,e2) c =>
    let sc_c := conc_map sc_instr c in    
    let sc_e := sc_pexpr e1 ++ sc_pexpr e2 in
    let i := MkI ii (Cfor x (d,e1,e2) sc_c) in
    safe_assert ii sc_e ++ [::i]
  | Cwhile a c1 e ii_w c2 => 
    let sc_e := safe_assert ii (sc_pexpr e) in
    let sc_c1 := conc_map sc_instr c1 ++ sc_e in
    let sc_c2 := conc_map sc_instr c2 in
    let i := MkI ii (Cwhile a sc_c1 e ii_w sc_c2) in
    [::i]
  | Cassert a =>
    let sc_e := sc_pexpr a.2 in
    safe_assert ii sc_e ++ [::i]
  end.

Definition sc_a_and (a : assertion) :=
  let sc_e := sc_pexpr a.2 in
  (a.1, eands (rcons sc_e a.2)).

Definition sc_ci ci :=
  let ci_pre := map sc_a_and ci.(f_pre) in
  let ci_post := map sc_a_and ci.(f_post) in
  MkContra ci.(f_iparams) ci.(f_ires) ci_pre ci_post.

Definition sc_fun (f: ufundef) :=
  let 'MkFun ii ci tin p c tout r ev := f in
  let ci :=
    match ci with
    | None => None
    | Some ci => Some (sc_ci ci)
    end
  in
  let c := conc_map sc_instr c in
  MkFun ii ci tin p c tout r ev.

Definition sc_prog (p:_uprog) : _uprog := map_prog sc_fun p.

End SAFETY.
