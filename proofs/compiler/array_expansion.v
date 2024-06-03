(* ** Imports and settings *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From mathcomp Require Import word_ssrZ.
Require Import expr.
Require Import compiler_util ZArith.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Module Import E.
  Definition pass : string := "array expansion".

  Definition reg_error (x:var_i) msg := {|
    pel_msg := pp_box [:: pp_s "cannot expand variable"; pp_var x; pp_s msg];
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := Some x.(v_info);
    pel_pass := Some pass;
    pel_internal := false
  |}.

  Definition reg_error_expr e msg := {|
    pel_msg := pp_nobox [:: pp_s "cannot expand expression"; PPEbreak;
                            pp_s "  "; pp_e e; PPEbreak; pp_s msg];
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := None;
    pel_pass := Some pass;
    pel_internal := false
  |}.

  Definition reg_ferror (fi : fun_info) msg := {|
    pel_msg := pp_s msg;
    pel_fn := None;
    pel_fi := Some fi;
    pel_ii := None;
    pel_vi := None;
    pel_pass := Some pass;
    pel_internal := false
  |}.

  Definition reg_ierror (x:var_i) msg := {|
    pel_msg := pp_box [:: pp_s msg; pp_nobox [:: pp_s "("; pp_var x; pp_s ")"]];
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := Some x.(v_info);
    pel_pass := Some pass;
    pel_internal := true
  |}.

  Definition length_mismatch := pp_internal_error_s pass "length mismatch".

  Definition reg_ierror_no_var := pp_internal_error_s pass.

End E.

Record varr_info := {
  vi_v : var;
  vi_s : wsize;
  vi_n : list Ident.ident;
}.

Record expand_info := {
  vars : list var;
  arrs : list varr_info;
  finfo : fun_info;
}.

Record array_info := {
   ai_ty     : wsize;
   ai_len    : Z;
   ai_elems  : list var;
}.

Record t := {
  svars : Sv.t;
  sarrs : Mvar.t array_info;
}.

Definition expd_t := (Mf.t (seq (option (wsize * Z)) * seq (option (wsize * Z)))).

Definition init_elems xi (svmi : Sv.t * Z) :=
  let '(sv,i) := svmi in
  Let _ := assert (~~ Sv.mem xi sv) (reg_ierror_no_var "init_elems") in
  ok (Sv.add xi sv, (i + 1)%Z).

Definition init_array_info (x : varr_info) (svm:Sv.t * Mvar.t array_info) :=
  let (sv,m) := svm in
  let ty := sword x.(vi_s) in
  Let _ :=  assert (~~ Sv.mem x.(vi_v) sv) (reg_ierror_no_var "init_array_info") in
  let vars := map (fun id => {| vtype := ty; vname := id |}) x.(vi_n) in
  Let svelems := foldM init_elems (sv,0%Z) vars in
  let '(sv, len) := svelems in
  Let _ := assert [&& (0 <? len)%Z & vtype (vi_v x) == sarr (Z.to_pos (arr_size x.(vi_s) (Z.to_pos len)))]
             (reg_ierror_no_var "init_array_info") in
  ok (sv, Mvar.set m x.(vi_v) {| ai_ty := x.(vi_s); ai_len := len; ai_elems := vars |}).

Definition init_map (fi : expand_info) := 
  let svars := sv_of_list (fun x => x) fi.(vars) in
  Let sarrs := foldM init_array_info (svars, Mvar.empty _) fi.(arrs) in
  ok ({| svars := svars; sarrs := sarrs.2 |}, finfo fi).

Definition check_gvar (m : t) (x: gvar) := 
  ~~ is_lvar x || Sv.mem (gv x) m.(svars).

Definition nelem (ty: stype) (ws: wsize) : Z :=
  if ty is sarr n
  then n / wsize_size ws
  else 0.

Fixpoint expand_e (m : t) (e : pexpr) : cexec pexpr := 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ => ok e

  | Pvar x =>
    Let _ := assert (check_gvar m x) (reg_error x.(gv) "(the array cannot be manipulated alone, you need to access its cells instead)") in
    ok e

  | Pget al aa ws x e1 =>
    if check_gvar m x then
      Let e1 := expand_e m e1 in
      ok (Pget al aa ws x e1)
    else
      let x := gv x in
      match Mvar.get m.(sarrs) x, is_const e1 with
      | Some ai, Some i =>
        Let _ := assert (ai.(ai_ty) == ws) (reg_error x "(the default scale must be used)") in
        Let _ := assert (al == Aligned) (reg_error x "(alignement must be enforced)") in
        Let _ := assert (aa == AAscale) (reg_error x "(the default scale must be used)") in
        Let _ := assert [&& 0 <=? i & i <? ai.(ai_len)]%Z (reg_error x "(index out of bounds)") in
        let v := znth (v_var x) ai.(ai_elems) i in
        ok (Pvar (mk_lvar {| v_var := v; v_info := v_info x |}))
      | _, _ => Error (reg_error x "(the index is not a constant)")
      end

  | Psub aa ws len x e1 => 
    Let _ := assert (check_gvar m x) (reg_error x.(gv) "(sub-reg arrays are not allowed)") in
    Let e1 := expand_e m e1 in
    ok (Psub aa ws len x e1)

  | Pload al ws x e1 =>
    Let _ := assert (Sv.mem x m.(svars)) (reg_ierror x "reg array in memory access") in
    Let e1 := expand_e m e1 in
    ok (Pload al ws x e1)

  | Papp1 o e1 => 
    Let e1 := expand_e m e1 in
    ok (Papp1 o e1)

  | Papp2 o e1 e2 =>
    Let e1 := expand_e m e1 in
    Let e2 := expand_e m e2 in
    ok (Papp2 o e1 e2) 

  | PappN o es => 
    Let es := mapM (expand_e m) es in
    ok (PappN o es)

  | Pif ty e1 e2 e3 =>
    Let e1 := expand_e m e1 in
    Let e2 := expand_e m e2 in
    Let e3 := expand_e m e3 in
    ok (Pif ty e1 e2 e3) 

  end.

Definition expand_lv (m : t) (x : lval)  :=
  match x with
  | Lnone _ _ => ok x

  | Lvar x => 
    Let _ := assert (Sv.mem x m.(svars)) (reg_error x "(the array cannot be manipulated alone, you need to access its cells instead)") in
    ok (Lvar x)

  | Lmem al ws x e =>
    Let _ := assert (Sv.mem x m.(svars)) (reg_ierror x "reg array in memory access") in
    Let e := expand_e m e in
    ok (Lmem al ws x e)

  | Laset al aa ws x e =>
    if Sv.mem x m.(svars) then 
      Let e := expand_e m e in
      ok (Laset al aa ws x e)
    else 
      match Mvar.get m.(sarrs) x, is_const e with
      | Some ai, Some i =>
        Let _ := assert (ai.(ai_ty) == ws) (reg_error x "(the default scale must be used)") in
        Let _ := assert (al == Aligned) (reg_error x "(alignement must be enforced)") in
        Let _ := assert (aa == AAscale) (reg_error x "(the default scale must be used)") in
        Let _ := assert [&& 0 <=? i & i <? ai.(ai_len)]%Z (reg_error x "(index out of bounds)") in
        let v := znth (v_var x) ai.(ai_elems) i in
        ok (Lvar {| v_var := v; v_info := v_info x |})
      | _, _ => Error (reg_error x "(the index is not a constant)")
      end

  | Lasub aa ws len x e =>
    Let _ := assert (Sv.mem x m.(svars)) (reg_error x "(sub-reg arrays are not allowed)") in
    Let e := expand_e m e in
    ok (Lasub aa ws len x e)

  end.

Definition expand_es m := mapM (expand_e m).

Definition expand_lvs m := mapM (expand_lv m).

Definition expand_param (m : t) ex (e : pexpr) : cexec _ :=
  match ex with
  | Some (ws, len) =>
    match e with
    | Pvar x =>
      Let ai := o2r (reg_error (gv x) "(not a reg array)") (Mvar.get m.(sarrs) (gv x)) in
      Let _ := assert [&& ws == ai_ty ai, len == ai_len ai & is_lvar x]
                      (reg_error (gv x) "(type mismatch)") in
      let vi := v_info (gv x) in
      ok (map (fun v => Pvar (mk_lvar (VarI v vi))) (ai_elems ai))
    | Psub aa ws' len' x e =>
      Let _ := assert (aa == AAscale) (reg_error (gv x) "(the default scale must be used)") in
      Let i := o2r (reg_error (gv x) "(the index is not a constant)") (is_const e) in
      Let ai := o2r (reg_error (gv x) "(not a reg array)") (Mvar.get m.(sarrs) (gv x)) in
      Let _ := assert [&& ws == ai_ty ai, ws' == ws, len == len' & is_lvar x]
                      (reg_error (gv x) "(type mismatch)") in
      let elems := take (Z.to_nat len) (drop (Z.to_nat i) (ai_elems ai)) in
      let vi := v_info (gv x) in
      ok (map (fun v => Pvar (mk_lvar (VarI v vi))) elems)
    | _ =>
      Error (reg_error_expr e "Only variables and sub-arrays can be expanded in function arguments.")
    end
  | None => rmap (fun x => [:: x]) (expand_e m e)
  end.

Definition expand_return m ex x :=
  match ex with
  | Some (ws, len) =>
    match x with
    | Lnone v t => ok (nseq (Z.to_nat len) (Lnone v (sword ws)))
    | Lvar x =>
      Let ai := o2r (reg_error x "(not a reg array)") (Mvar.get m.(sarrs) x) in
      Let _ := assert [&& ws == ai_ty ai & len == ai_len ai]
                      (reg_error x "(type mismatch)") in
      let vi := v_info x in
      ok (map (fun v => Lvar (VarI v vi)) (ai_elems ai))
    | Lasub aa ws' len' x e =>
      Let _ := assert (aa == AAscale) (reg_error x "(the default scale must be used)") in
      Let i := o2r (reg_error x "(the index is not a constant)") (is_const e) in
      Let ai := o2r (reg_error x "(not a reg array)") (Mvar.get m.(sarrs) x) in
      Let _ := assert [&& ws == ai_ty ai, ws' == ws & len == len']
                      (reg_error x "(type mismatch)") in
      let vi := v_info x in
      let elems := take (Z.to_nat len) (drop (Z.to_nat i) (ai_elems ai)) in
      ok (map (fun v => Lvar (VarI v vi)) elems)
    | _ => Error (reg_ierror_no_var "only variables/sub-arrays/_ can be expanded in function return")
    end
  | None => rmap (fun x => [:: x]) (expand_lv m x)
  end.

Section ASM_OP.

Context `{asmop : asmOp}.

Section FSIGS.

Context (fsigs : expd_t).

Fixpoint expand_i (m : t) (i : instr) : cexec instr :=
  let (ii,ir) := i in
  match ir with
  | Cassgn x tag ty e =>
    Let x := add_iinfo ii (expand_lv m x) in
    Let e := add_iinfo ii (expand_e m e) in
    ok (MkI ii (Cassgn x tag ty e))

  | Copn xs tag o es =>
    Let xs := add_iinfo ii (expand_lvs m xs) in
    Let es := add_iinfo ii (expand_es m es) in
    ok (MkI ii (Copn xs tag o es))

  | Csyscall xs o es =>
    Let xs := add_iinfo ii (expand_lvs m xs) in
    Let es := add_iinfo ii (expand_es m es) in
    ok (MkI ii (Csyscall xs o es))

  | Cif b c1 c2 =>
    Let b  := add_iinfo ii (expand_e m b) in
    Let c1 := mapM (expand_i m) c1 in 
    Let c2 := mapM (expand_i m) c2 in 
    ok (MkI ii (Cif b c1 c2))

  | Cfor x (dir, e1, e2) c =>
    Let _  := add_iinfo ii (assert (Sv.mem x m.(svars)) (reg_ierror x "reg array as a variable of a for loop")) in
    Let e1 := add_iinfo ii (expand_e m e1) in
    Let e2 := add_iinfo ii (expand_e m e2) in
    Let c  := mapM (expand_i m) c in 
    ok (MkI ii (Cfor x (dir, e1, e2) c))

  | Cwhile a c e c' =>
    Let e  := add_iinfo ii (expand_e m e) in
    Let c  := mapM (expand_i m) c in 
    Let c' := mapM (expand_i m) c' in 
    ok (MkI ii (Cwhile a c e c'))

  | Ccall xs fn es =>
    if Mf.get fsigs fn is Some (expdin, expdout) then
      Let xs := add_iinfo ii (rmap flatten (mapM2 length_mismatch (expand_return m) expdout xs)) in
      Let es := add_iinfo ii (rmap flatten (mapM2 length_mismatch (expand_param m) expdin es)) in
      ok (MkI ii (Ccall xs fn es))
    else Error (reg_ierror_no_var "function not found")
  end.

Definition expand_tyv m b s ty v :=
  if Mvar.get m.(sarrs) (v_var v) is Some ai then
    Let _ := assert b (reg_error v ("(reg arrays are not allowed in " ++ s ++ " of export functions)")) in
    let vi := v_info v in
    let vvars := map (fun v' => VarI v' vi) (ai_elems ai) in
    let vtypes := map vtype (ai_elems ai) in
    ok (vtypes, vvars, Some (ai_ty ai, ai_len ai))
  else
    Let _ := assert (Sv.mem (v_var v) m.(svars))
    (reg_ierror v "there should be an invariant ensuring this never happens in array_expansion_proof") in
    ok ([:: ty], [:: v], None).

Definition expand_fsig fi (entries : seq funname) (fname: funname) (fd: ufundef) :=
  Let x := init_map (fi fname fd) in
  match fd with
  | MkFun _ tyin params c tyout res ef =>
    let '(m, fi) := x in
    let exp := ~~(fname \in entries) in
    Let ins  := mapM2 length_mismatch (expand_tyv m exp "the parameters") tyin params in
    let tyin   := map (fun x => fst (fst x)) ins in
    let params := map (fun x => snd (fst x)) ins in
    let ins    := map snd ins in
    Let outs := mapM2 length_mismatch (expand_tyv m exp "the return type") tyout res in
    let tyout  := map (fun x => fst (fst x)) outs in
    let res    := map (fun x => snd (fst x)) outs in
    let outs   := map snd outs in
    ok (MkFun fi (flatten tyin) (flatten params) c (flatten tyout) (flatten res) ef,
        m, (ins, outs))
  end.

Definition expand_fbody (fname: funname) (fs: ufundef * t) :=
  let (fd, m) := fs in
  match fd with
  | MkFun fi tyin params c tyout res ef =>
    Let c := mapM (expand_i m) c in
    ok (MkFun fi tyin params c tyout res ef)
  end.

End FSIGS.

Notation map_cfprog_name_cdata := (map_cfprog_name_gen (fun x => @f_info _ _ _ (fst (fst x)))).

Definition expand_prog (fi : funname -> ufundef -> expand_info) (entries : seq funname) (p: uprog) : cexec uprog :=
  Let step1 := map_cfprog_name (expand_fsig fi entries) (p_funcs p) in
  let fsigs := foldr (fun x y => Mf.set y x.1 x.2.2) (Mf.empty _) step1 in
  Let funcs := map_cfprog_name_cdata (fun fn x => expand_fbody fsigs fn (fst x)) step1 in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End ASM_OP.
