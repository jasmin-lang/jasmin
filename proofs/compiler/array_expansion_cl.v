(* ** Imports and settings *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From mathcomp Require Import word_ssrZ.
Require Import expr.
Require Import compiler_util ZArith.
Import Utf8.

Require Import array_expansion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Module Import E.
  Definition pass : string := "array expansion cryptoline".

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

Record t := {
  svars : Sv.t;
  sarrs : Mvar.t array_info;
  selem : Sv.t;
}.

Definition expd_t := (Mf.t (seq (option (wsize * Z)) * seq (option (wsize * Z)))).

Definition init_elems svars xi (svmi : Sv.t * Z) :=
  let '(sv,i) := svmi in
  Let _ := assert (~~ Sv.mem xi sv && ~~ Sv.mem xi svars) (reg_ierror_no_var "init_elems") in
  ok (Sv.add xi sv, (i + 1)%Z).

Definition init_array_info svars (x : varr_info) (svm:Sv.t * Mvar.t array_info) :=
  let (sv,m) := svm in
  let ty := sword x.(vi_s) in
  Let _ :=  assert (~~ Sv.mem x.(vi_v) sv && ~~Sv.mem x.(vi_v) svars) (reg_ierror_no_var "init_array_info") in
  let vars := map (fun id => {| vtype := ty; vname := id |}) x.(vi_n) in
  Let svelems := foldM (init_elems svars) (sv,0%Z) vars in
  let '(sv, len) := svelems in
  Let _ := assert [&& (0 <? len)%Z & vtype (vi_v x) == sarr (Z.to_pos (arr_size x.(vi_s) (Z.to_pos len)))]
             (reg_ierror_no_var "init_array_info") in
  ok (sv, Mvar.set m x.(vi_v) {| ai_ty := x.(vi_s); ai_len := len; ai_elems := vars |}).

Definition init_map (fi : expand_info) :=
  let svars := sv_of_list (fun x => x) fi.(vars) in
  Let sarrs := foldM (init_array_info svars) (Sv.empty, Mvar.empty _) fi.(arrs) in
  ok ({| svars := svars; sarrs := sarrs.2; selem := sarrs.1 |}, finfo fi).

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

  | Pbig idx op x body s len =>
    Let _ := assert (Sv.mem x m.(svars)) (reg_ierror x "Pbig binder not in svar") in
    Let idx := expand_e m idx in
    Let body := expand_e m body in
    Let s := expand_e m s in
    Let len := expand_e m len in
    ok (Pbig idx op x body s len)

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

Context (fresh_var_ident: v_kind → string → stype → Ident.ident).

Let fresh_var (ws: wsize) v : var :=
  {| vtype := sword ws;
     vname := fresh_var_ident (Reg (Normal, Direct)) (Ident.id_name (vname v)) (sword ws) |}.

Section FSIGS.

Context (fsigs : expd_t).

Definition is_array_move_lval (m:t) x :=
  match x with
  | Lvar x =>
    match Mvar.get m.(sarrs) x with
    | Some ai => Some(ai.(ai_ty), v_info x, ai.(ai_elems))
    | None => None
    end
  | Lasub aa ws' len' x e =>
    match Mvar.get m.(sarrs) x, is_const e with
    | Some ai, Some i =>
      if (ai.(ai_ty) == ws') && (aa == AAscale) then
        Some (ws', v_info x, take (Pos.to_nat len') (drop (Z.to_nat i) ai.(ai_elems)))
      else None
    | _, _ => None
    end
  | _ => None
  end.

Definition is_array_move_rval (m:t) x :=
  match x with
  | Pvar x =>
    if is_lvar x then
      let x := gv x in
      match Mvar.get m.(sarrs) x with
      | Some ai => Some(ai.(ai_ty), v_info x, ai.(ai_elems))
      | None => None
      end
    else None
  | Psub aa ws' len' x e =>
    if is_lvar x then
      let x := gv x in
      match Mvar.get m.(sarrs) x, is_const e with
      | Some ai, Some i =>
        if (ai.(ai_ty) == ws') && (aa == AAscale) then
          Some (ws', v_info x, take (Pos.to_nat len') (drop (Z.to_nat i) ai.(ai_elems)))
        else None
      | _, _ => None
      end
    else None
  | _ => None
  end.

Definition is_array_move m x e :=
  match is_array_move_lval m x, is_array_move_rval m e with
  | Some (ws1, vi1, t1), Some (ws2, vi2, t2) =>
    let len2 := size t2 in
    (* The test 0 < len2 is not necessary but it simplify proofs *)
    if [&& ws1 == ws2, size t1 == len2 & 0 < len2] then Some (ws1, vi1, t1, vi2, t2)
    else None
  | _, _ => None
  end.

Definition check_fresh selem svars xs :=
  foldM (fun x selem =>
           Let _ := assert (~~Sv.mem x selem && ~~ Sv.mem x svars)
                           (reg_ierror_no_var "fresh does not work") in
           ok (Sv.add x selem)) selem xs.

Fixpoint expand_i (m : t) (i : instr) : cexec cmd :=
  let (ii,ir) := i in
  match ir with
  | Cassgn x tag ty e =>
    match is_array_move m x e with
    | Some (ws, vi1, t1, vi2, t2) =>
      let aux := map (fresh_var ws) t2 in
      Let _ := check_fresh m.(selem) m.(svars) aux in
      ok (map2 (fun x1 x2 => MkI ii (Cassgn (Lvar (VarI x1 vi2)) tag (sword ws) (Plvar (VarI x2 vi2))))
               aux t2 ++
          map2 (fun x1 x2 => MkI ii (Cassgn (Lvar (VarI x1 vi1)) tag (sword ws) (Plvar (VarI x2 vi2))))
               t1 aux)

    | None =>
      Let x := add_iinfo ii (expand_lv m x) in
      Let e := add_iinfo ii (expand_e m e) in
      ok [:: MkI ii (Cassgn x tag ty e) ]
    end

  | Copn xs tag o es =>
    Let xs := add_iinfo ii (expand_lvs m xs) in
    Let es := add_iinfo ii (expand_es m es) in
    ok [:: MkI ii (Copn xs tag o es) ]

  | Csyscall xs o es =>
    Let xs := add_iinfo ii (expand_lvs m xs) in
    Let es := add_iinfo ii (expand_es m es) in
    ok [:: MkI ii (Csyscall xs o es) ]

  | Cassert t p b =>
    Let b  := add_iinfo ii (expand_e m b) in
    ok [:: MkI ii (Cassert t p b)]

  | Cif b c1 c2 =>
    Let b  := add_iinfo ii (expand_e m b) in
    Let c1 := mapM (expand_i m) c1 in
    Let c2 := mapM (expand_i m) c2 in
    ok [:: MkI ii (Cif b (flatten c1) (flatten c2)) ]

  | Cfor x (dir, e1, e2) c =>
    Let _  := add_iinfo ii (assert (Sv.mem x m.(svars)) (reg_ierror x "reg array as a variable of a for loop")) in
    Let e1 := add_iinfo ii (expand_e m e1) in
    Let e2 := add_iinfo ii (expand_e m e2) in
    Let c  := mapM (expand_i m) c in
    ok [:: MkI ii (Cfor x (dir, e1, e2) (flatten c)) ]

  | Cwhile a c e c' =>
    Let e  := add_iinfo ii (expand_e m e) in
    Let c  := mapM (expand_i m) c in
    Let c' := mapM (expand_i m) c' in
    ok [:: MkI ii (Cwhile a (flatten c) e (flatten c')) ]

  | Ccall xs fn es =>
    if Mf.get fsigs fn is Some (expdin, expdout) then
      Let xs := add_iinfo ii (rmap flatten (mapM2 length_mismatch (expand_return m) expdout xs)) in
      Let es := add_iinfo ii (rmap flatten (mapM2 length_mismatch (expand_param m) expdin es)) in
      ok [:: MkI ii (Ccall xs fn es) ]
    else Error (reg_ierror_no_var "function not found")
  end.

Definition expand_fbody (fname: funname) (fs: ufundef * (cmd * t)) :=
  let (fd, m) := fs in
  let (init, m) := m in
  match fd with
  | MkFun fi ci tyin params c tyout res ef =>
    Let c := mapM (expand_i m) c in
    ok (MkFun fi ci tyin params (init ++ flatten c) tyout res ef)
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
                    (reg_error (v_var v) "error")
               (* (reg_ierror v "there should be an invariant ensuring this never happens in array_expansion_proof") *)
      in
    ok ([:: ty], [:: v], None).

Definition restr_map X (m:t) :=
 {| svars := m.(svars)
  ; sarrs := Mvar.filter_map (fun x ai => if Sv.mem x X then Some ai else None) m.(sarrs)
  ; selem := m.(selem)
 |}.

Definition expand_ci m exp (insf: seq (seq stype * seq var_i * option (wsize * Z)))
                           (ins: seq (option (wsize * Z)))
                           (outsf: seq (seq stype * seq var_i * option (wsize * Z)))
                           (outs: seq (option (wsize * Z)))
 ityin tyout ci :=
  match ci with
  | Some ci =>
    Let iins := mapM2 length_mismatch (expand_tyv m exp "the parameters") ityin ci.(f_iparams) in
    Let _ := assert ([seq x.1.1 | x <- insf] == [seq x.1.1 | x <- iins])
                    (E.reg_ierror_no_var "ins.1.1 <> iins.1.1") in
    Let _ := assert (ins == [seq i.2 | i <- iins]) (E.reg_ierror_no_var "ins <> map snd iins") in
    let ci_params := flatten (map (fun x => snd (fst x)) iins) in
    Let ires := mapM2 length_mismatch (expand_tyv m exp "the results") tyout ci.(f_ires) in
    Let _ := assert ([seq x.1.1 | x <- outsf] == [seq x.1.1 | x <- ires])
                    (E.reg_ierror_no_var "outsf.1.1 <> ires.1.1") in
    Let _ := assert (outs == [seq i.2 | i <- ires]) (E.reg_ierror_no_var "outs <> map snd ires") in
    let ci_res := flatten (map (fun x => snd (fst x)) ires) in
    let X := sv_of_list v_var ci.(f_iparams) in
    let m_pre := restr_map X m in
    Let ci_pre := mapM (fun c =>
                        Let e := expand_e m_pre (snd c) in
                        ok(fst c, e)) ci.(f_pre) in
    let m_post := restr_map (Sv.union X (sv_of_list v_var ci.(f_ires))) m in
    Let ci_post := mapM (fun c =>
                        Let e := expand_e m_post (snd c) in
                        ok(fst c, e)) ci.(f_post) in
    ok (Some (MkContra ci_params ci_res ci_pre ci_post))
  | None => ok None
  end.

Definition init_array (params:Sv.t) (a:var) (ai:array_info) (all:cmd) :=
  if Sv.mem a params then all else
  let vi := dummy_var_info in
  let ws := ai.(ai_ty) in
  let ty := sword ws in
  let z  := wconst (wrepr ws 0) in
  map (fun x => MkI dummy_instr_info (Cassgn (Lvar (VarI x vi)) AT_none ty z)) ai.(ai_elems)
  ++ all.

Definition expand_fsig fi (entries : seq funname) (fname: funname) (fd: ufundef) :=
  Let x := init_map (fi fname fd) in
  match fd with
  | MkFun _ ci ityin params c ityout res ef =>
    let '(m, fi) := x in
    let exp := ~~(fname \in entries) in
    Let insf  := mapM2 length_mismatch (expand_tyv m exp "the parameters") ityin params in
    let tyin   := map (fun x => fst (fst x)) insf in
    let s := sv_of_list v_var params in
    let params := map (fun x => snd (fst x)) insf in
    let ins := map snd insf in
    Let outsf := mapM2 length_mismatch (expand_tyv m exp "the return type") ityout res in
    let tyout  := map (fun x => fst (fst x)) outsf in
    let res    := map (fun x => snd (fst x)) outsf in
    let outs   := map snd outsf in
    Let ci := expand_ci m exp insf ins outsf outs ityin ityout ci in
    let init :=
      Mvar.fold (init_array s) m.(sarrs) [::] in
    ok (MkFun fi ci (flatten tyin) (flatten params) c (flatten tyout) (flatten res) ef,
        (init, m), (ins, outs))
  end.

End FSIGS.

Notation map_cfprog_name_cdata := (map_cfprog_name_gen (fun x => @f_info _ _ _ _ (fst (fst x)))).

Definition expand_prog (fi : funname -> ufundef -> expand_info) (entries : seq funname) (p: uprog) : cexec uprog :=
  Let step1 := map_cfprog_name (expand_fsig fi entries) (p_funcs p) in
  let fsigs := foldr (fun x y => Mf.set y x.1 x.2.2) (Mf.empty _) step1 in
  Let funcs := map_cfprog_name_cdata (fun fn x => expand_fbody fsigs fn (fst x)) step1 in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End ASM_OP.
