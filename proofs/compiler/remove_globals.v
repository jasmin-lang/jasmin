(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import xseq.
Require Import compiler_util ZArith expr leakage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Section REMOVE.

  Context (is_glob : var -> bool).
  Context (fresh_id : glob_decls -> var -> Ident.ident).

  Notation venv := (Mvar.t global).

  Fixpoint myfind (A B:Type) (f: A -> option B) (l:seq A) : option B :=
    match l with
    | [::] => None
    | a :: l =>
      let fa := f a in
      if fa is None then myfind f l else fa
    end.

  Definition find_glob ii (xi:var_i) (gd:glob_decls) (ws:wsize) (z:Z) :=
    let test (gv:glob_decl) :=
      if (ws == size_of_global gv.1) && (z == gv.2) then Some gv.1
      else None in
    match myfind test gd with
    | None => cferror (Ferr_remove_glob ii xi)
    | Some g => ok g
    end.

  Definition add_glob ii (x:var) (gd:glob_decls) (ws:wsize) (z:Z) :=
    let test (gv:glob_decl) :=
      (ws == size_of_global gv.1) && (z == gv.2) in
    if has test gd then ok gd
    else
      let g := Global ws (fresh_id gd x) in
      if has (fun g' => g'.1 == g) gd then cferror (Ferr_remove_glob_dup ii g)
      else ok ((g, z) :: gd).

  Fixpoint extend_glob_i  (i:instr) (gd:glob_decls) :=
    let (ii,i) := i in
    match i with
    | Cassgn lv _ ty e =>
      match lv with
      | Lvar xi =>
        let x := xi.(v_var) in
        if is_glob x then
          match e with
          | Papp1 (Oword_of_int ws) (Pconst z) => add_glob ii x gd ws z
          | _                   => cferror (Ferr_remove_glob ii xi)
          end
        else ok gd
      | _ => ok gd
      end
    | Copn _ _ _ _ | Ccall _ _ _ _ => ok gd
    | Cif _ c1 c2 =>
      Let gd := foldM extend_glob_i gd c1 in
      foldM extend_glob_i gd c2
    | Cwhile _ c1 _ c2 =>
      Let gd := foldM extend_glob_i gd c1 in
      foldM extend_glob_i gd c2
    | Cfor _ _ c =>
      foldM extend_glob_i gd c
    end.

  Definition extend_glob_prog (p:prog) :=
    foldM (fun f gd => foldM extend_glob_i gd f.2.(f_body)) (p_globs p) (p_funcs p).

  Section GD.
    Context (gd:glob_decls).

    Fixpoint remove_glob_e ii (env:venv) (e:pexpr) : cfexec (pexpr * leak_e_tr) :=
      match e with
      | Pconst _ | Pbool _ => ok (e, LT_id)
      | Parr_init _ => ok (e, LT_id)
      | Pvar xi =>
        let x := xi.(v_var) in
        if is_glob x then
          match Mvar.get env x with
          | Some g => ok ((Pglobal g), LT_id)
          | None   => cferror (Ferr_remove_glob ii xi)
          end
        else ok (e, LT_id)
      | Pglobal g => ok (e, LT_id)
      | Pget ws xi e =>
        let x := xi.(v_var) in
        if is_glob x then cferror (Ferr_remove_glob ii xi)
        else
          Let e := remove_glob_e ii env e in
          ok ((Pget ws xi e.1), LT_map [:: e.2 ; LT_id])
      | Pload ws xi e =>
        let x := xi.(v_var) in
        if is_glob x then cferror (Ferr_remove_glob ii xi)
        else
          Let e := remove_glob_e ii env e in
          ok ((Pload ws xi e.1), LT_map [:: e.2; LT_id])
      | Papp1 o e =>
        Let e := remove_glob_e ii env e in
        ok ((Papp1 o e.1), LT_map [:: e.2; LT_id])
      | Papp2 o e1 e2 =>
        Let e1 := remove_glob_e ii env e1 in
        Let e2 := remove_glob_e ii env e2 in
        ok ((Papp2 o e1.1 e2.1), LT_map [:: LT_map[:: e1.2; e2.2]; LT_id]) 
      | PappN op es =>
        Let vs := mapM (remove_glob_e ii env) es in
        ok ((PappN op (unzip1 vs)), LT_map [:: LT_map (unzip2 vs); LT_id])
      | Pif t e e1 e2 =>
        Let e := remove_glob_e ii env e in
        Let e1 := remove_glob_e ii env e1 in
        Let e2 := remove_glob_e ii env e2 in
        ok ((Pif t e.1 e1.1 e2.1), LT_map [:: e.2; e1.2; e2.2])
      end.

    Definition remove_glob_lv ii (env:venv) (lv:lval) : cfexec (lval * leak_e_tr) :=
      match lv with
      | Lnone _ _ => ok (lv, LT_id)
      | Lvar xi =>
        let x := xi.(v_var) in
        if is_glob x then cferror (Ferr_remove_glob ii xi)
        else ok (lv, LT_id)
      | Lmem ws xi e =>
        let x := xi.(v_var) in
        if is_glob x then cferror (Ferr_remove_glob ii xi)
        else
          Let e := remove_glob_e ii env e in
          ok ((Lmem ws xi e.1), LT_map [:: e.2; LT_id])
      | Laset ws xi e =>
        let x := xi.(v_var) in
        if is_glob x then cferror (Ferr_remove_glob ii xi)
        else
          Let e := remove_glob_e ii env e in
          ok ((Laset ws xi e.1), LT_map [:: e.2; LT_id])
      end.

    Section REMOVE_C.
      Variable (remove_glob_i : venv -> instr -> cfexec (venv * cmd * leak_i_tr)).

      Fixpoint remove_glob (e:venv) (c:cmd) : cfexec (venv * cmd * leak_c_tr) :=
        match c with
        | [::] => ok (e, [::], [::])
        | i::c =>
          Let envi := remove_glob_i e i in
          let: (vei, ci, lti) := envi in 
          Let envc := remove_glob vei c in
          let: (vci, cc, ltc) := envc in                   
          ok (vci, List.app ci cc, lti :: ltc)
        end.

    End REMOVE_C.

    Definition merge_glob (x:var) (o1 o2:option global) :=
      match o1, o2 with
      | Some g1, Some g2 => if g1 == g2 then o1 else None
      | _, _ => None
      end.

    Definition Mincl (m1 m2 : venv) :=
      all (fun xg => if Mvar.get m2 xg.1 is Some g' then xg.2 == g' else false)
        (Mvar.elements m1).

    Definition merge_env (env1 env2:venv) := Mvar.map2 merge_glob env1 env2.

    Section INSTR.

    Variable fn:funname.

    Section Loop2.

      Variable check_c : venv -> cfexec (venv * cmd * leak_c_tr).

      Fixpoint loop (n:nat) (m:venv) :=
        match n with
        | O => cferror (Ferr_fun fn (Cerr_Loop "remove_glob"))
        | S n =>
          Let m' := check_c m in
          let: (mc, cc, ltc) := m' in
          if Mincl m mc then ok (m, cc, ltc)
          else loop n (merge_env m mc)
        end.

      Variable A : Type.
      Variant check2_r :=
        | Check2_r : pexpr -> (venv * cmd) -> (venv * cmd * A) -> check2_r.

      Variant loop2_r :=
        | Loop2_r : pexpr -> cmd -> cmd -> (venv * A) -> loop2_r.

      Variable check_c2 : venv -> cfexec check2_r.

      Fixpoint loop2 (n:nat) (m:venv) :=
        match n with
        | O => cferror (Ferr_fun fn (Cerr_Loop "remove_glob"))
        | S n =>
          Let cr := check_c2 m in
          let: (Check2_r e (m1,c1) (m2,c2, lt)) := cr in
          if Mincl m m2 then ok (Loop2_r e c1 c2 (m1, lt)) else loop2 n (merge_env m m2)
        end.

    End Loop2.

    Fixpoint remove_glob_i (env:venv) (i:instr) : cfexec (venv * cmd * leak_i_tr) :=
      match i with
      | MkI ii i =>
        match i with
        | Cassgn lv tag ty e =>
          Let e := remove_glob_e ii env e in
          match lv with
          | Lvar xi =>
            let x := xi.(v_var) in
            if is_glob x then
              match e.1 with
              | Papp1 (Oword_of_int ws) (Pconst z) =>
                if (ty == sword ws) && (vtype x == sword ws) then
                  Let g := find_glob ii xi gd ws z in
                  ok (Mvar.set env x g, [::], LT_iremove)
                else cferror (Ferr_remove_glob ii xi)
              | _ => cferror (Ferr_remove_glob ii xi)
              end
            else
              Let rlv := remove_glob_lv ii env lv in
              ok (env, [::MkI ii (Cassgn rlv.1 tag ty e.1)], LT_ile (LT_map ([:: e.2 ; rlv.2])))
          | _ =>
            Let rlv := remove_glob_lv ii env lv in
            ok (env, [::MkI ii (Cassgn rlv.1 tag ty e.1)], LT_ile (LT_map ([:: e.2 ; rlv.2])))
          end
        | Copn lvs tag o es =>
          Let rlvs := mapM (remove_glob_lv ii env) lvs in
          Let res  := mapM (remove_glob_e ii env) es in
          ok (env, [::MkI ii (Copn (unzip1 rlvs) tag o (unzip1 res))],
              LT_ile (LT_map [:: LT_map (unzip2 res) ; LT_id; LT_map (unzip2 rlvs)]))
        | Cif e c1 c2 =>
          Let e := remove_glob_e ii env e in
          Let envc1 := remove_glob remove_glob_i env c1 in
          let: (env1, c1, ltc1) := envc1 in
          Let envc2 := remove_glob remove_glob_i env c2 in
          let: (env2, c2, ltc2) := envc2 in
          let env := merge_env env1 env2 in
          ok (env, [::MkI ii (Cif e.1 c1 c2)], LT_icond e.2 ltc1 ltc2)
        | Cwhile a c1 e c2 =>
          let check_c env :=
            Let envc1 := remove_glob remove_glob_i env c1 in
            let: (env1, c1, ltc1) := envc1 in
            Let e := remove_glob_e ii env1 e in
            Let envc2 := remove_glob remove_glob_i env1 c2 in
            let: (env2, c2, ltc2) := envc2 in
            ok ((Check2_r e.1 (env1, c1) (env2, c2, (ltc1, e.2, ltc2)))) in
          Let lr := loop2 check_c Loop.nb env in
          let: (Loop2_r e c1 c2 (env, (ltc, lte, ltc'))) := lr in
          ok (env, [::MkI ii (Cwhile a c1 e c2)], LT_iwhile ltc lte ltc')
        | Cfor xi (d,e1,e2) c =>
          if is_glob xi.(v_var) then cferror (Ferr_remove_glob ii xi)
          else
            Let e1 := remove_glob_e ii env e1 in
            Let e2 := remove_glob_e ii env e2 in
            let check_c env := remove_glob remove_glob_i env c in
            Let envc := loop check_c Loop.nb env in
            let: (env, c, ltc) := envc in
            ok (env, [::MkI ii (Cfor xi (d,e1.1,e2.1) c)], LT_ifor (LT_map [:: e1.2; e2.2]) ltc)
        | Ccall i lvs fn es =>
          Let lvs := mapM (remove_glob_lv ii env) lvs in
          Let es  := mapM (remove_glob_e ii env) es in
          ok (env, [::MkI ii (Ccall i (unzip1 lvs) fn (unzip1 es))],
                   (LT_icall fn (LT_map (unzip2 es)) (LT_map (unzip2 lvs))))
        end
      end.

    End INSTR.

    Definition remove_glob_fundef (f:funname * fundef) :=
      let (fn, f) := f in
      let env := Mvar.empty _ in
      let check_var xi :=
        if is_glob xi.(v_var) then cferror (Ferr_remove_glob xH xi) else ok (tt) in
      Let _ := mapM check_var f.(f_params) in
      Let _ := mapM check_var f.(f_res) in
      Let envc := remove_glob (remove_glob_i fn) env f.(f_body) in
      let: (env1, c1, ltc) := envc in
      ok
        ({| f_iinfo := f.(f_iinfo);
                f_tyin  := f.(f_tyin);
                f_params := f.(f_params);
                f_body   := c1;
                f_tyout := f.(f_tyout);
                f_res   := f.(f_res); |}, ltc).
  End GD.

  Definition remove_glob_prog (p:prog) : cfexec (prog * leak_f_tr) :=
    Let gd := extend_glob_prog p in
      if uniq (map fst gd) then
      Let fs := map_fnprog_leak (remove_glob_fundef gd) (p_funcs p) in
      ok ({| p_globs := gd; p_funcs := fs.1|}, fs.2)
    else cferror Ferr_uniqglob.


End REMOVE.

