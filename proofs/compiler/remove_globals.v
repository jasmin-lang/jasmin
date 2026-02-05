(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Import xseq.
Require Import psem_defs.
Require Import expr compiler_util.

Definition type_of_glob_value (gv: glob_value) : atype :=
  match gv with
  | Gword ws _ => aword ws
  | Garr p _ => aarr U8 p
  end.

Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "remove globals".

  Definition rm_glob_error_gen (ii: instr_info) (x: var) (extra: seq pp_error) := {|
    pel_msg := pp_box (pp_s "Cannot remove global variable" :: pp_var x :: extra);
    pel_fn := None;
    pel_fi := None;
    pel_ii := Some ii;
    pel_vi := None;
    pel_pass := Some pass;
    pel_internal := false
  |}.

  Definition rm_glob_error ii x := rm_glob_error_gen ii x [::].

  Definition rm_glob_error_dup (ii:instr_info) (x:var) := {|
    pel_msg := pp_box [:: pp_s "Duplicate definition of global variable"; pp_var x];
    pel_fn := None;
    pel_fi := None;
    pel_ii := Some ii;
    pel_vi := None;
    pel_pass := Some pass;
    pel_internal := false
  |}.

  Definition loop_iterator := loop_iterator pass.

  Definition rm_glob_ierror := pp_internal_error_s pass.

End E.

Section REMOVE.

  Context `{asmop:asmOp}.
  Context (fresh_id : glob_decls -> var -> Ident.ident).
  Context {fcp : FlagCombinationParams}.

  Notation venv := (Mvar.t var).

  Definition check_data (d' d: glob_value) : bool :=
    match d', d with
    | @Gword ws' w', @Gword ws w => (ws == ws') && (w == zero_extend ws w')
    | @Garr len' arr', @Garr len arr => WArray.is_uincl arr arr'
    | _, _ => false
    end.

  Definition check (gv: glob_value) (gd: glob_decl) : bool :=
    (convertible (type_of_glob_value gv) (vtype gd.1)) && (check_data gd.2 gv).

  Definition find_glob ii (xi: var_i) (gd: glob_decls) (gv: glob_value) :=
    let test gd := if check gv gd then Some gd.1 else None in
    match find_map test gd with
    | None => Error (rm_glob_error ii xi)
    | Some g => ok g
    end.

  Definition add_glob ii (x: var) (gd: glob_decls) (gv: glob_value) :=
    if has (check gv) gd then ok gd
    else
      let gx := {| vtype := vtype x; vname := fresh_id gd x |} in
      if has (fun g' => g'.1 == gx) gd then Error (rm_glob_error_dup ii gx)
      else ok ((gx, gv) :: gd).

  Definition evaluate_bytes ii x : pexprs -> result pp_error_loc values :=
    mapM (fun pe =>
      if pe is Papp1 (Oword_of_int sz) (Pconst z)
      then ok (Vword (wrepr sz z))
      else Error (rm_glob_error_gen ii x [:: pp_s "a cell has a non-constant value"; pp_e pe ])
    ).

  Definition array_from_cells ii x (len: positive) (cells: pexprs) : result pp_error_loc (WArray.array len) :=
    Let bytes := evaluate_bytes ii x cells in
    match sem_opN (Oarray len) bytes >>= to_arr len with
    | Ok array => Ok _ array
    | Error _ => Error (rm_glob_error_gen ii x [:: pp_s "cannot fill the array"])
    end.

  Fixpoint extend_glob_i  (i:instr) (gd:glob_decls) :=
    let (ii,i) := i in
    match i with
    | Cassgn lv _ ty e =>
      match lv with
      | Lvar xi =>
        let x := xi.(v_var) in
        if is_glob_var x then
          match e with
          | Papp1 (Oword_of_int ws) (Pconst z) => add_glob ii x gd (Gword (wrepr ws z))
          | PappN (Oarray len) cells =>
              Let array := array_from_cells ii x len cells in
              add_glob ii x gd (Garr array)
          | _                   => Error (rm_glob_error ii xi)
          end
        else ok gd
      | _ => ok gd
      end
    | Copn _ _ _ _ | Csyscall _ _ _ _ | Cassert _ | Ccall _ _ _ _ => ok gd
    | Cif _ c1 c2 =>
      Let gd := foldM extend_glob_i gd c1 in
      foldM extend_glob_i gd c2
    | Cwhile _ c1 _ _ c2 =>
      Let gd := foldM extend_glob_i gd c1 in
      foldM extend_glob_i gd c2
    | Cfor _ _ c =>
        (* FIXME: there are no for loops at this point *)
      foldM extend_glob_i gd c
    end.

  Definition extend_glob_prog (p:uprog) :=
    foldM (fun f gd => foldM extend_glob_i gd f.2.(f_body)) (p_globs p) (p_funcs p).

  Section GD.
    Context (gd:glob_decls).

    Definition get_var_ ii (env:venv) (xi:gvar) := 
      if is_lvar xi then
        let vi := xi.(gv) in 
        let x := vi.(v_var) in
        if is_glob_var x then
          match Mvar.get env x with
          | Some g => ok (mk_gvar (VarI g vi.(v_info)))
          | None   => Error (rm_glob_error ii vi)
          end 
        else ok xi
      else ok xi.

    Fixpoint remove_glob_e ii (env:venv) (e:pexpr) :=
      match e with
      | Pconst _ | Pbool _ => ok e
      | Parr_init _ _ => ok e
      | Pvar xi =>
        Let xi := get_var_ ii env xi in
        ok (Pvar xi)

      | Pget al aa ws xi e =>
        Let e  := remove_glob_e ii env e in
        Let xi := get_var_ ii env xi in
        ok (Pget al aa ws xi e)

      | Psub aa ws len xi e =>
        Let e  := remove_glob_e ii env e in
        Let xi := get_var_ ii env xi in
        ok (Psub aa ws len xi e)

      | Pload al ws e =>
        Let e := remove_glob_e ii env e in
        ok (Pload al ws e)
      | Papp1 o e =>
        Let e := remove_glob_e ii env e in
        ok (Papp1 o e)
      | Papp2 o e1 e2 =>
        Let e1 := remove_glob_e ii env e1 in
        Let e2 := remove_glob_e ii env e2 in
        ok (Papp2 o e1 e2)
      | PappN op es =>
        Let es := mapM (remove_glob_e ii env) es in
        ok (PappN op es)
      | Pif t e e1 e2 =>
        Let e := remove_glob_e ii env e in
        Let e1 := remove_glob_e ii env e1 in
        Let e2 := remove_glob_e ii env e2 in
        ok (Pif t e e1 e2)
      end.

    Definition remove_glob_lv ii (env:venv) (lv:lval) :=
      match lv with
      | Lnone _ _ => ok lv
      | Lvar xi =>
        let x := xi.(v_var) in
        if is_glob_var x then Error (rm_glob_error ii xi)
        else ok lv
      | Lmem al ws vi e =>
        Let e := remove_glob_e ii env e in
        ok (Lmem al ws vi e)
      | Laset al aa ws xi e =>
        let x := xi.(v_var) in
        if is_glob_var x then Error (rm_glob_error ii xi)
        else
          Let e := remove_glob_e ii env e in
          ok (Laset al aa ws xi e)
      | Lasub aa ws len xi e =>
        let x := xi.(v_var) in
        if is_glob_var x then Error (rm_glob_error ii xi)
        else
          Let e := remove_glob_e ii env e in
          ok (Lasub aa ws len xi e)
      end.

    Section REMOVE_C.
      Variable (remove_glob_i : venv -> instr -> cexec (venv * cmd)).

      Fixpoint remove_glob (e:venv) (c:cmd) : cexec (venv * cmd) :=
        match c with
        | [::] => ok (e, [::])
        | i::c =>
          Let envi := remove_glob_i e i in
          Let envc := remove_glob envi.1 c in
          ok (envc.1, List.app envi.2 envc.2)
        end.

    End REMOVE_C.

    Definition merge_glob (x:var) (o1 o2:option var) :=
      match o1, o2 with
      | Some g1, Some g2 => if g1 == g2 then o1 else None
      | _, _ => None
      end.

    Definition Mincl (m1 m2 : venv) :=
      all (fun xg => if Mvar.get m2 xg.1 is Some g' then xg.2 == g' else false)
        (Mvar.elements m1).

    Definition merge_env (env1 env2:venv) := Mvar.map2 merge_glob env1 env2.

    Section INSTR.

    Section Loop2.

      Variable check_c : venv -> cexec (venv * cmd).

      Fixpoint loop (n:nat) (m:venv) :=
        match n with
        | O => Error loop_iterator
        | S n =>
          Let m' := check_c m in
          if Mincl m m'.1 then ok (m, m'.2)
          else loop n (merge_env m m'.1)
        end.

      Variant check2_r :=
        | Check2_r : pexpr -> (venv * cmd) -> (venv * cmd) -> check2_r.

      Variant loop2_r :=
        | Loop2_r : pexpr -> cmd -> cmd -> venv ->loop2_r.

      Variable check_c2 : venv -> cexec check2_r.

      Fixpoint loop2 (n:nat) (m:venv) :=
        match n with
        | O => Error loop_iterator
        | S n =>
          Let cr := check_c2 m in
          let: (Check2_r e (m1,c1) (m2,c2)) := cr in
          if Mincl m m2 then ok (Loop2_r e c1 c2 m1) else loop2 n (merge_env m m2)
        end.

    End Loop2.

    Fixpoint remove_glob_i (env:venv) (i:instr) : cexec (venv * cmd) :=
      match i with
      | MkI ii i =>
        match i with
        | Cassgn lv tag ty e =>
          Let e := remove_glob_e ii env e in
          match lv with
          | Lvar xi =>
            let x := xi.(v_var) in
            if is_glob_var x then
              match e with
              | Papp1 (Oword_of_int ws) (Pconst z) =>
                if convertible ty (aword ws) && convertible (vtype x) (aword ws) then
                  Let g := find_glob ii xi gd (Gword (wrepr ws z)) in
                  ok (Mvar.set env x g, [::])
                else Error (rm_glob_error ii xi)
              | PappN (Oarray len) cells =>
                  if convertible (vtype x) (aarr U8 len) then
                    Let array := array_from_cells ii x len cells in
                    Let g := find_glob ii xi gd (Garr array) in
                    ok (Mvar.set env x g, [::])
                  else Error (rm_glob_error ii xi)
              | _ => Error (rm_glob_error ii xi)
              end
            else
              Let lv := remove_glob_lv ii env lv in
              ok (env, [::MkI ii (Cassgn lv tag ty e)])
          | _ =>
            Let lv := remove_glob_lv ii env lv in
            ok (env, [::MkI ii (Cassgn lv tag ty e)])
          end
        | Copn lvs tag o es =>
          Let lvs := mapM (remove_glob_lv ii env) lvs in
          Let es  := mapM (remove_glob_e ii env) es in
          ok (env, [::MkI ii (Copn lvs tag o es)])
        | Csyscall lvs o al es =>
          Let lvs := mapM (remove_glob_lv ii env) lvs in
          Let es  := mapM (remove_glob_e ii env) es in
          ok (env, [::MkI ii (Csyscall lvs o al es)])
        | Cassert a =>
          Let a := sndM (remove_glob_e ii env) a in
          ok (env, [::MkI ii (Cassert a)])
        | Cif e c1 c2 =>
          Let e := remove_glob_e ii env e in
          Let envc1 := remove_glob remove_glob_i env c1 in
          let env1 := envc1.1 in
          let c1   := envc1.2 in
          Let envc2 := remove_glob remove_glob_i env c2 in
          let env2 := envc2.1 in
          let c2   := envc2.2 in
          let env := merge_env env1 env2 in
          ok (env, [::MkI ii (Cif e c1 c2)])
        | Cwhile a c1 e info c2 =>
          let check_c env :=
            Let envc1 := remove_glob remove_glob_i env c1 in
            let env1 := envc1.1 in
            Let e := remove_glob_e ii env1 e in
            Let envc2 := remove_glob remove_glob_i env1 c2 in
            ok (Check2_r e envc1 envc2) in
          Let lr := loop2 check_c Loop.nb env in
          let: (Loop2_r e c1 c2 env) := lr in
          ok (env, [::MkI ii (Cwhile a c1 e info c2)])
        | Cfor xi (d,e1,e2) c =>
          if is_glob_var xi.(v_var) then Error (rm_glob_error ii xi)
          else
            Let e1 := remove_glob_e ii env e1 in
            Let e2 := remove_glob_e ii env e2 in
            let check_c env := remove_glob remove_glob_i env c in
            Let envc := loop check_c Loop.nb env in
            let: (env, c) := envc in
            ok (env, [::MkI ii (Cfor xi (d,e1,e2) c)])
        | Ccall lvs fn al es =>
          Let lvs := mapM (remove_glob_lv ii env) lvs in
          Let es  := mapM (remove_glob_e ii env) es in
          ok (env, [::MkI ii (Ccall lvs fn al es)])
        end
      end.

    End INSTR.

    Definition remove_glob_fundef (f:ufundef) :=
      let env := Mvar.empty _ in
      let check_var xi :=
        if is_glob_var xi.(v_var) then Error (rm_glob_error dummy_instr_info xi) else ok tt in
      Let _ := mapM check_var f.(f_params) in
      Let _ := mapM check_var f.(f_res) in
      Let envc := remove_glob remove_glob_i env f.(f_body) in
      ok
        {| f_info   := f.(f_info);
           f_al     := f.(f_al);
           f_tyin   := f.(f_tyin);
           f_params := f.(f_params);
           f_body   := envc.2;
           f_tyout  := f.(f_tyout);
           f_res    := f.(f_res);
           f_extra  := f.(f_extra);
        |}.
  End GD.

  Definition remove_glob_prog (p:uprog) :=
    Let gd := extend_glob_prog p in
    if uniq (map fst gd) then
      Let fs := map_cfprog (remove_glob_fundef gd) (p_funcs p) in
      ok {| p_extra := p_extra p; p_globs := gd; p_funcs := fs |}
    else Error (rm_glob_ierror "Two global declarations have the same name").

End REMOVE.

