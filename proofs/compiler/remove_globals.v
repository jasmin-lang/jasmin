(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import xseq.
Require Import compiler_util ZArith expr. 

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

  Definition find_glob (xi:var_i) (gd:glob_decls) (ws:wsize) (z:Z) := 
    let test (gv:glob_decl) := 
      if (ws == size_of_global gv.1) && (z == gv.2) then Some gv.1
      else None in 
    match myfind test gd with 
    | None => cferror (Ferr_remove_glob xi) 
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
    | Cassgn lv _ _ e =>
      match lv with
      | Lvar xi =>
        let x := xi.(v_var) in
        if is_glob x then 
          match e with
          | Pcast ws (Pconst z) => add_glob ii x gd ws z
          | _                   => cferror (Ferr_remove_glob xi)
          end
        else ok gd
      | _ => ok gd
      end
    | Copn _ _ _ _ | Ccall _ _ _ _ => ok gd
    | Cif _ c1 c2 => 
      Let gd := foldM extend_glob_i gd c1 in
      foldM extend_glob_i gd c2 
    | Cwhile c1 _ c2 => 
      Let gd := foldM extend_glob_i gd c1 in
      foldM extend_glob_i gd c2
    | Cfor _ _ c =>
      foldM extend_glob_i gd c
    end.

  Definition extend_glob_prog (p:prog) := 
    foldM (fun f gd => foldM extend_glob_i gd f.2.(f_body)) (p_globs p) (p_funcs p).

  Section GD.
    Context (gd:glob_decls).

    Fixpoint remove_glob_e (env:venv) (e:pexpr) := 
      match e with
      | Pconst _ | Pbool _ => ok e 
      | Parr_init _ _ => ok e
      | Pcast w e =>
        Let e := remove_glob_e env e in ok (Pcast w e)
      | Pvar xi =>
        let x := xi.(v_var) in
        if is_glob x then
          match Mvar.get env x with
          | Some g => ok (Pglobal g)
          | None   => cferror (Ferr_remove_glob xi) 
          end 
        else ok e
      | Pglobal g => ok e
      | Pget xi e =>
        let x := xi.(v_var) in
        if is_glob x then cferror (Ferr_remove_glob xi)  
        else
          Let e := remove_glob_e env e in
          ok (Pget xi e)
      | Pload ws xi e =>  
        let x := xi.(v_var) in
        if is_glob x then cferror (Ferr_remove_glob xi)
        else
          Let e := remove_glob_e env e in
          ok (Pload ws xi e)
      | Papp1 o e =>
        Let e := remove_glob_e env e in
        ok (Papp1 o e)
      | Papp2 o e1 e2 =>
        Let e1 := remove_glob_e env e1 in
        Let e2 := remove_glob_e env e2 in
        ok (Papp2 o e1 e2)
      | Pif e e1 e2 =>
        Let e := remove_glob_e env e in
        Let e1 := remove_glob_e env e1 in
        Let e2 := remove_glob_e env e2 in
        ok (Pif e e1 e2)
      end.
  
    Definition remove_glob_lv (env:venv) (lv:lval) := 
      match lv with
      | Lnone _ _ => ok lv
      | Lvar xi =>
        let x := xi.(v_var) in
        if is_glob x then cferror (Ferr_remove_glob xi)
        else ok lv
      | Lmem ws xi e =>
        let x := xi.(v_var) in
        if is_glob x then cferror (Ferr_remove_glob xi)
        else
          Let e := remove_glob_e env e in
          ok (Lmem ws xi e)
      | Laset xi e =>
        let x := xi.(v_var) in
        if is_glob x then cferror (Ferr_remove_glob xi)
        else
          Let e := remove_glob_e env e in
          ok (Laset xi e)
      end.
    
    Section REMOVE_C.
      Variable (remove_glob_i : venv -> instr -> cfexec (venv * cmd)).
  
      Fixpoint remove_glob (e:venv) (c:cmd) : cfexec (venv * cmd) := 
        match c with
        | [::] => ok (e, [::])
        | i::c =>
          Let envi := remove_glob_i e i in
          Let envc := remove_glob envi.1 c in
          ok (envc.1, List.app envi.2 envc.2)
        end.
  
    End REMOVE_C.
  
    Definition merge_glob (x:var) (o1 o2:option global) := 
      match o1, o2 with
      | Some g1, Some g2 => if g1 == g2 then o1 else None
      | _, _ => None
      end.
  
    Definition Mincl (m1 m2 : venv) := 
      Mvar.fold 
        (fun x g r => r && if Mvar.get m2 x is Some g' then g == g' else false) m1 true.
      
    Definition merge_env (env1 env2:venv) := Mvar.map2 merge_glob env1 env2.
  
    Section INSTR.

    Variable fn:funname.

    Section Loop2.
  
      Variable check_c : venv -> cfexec (venv * cmd).
      
      Fixpoint loop (n:nat) (m:venv) := 
        match n with
        | O => cferror (Ferr_fun fn (Cerr_Loop "remove_glob"))
        | S n =>
          Let m' := check_c m in
          if Mincl m m'.1 then ok m'
          else loop n (merge_env m m'.1)
        end.
      
      Variant check2_r := 
        | Check2_r : pexpr -> (venv * cmd) -> (venv * cmd) -> check2_r.

      Variant loop2_r := 
        | Loop2_r : pexpr -> cmd -> cmd -> venv ->loop2_r.

      Variable check_c2 : venv -> cfexec check2_r.
      
      Fixpoint loop2 (n:nat) (m:venv) := 
        match n with
        | O => cferror (Ferr_fun fn (Cerr_Loop "remove_glob"))
        | S n =>
          Let cr := check_c2 m in
          let: (Check2_r e (m1,c1) (m2,c2)) := cr in
          if Mincl m m1 then ok (Loop2_r e c1 c2 m1) else loop2 n (merge_env m m2)
        end.
  
    End Loop2.
  
    Fixpoint remove_glob_i (env:venv) (i:instr) : cfexec (venv * cmd) := 
      match i with
      | MkI ii i =>
        match i with 
        | Cassgn lv tag ty e =>
          Let e := remove_glob_e env e in
          match lv with
          | Lvar xi =>
            let x := xi.(v_var) in
            if is_glob x then 
              match e with
              | Pcast ws (Pconst z) =>
                if ty == sword ws then
                  Let g := find_glob xi gd ws z in
                  ok (env, [::])
                else cferror (Ferr_remove_glob xi)
              | _ => cferror (Ferr_remove_glob xi)
              end
            else
              Let lv := remove_glob_lv env lv in
              ok (env, [::MkI ii (Cassgn lv tag ty e)])
          | _ => 
            Let lv := remove_glob_lv env lv in
            ok (env, [::MkI ii (Cassgn lv tag ty e)])    
          end
        | Copn lvs tag o es =>
          Let lvs := mapM (remove_glob_lv env) lvs in
          Let es  := mapM (remove_glob_e env) es in
          ok (env, [::MkI ii (Copn lvs tag o es)])
        | Cif e c1 c2 =>
          Let e := remove_glob_e env e in
          Let envc1 := remove_glob remove_glob_i env c1 in
          let env1 := envc1.1 in
          let c1   := envc1.2 in
          Let envc2 := remove_glob remove_glob_i env c2 in
          let env2 := envc2.1 in
          let c2   := envc2.2 in
          let env := merge_env env1 env2 in
          ok (env, [::MkI ii (Cif e c1 c2)])
        | Cwhile c1 e c2 =>
          let check_c env := 
            Let envc1 := remove_glob remove_glob_i env c1 in
            let env1 := envc1.1 in
            Let e := remove_glob_e env1 e in
            Let envc2 := remove_glob remove_glob_i env1 c2 in
            ok (Check2_r e envc1 envc2) in
          Let lr := loop2 check_c Loop.nb env in
          let: (Loop2_r e c1 c2 env) := lr in                               
          ok (env, [::MkI ii (Cwhile c1 e c2)])
        | Cfor xi (d,e1,e2) c =>
          if is_glob xi.(v_var) then cferror (Ferr_remove_glob xi)
          else
            Let e1 := remove_glob_e env e1 in
            Let e2 := remove_glob_e env e2 in
            let check_c env := remove_glob remove_glob_i env c in 
            Let envc := loop check_c Loop.nb env in
            let: (env, c) := envc in
            ok (env, [::MkI ii (Cfor xi (d,e1,e2) c)])
        | Ccall i lvs fn es =>
          Let lvs := mapM (remove_glob_lv env) lvs in
          Let es  := mapM (remove_glob_e env) es in
          ok (env, [::MkI ii (Ccall i lvs fn es)])
        end
      end.
  
    End INSTR.
  
    Definition remove_glob_fundef (f:funname*fundef) := 
      let (fn,f) := f in
      let env := Mvar.empty _ in
      let check_var xi := 
        if is_glob xi.(v_var) then cferror (Ferr_remove_glob xi) else ok tt in
      Let _ := mapM check_var f.(f_params) in
      Let _ := mapM check_var f.(f_res) in
      Let envc := remove_glob (remove_glob_i fn) env f.(f_body) in
      ok 
        (fn, {| f_iinfo := f.(f_iinfo);
                f_tyin  := f.(f_tyin);
                f_params := f.(f_params);
                f_body   := envc.2;
                f_tyout := f.(f_tyout); 
                f_res   := f.(f_res); |}).
  End GD.

  Definition remove_glob_prog (p:prog) := 
    Let gd := extend_glob_prog p in
    Let fs := mapM (remove_glob_fundef gd) (p_funcs p) in
    ok {| p_globs := gd; p_funcs := fs |}.
     
End REMOVE.