(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Coq Require Import ZArith Uint63.
Require Import sopn pseudo_operator expr compiler_util.

Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "lower spilling instructions".

  Definition ii_loop_iterator := ii_loop_iterator pass.

  Definition error ii (pp : pp_error) := {|
    pel_msg := pp;
    pel_fn := None;
    pel_fi := None;
    pel_ii := Some ii;
    pel_vi := None;
    pel_pass := Some pass;
    pel_internal := false
  |}.

End E.

Section ASM_OP.

Context `{asmop : asmOp}.
Context (fresh_var_ident: v_kind -> instr_info -> int -> string -> atype -> Ident.ident).

Definition to_spill_e s e :=
  match e with
  | Pvar x => Sv.add x.(gv) s
  | _ => s
  end.

(* Compute the set for variable that are spilled *)
Fixpoint to_spill_i (s : Sv.t * bool) (i : instr) :=
  let (ii,ir) := i in
  match ir with
  | Cassgn _ _ _ _ => s
  | Copn _ _ o es =>
    match is_spill_op o with
    | Some (Spill, _) => (foldl to_spill_e s.1 es, true)
    | Some (Unspill, _) => (s.1, true)
    | _ => s
    end
  | Csyscall _ _ _ _ | Cassert _ => s
  | Cif _ c1 c2 => foldl to_spill_i (foldl to_spill_i s c1) c2
  | Cfor _ _ c => foldl to_spill_i s c
  | Cwhile _ c1 _ _ c2 => foldl to_spill_i (foldl to_spill_i s c1) c2
  | Ccall _ _ _ _ => s
  end.

Definition spill_env := Sv.t.

Definition update_lv (env : spill_env) (lv : lval) : spill_env :=
  match lv with
  | Lnone _ _ | Lmem _ _ _ _ => env
  | Lvar x | Laset _ _ _ x _ | Lasub _ _ _ x _ => Sv.remove x env
  end.

Definition update_lvs := foldl update_lv.

Definition get_Pvar ii (e : pexpr) : cexec var_i :=
  if e is Pvar {| gv := x ; gs := Slocal |} then
    ok x
  else Error (E.error ii (pp_hov [::pp_e e; pp_s "should be a variable"])).

Definition get_Pvars ii (es : pexprs) : cexec (seq var_i) :=
  mapM (get_Pvar ii) es.

Definition check_ty ii (xs : seq var_i) (tys : seq atype) :=
  assert (all2 (fun (x : var_i) ty => convertible (vtype x) ty) xs tys)
      (pp_internal_error_s_at E.pass ii "bad type for spill/unspill").

Section GET.

Context (get_spill : instr_info -> var -> cexec var).

Definition spill_x  (ii : instr_info) (env : spill_env) (x : var_i) :=
  Let sx := get_spill ii x in
  let sx := {| v_var := sx; v_info := x.(v_info) |} in
  ok (Sv.add (v_var x) env, MkI ii (Cassgn (Lvar sx) AT_none (vtype x) (Plvar x))).

Definition spill_es ii env tys es :=
  Let xs := get_Pvars ii es in
  Let _ := check_ty ii xs tys in
  fmapM (spill_x ii) env xs.

Definition unspill_x (ii : instr_info) (env : spill_env) (x : var_i) :=
  if Sv.mem (v_var x) env then
    Let sx := get_spill ii x in
    let sx := {| v_var := sx; v_info := x.(v_info) |} in
    ok (MkI ii (Cassgn (Lvar x) AT_none (vtype x) (Plvar sx)))
  else
    Error (E.error ii (pp_nobox [:: PPEbreak; pp_hov [::pp_s "The variable"; pp_var x;
            pp_s "needs to be spilled before (maybe the variable has been written since the last spill)"]])).

Definition unspill_es ii env tys es :=
  Let xs := get_Pvars ii es in
  Let _ := check_ty ii xs tys in
  mapM (unspill_x ii env) xs.

Section CMD.

  Context (spill_i : spill_env -> instr -> cexec (spill_env * cmd)).

  Fixpoint spill_c (env : spill_env) (c : cmd) : cexec (spill_env * cmd) :=
    match c with
    | [::] => ok (env, [::])
    | i::c =>
      Let ei := spill_i env i in
      Let ec := spill_c ei.1 c in
      ok (ec.1, ei.2 ++ ec.2)
  end.

End CMD.

Definition merge_env (env1 env2 : spill_env) := Sv.inter env1 env2.

Section LOOP.

  Context (spill_c : spill_env -> cmd -> cexec (spill_env * cmd)).

  Context (ii : instr_info).

  Context (c1 c2 : cmd).

  Fixpoint loop (n : nat) (env : spill_env) : cexec (spill_env * cmd) :=
    match n with
    | O => Error (E.ii_loop_iterator ii)
    | S n =>
      Let ec := spill_c env c1 in
      if Sv.subset env ec.1 then ok (env, ec.2)
      else loop n (merge_env env ec.1)
    end.

  (* while c1 e c2
     c1; while e do c2; c1
  *)

  Fixpoint wloop (n:nat) (env : Sv.t) : cexec (Sv.t * (cmd * cmd)) :=
    match n with
    | O => Error (ii_loop_iterator ii)
    | S n =>
      Let ec1 := spill_c env c1 in
      Let ec2 := spill_c ec1.1 c2 in
      if Sv.subset env ec2.1 then ok (ec1.1, (ec1.2, ec2.2))
      else wloop n (merge_env env ec2.1)
    end.

End LOOP.

Fixpoint spill_i (env : spill_env) (i : instr) : cexec (spill_env * cmd) :=
  let (ii, ir) := i in
  match ir with
  | Cassgn lv t ty e => ok (update_lv env lv, [:: i])
  | Copn lvs t o es =>
    match is_spill_op o with
    | Some (Spill, tys)   => spill_es ii env tys es
    | Some (Unspill, tys) => Let c := unspill_es ii env tys es in ok (env, c)
    | None                => ok (update_lvs env lvs, [::i])
    end
  | Csyscall lvs c _ es => ok (update_lvs env lvs, [::i])
  | Cassert _ => ok (env, [::i])
  | Cif e c1 c2 =>
    Let ec1 := spill_c spill_i env c1 in
    Let ec2 := spill_c spill_i env c2 in
    ok (merge_env ec1.1 ec2.1, [:: MkI ii (Cif e ec1.2 ec2.2)])
  | Cfor x r c =>
    Let ec := loop (spill_c spill_i) ii c Loop.nb (Sv.remove x env) in
    ok (ec.1, [:: MkI ii (Cfor x r ec.2)])
  | Cwhile a c1 e info c2 =>
    Let ec := wloop (spill_c spill_i) ii c1 c2 Loop.nb env in
    ok (ec.1, [:: MkI ii (Cwhile a ec.2.1 e info ec.2.2)])
  | Ccall lvs f _ es => ok (update_lvs env lvs, [::i])
  end.

End GET.

Section PROGT.
Context {pT: progT}.

Definition init_map (s:Sv.t) :=
  Sv.fold (fun (x:var) '(m, count) =>
    let n := vname x in         
    let k :=
      match Ident.id_kind n with
      | Reg (_, r) => 
          if Ident.spill_to_mmx n then Reg(Extra, r)
          else Stack r
      | _ => Stack Direct (* This is a dummy value, pretyping ensure this never appen *)
      end in
    let ty := vtype x in
    let n := Ident.id_name n in
    (Mvar.set m x {| vname := fresh_var_ident k dummy_instr_info count n ty; vtype := ty |}
    , succ count))
    s (Mvar.empty var, 0%uint63).

Definition get_spill (m:Mvar.t var) ii (x:var) :=
  match Mvar.get m x with
  | Some sx => ok sx
  | None => Error (E.error ii
     (pp_hov [::pp_s "The variable"; pp_var x; pp_s "needs to be spilled"]))
  end.

Definition check_map (m:Mvar.t var) X :=
  Mvar.fold (fun (x:var) (sx:var) bX =>
    (bX.1 && ~~Sv.mem sx bX.2, Sv.add sx bX.2)) m (true, X).

Definition spill_fd {eft} (fn:funname) (fd: _fundef eft) : cexec (_fundef eft) :=
  let 'MkFun ii al tyi params c tyo res ef := fd in
  let s := foldl to_spill_i (Sv.empty, false) c in
  if ~~s.2 then ok fd else
  let: (m, _) := init_map s.1 in
  let X := Sv.union (vars_l params) (Sv.union (vars_l res) (vars_c c)) in
  let b := check_map m X in
  Let _ := assert b.1 (pp_internal_error E.pass (pp_s "invalid map")) in
  Let ec := spill_c (spill_i (get_spill m)) Sv.empty c in
  ok (MkFun ii al tyi params ec.2 tyo res ef).

Definition spill_prog (p: prog) : cexec prog :=
  Let funcs := map_cfprog_name spill_fd (p_funcs p) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End PROGT.

Definition spill_uprog (p: _uprog) : cexec _uprog :=
  spill_prog (p: @prog _ _ progUnit).

End ASM_OP.
