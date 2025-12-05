From mathcomp Require Import ssreflect ssrbool.
Require Import utils expr.
Require Import compiler_util.
Require Import operators.

Module Import E.

  Definition pass : string := "extra_var_call".

  Definition ierror msg := {|
    pel_msg      := PPEstring msg;
    pel_fn       := None;
    pel_fi       := None;
    pel_ii       := None;
    pel_vi       := None;
    pel_pass     := Some pass;
    pel_internal := true
  |}.

End E.

Section ASM_OP.
Context `{asmop:asmOp}.
Context (create_var : v_kind -> string -> atype -> var_info -> var).

Definition create_fresh_var (name : string) (ty: atype): var_i :=
    let x := create_var (Reg(Normal, Direct)) name ty dummy_var_info in
    mk_var_i x.

Section Section.
Context (get_fun: funname -> option ufundef).

(* Ensure that the arguments and the destination are uniq variables. This is useful to validate the next passes *)

Definition extra_vars_call_c (extra_vars_call_i : instr -> cexec cmd) (c:cmd) :=
  Let c := mapM extra_vars_call_i c in
  ok (flatten c).

Fixpoint extra_vars_call_i (fv: Sv.t) (i:instr) : cexec cmd :=
    let 'MkI ii ir := i in
    match ir with
    | Cif e c1 c2 =>
      Let c1 := extra_vars_call_c (extra_vars_call_i fv) c1 in
      Let c2 := extra_vars_call_c (extra_vars_call_i fv) c2 in
      let i := MkI ii (Cif e c1 c2) in
      ok [::i]
    | Cwhile a c1 e ii_w c2 =>
      Let c1 := extra_vars_call_c (extra_vars_call_i fv) c1 in
      Let c2 := extra_vars_call_c (extra_vars_call_i fv) c2 in
      let i := MkI ii (Cwhile a c1 e ii_w c2) in
      ok [::i]
    | Cfor x r c =>
      Let c := extra_vars_call_c (extra_vars_call_i fv) c in
      let i := MkI ii (Cfor x r c) in
      ok [::i]
    | Ccall lvs n es =>
      match get_fun n with
      | Some (MkFun _ _ ty_in _ _ ty_out _ _) =>
        let params := map (create_fresh_var "param") ty_in in
        let xs := map (create_fresh_var "result") ty_out in
        Let _ := assert ([&& uniq (map v_var params),
                             uniq (map v_var xs),
                             disjoint fv (sv_of_list v_var params) &
                             disjoint fv (sv_of_list v_var xs)])
                          (E.ierror "create_fresh_var not fresh"%string) in
        let pre := map3 (fun ty x e => MkI ii (Cassgn (Lvar x) AT_inline ty e)) ty_in params es in
        let params := map (Plvar) params in
        let post :=  map3 (fun ty lv x => MkI ii (Cassgn lv AT_inline ty (Plvar x))) ty_out lvs xs in
        let xs := map (Lvar) xs in
        ok (pre ++ [::MkI ii (Ccall xs n params)] ++ post)
      | _ => ok [::i]
      end
    | Cassgn _ _ _ _ | Copn _ _ _ _ | Csyscall _ _ _ => ok [::i]
    end.

Definition extra_vars_call_fn (f: ufundef) : cexec ufundef :=
  let fv := vars_fd f in
  Let c := extra_vars_call_c (extra_vars_call_i fv) f.(f_body) in
  ok (with_body f c).

End Section.

Definition extra_vars_call_prog (p:_uprog) : cexec _uprog :=
  let get_f := get_fundef p.(p_funcs) in
  Let funcs := map_cfprog (extra_vars_call_fn get_f) p.(p_funcs) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End ASM_OP.
