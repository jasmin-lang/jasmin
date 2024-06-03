(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
From Coq Require Import ZArith Uint63.
Require Import gen_map expr compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "make reference arguments".

  Definition make_ref_error := pp_internal_error_s_at pass.

End E.

Section Section.
Context `{asmop:asmOp}.
Context (fresh_reg_ptr : instr_info -> int -> string -> stype -> Ident.ident).
Context (p : uprog).

Definition with_id vi ii ctr id ty :=
  {| v_var := {| vtype := ty; vname := fresh_reg_ptr ii ctr id ty |};
     v_info := vi |}.

Definition is_reg_ptr_expr doit ii ctr id ty e :=
  match e with
  | Pvar x' =>
    if doit && (is_glob x' || ~~is_reg_ptr x'.(gv)) then
      Some (with_id x'.(gv).(v_info) ii ctr id ty)
    else None
  | Psub _ _ _ x' _ =>
    if doit then Some (with_id x'.(gv).(v_info) ii ctr id ty) else None
  | _      => None
  end.

Definition is_reg_ptr_lval doit ii ctr id ty r :=
  match r with
  | Lvar x' => if doit && ~~is_reg_ptr x' then Some (with_id x'.(v_info) ii ctr id ty) else None
  | Lasub _ _ _ x' _ =>
    if doit then Some (with_id x'.(v_info) ii ctr id ty) else None
  | _      => None
  end.

Fixpoint make_prologue ii (X:Sv.t) ctr xtys es :=
  match xtys, es with
  | [::], [::] => ok ([::], [::])
  | (doit, id, ty)::xtys, e::es =>
    match is_reg_ptr_expr doit ii ctr id ty e with
    | Some y =>
      Let _ := assert (~~Sv.mem y X) (make_ref_error ii "bad fresh id (prologue)") in
      Let pes := make_prologue ii (Sv.add y X) (Uint63.succ ctr) xtys es in
      let: (p,es') := pes in 
      ok (MkI ii (Cassgn (Lvar y) AT_rename ty e) :: p, Plvar y :: es')
    | None =>
      Let pes := make_prologue ii X ctr xtys es in
      let: (p,es') := pes in
      ok (p, e::es')
    end
  | _, _ => Error (make_ref_error ii "assert false (prologue)")
  end.

Variant pseudo_instr :=
  | PI_lv of lval
  | PI_i  of lval & stype & var_i.

Fixpoint make_pseudo_epilogue (ii:instr_info) (X:Sv.t) ctr xtys rs :=
  match xtys, rs with
  | [::], [::] => ok ([::])
  | (doit, id, ty)::xtys, r::rs =>
     match is_reg_ptr_lval doit ii ctr id ty r with
     | Some y => 
       Let _ := assert (~~Sv.mem y X)
                       (make_ref_error ii "bad fresh id (epilogue)") in
       Let pis := make_pseudo_epilogue ii X (Uint63.succ ctr) xtys rs in
       ok (PI_lv (Lvar y) :: (PI_i r ty y) :: pis)
     | None =>
       Let pis :=  make_pseudo_epilogue ii X ctr xtys rs in
       ok (PI_lv r :: pis) 
     end
   | _, _ => Error (make_ref_error ii "assert false (epilogue)")
   end.

Definition mk_ep_i ii r ty y :=  MkI ii (Cassgn r AT_rename ty (Plvar y)).

Definition wf_lv (lv:lval) :=
  match lv with
  | Lnone _ _ | Lmem _ _ _ _ | Laset _ _ _ _ _ => false
  | Lvar _ => true
  | Lasub _ _ _ _ e => ~~use_mem e
  end.

Fixpoint swapable (ii:instr_info) (pis : seq pseudo_instr) := 
  match pis with
  | [::] => ok ([::], [::])
  | PI_lv lv :: pis => 
    Let lvep := swapable ii pis in
    let '(lvs,ep) := lvep in
    ok (lv::lvs, ep)
  | PI_i r ty y :: pis =>
    Let lvep := swapable ii pis in
    let: (lvs,ep) := lvep in
    let i := mk_ep_i ii r ty y in
    Let _ := assert (disjoint (read_rvs lvs) (write_I i))
                    (make_ref_error ii "cannot swap 1") in
    Let _ := assert (disjoint (vrvs lvs) (Sv.union (write_I i) (read_I i)))
                     (make_ref_error ii "cannot swap 2") in
    Let _ := assert (wf_lv r) (make_ref_error ii "cannot swap 3") in
    ok (lvs, i::ep)
  end.

Definition make_epilogue ii (X:Sv.t) xtys rs :=
  Let pis := make_pseudo_epilogue ii X 0 xtys rs in
  swapable ii pis.

Definition update_c (update_i : instr -> cexec cmd) (c:cmd) :=
  Let ls := mapM update_i c in
  ok (flatten ls).

Definition mk_info (x:var_i) (ty:stype) :=
  (is_reg_ptr x, Ident.id_name x.(vname), ty).

Definition get_sig fn :=
  if get_fundef p.(p_funcs) fn is Some fd then
        (map2 mk_info fd.(f_params) fd.(f_tyin),
         map2 mk_info fd.(f_res) fd.(f_tyout))
  else ([::], [::]).

Definition get_syscall_sig o :=
  let: s := syscall.syscall_sig_u o in
  (map (fun ty => (is_sarr ty, "__p__"%string, ty)) s.(scs_tin),
   map (fun ty => (is_sarr ty, "__p__"%string, ty)) s.(scs_tout)).

Fixpoint update_i (X:Sv.t) (i:instr) : cexec cmd :=
  let (ii,ir) := i in
  match ir with
  | Cassgn _ _ _ _ |  Copn _ _ _ _  => ok [::i]
  | Cif b c1 c2 =>
    Let c1 := update_c (update_i X) c1 in
    Let c2 := update_c (update_i X) c2 in
    ok [::MkI ii (Cif b c1 c2)]
  | Cfor x r c =>
    Let c := update_c (update_i X) c in
    ok [::MkI ii (Cfor x r c)]
  | Cwhile a c e c' =>
    Let c  := update_c (update_i X) c in
    Let c' := update_c (update_i X) c' in
    ok [::MkI ii (Cwhile a c e c')]
  | Ccall xs fn es =>
    let: (params,returns) := get_sig fn in
    Let pres := make_prologue ii X 0 params es in
    let: (prologue, es) := pres in
    Let xsep := make_epilogue ii X returns xs in
    let: (xs, epilogue) := xsep in 
    ok (prologue ++ MkI ii (Ccall xs fn es) :: epilogue)
  | Csyscall xs o es =>
    let: (params,returns) := get_syscall_sig o in
    Let: (prologue, es) := make_prologue ii X 0 params es in
    Let: (xs, epilogue) := make_epilogue ii X returns xs in
    ok (prologue ++ MkI ii (Csyscall xs o es) :: epilogue)
  end.

Definition update_fd (fd: ufundef) :=
  let body    := fd.(f_body) in
  let write   := write_c body in
  let read    := read_c  body in
  let returns := read_es (map Plvar fd.(f_res)) in
  let X := Sv.union returns (Sv.union write read) in
  Let body := update_c (update_i X) body in
  ok (with_body fd body).

Definition makereference_prog : cexec uprog :=
  Let funcs := map_cfprog update_fd p.(p_funcs) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End Section.

