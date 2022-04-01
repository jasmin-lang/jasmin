(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect.
Require Import gen_map expr compiler_util ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "make reference arguments".

  Definition make_ref_error := pp_internal_error_s_at pass.

End E.

Section Section.

Context `{asmop:asmOp}.
Context (is_reg_ptr : var -> bool) (fresh_id : glob_decls -> var -> Ident.ident).
Context {T} {pT:progT T}.
Context (p : prog).

Definition with_var xi x := 
  let x' := {| vtype := vtype x; vname := fresh_id (p_globs p) x |} in
  {| v_var := x'; v_info := xi.(v_info) |}.

Definition is_reg_ptr_expr x e :=
  match e with
  | Pvar x' =>
    if is_reg_ptr x && (is_glob x' || ~~is_reg_ptr x'.(gv)) then 
      Some (with_var x'.(gv) x) 
    else None
  | Psub _ _ _ x' _ =>  Some (with_var x'.(gv) x)
  | _      => None 
  end.

Definition is_reg_ptr_lval x r := 
  match r with
  | Lvar x' => if is_reg_ptr x && ~~is_reg_ptr x' then Some (with_var x' x) else None
  | Lasub _ _ _ x' _ => Some (with_var x' x)
  | _      => None 
  end.

Fixpoint make_prologue ii (X:Sv.t) xs tys es := 
  match xs, tys, es with
  | [::], [::], [::] => ok ([::], [::])
  | x::xs, ty::tys, e::es =>
    let x := x.(v_var) in
    match is_reg_ptr_expr x e with
    | Some y => 
      Let _ := assert ([&& ty == vtype y, ~~is_sbool ty & ~~Sv.mem y X ])
                      (make_ref_error ii "bad fresh id (prologue)") in
      Let pes := make_prologue ii (Sv.add y X) xs tys es in
      let: (p,es') := pes in 
      ok (MkI ii (Cassgn (Lvar y) AT_rename ty e) :: p, Plvar y :: es')
    | None =>
      Let pes := make_prologue ii X xs tys es in
      let: (p,es') := pes in
      ok (p, e::es')
    end
  | _, _, _ => Error (make_ref_error ii "assert false (prologue)")
  end.

Variant pseudo_instr :=
  | PI_lv of lval
  | PI_i  of lval & stype & var_i.

Fixpoint make_pseudo_epilogue (ii:instr_info) (X:Sv.t) xs tys rs := 
  match xs, tys, rs with
  | [::], [::], [::] => ok ([::])
  | x::xs, ty::tys, r::rs =>
    let x := x.(v_var) in
     match is_reg_ptr_lval x r with
     | Some y => 
       Let _ := assert ([&& ty == vtype y, ~~is_sbool ty & ~~Sv.mem y X ])
                       (make_ref_error ii "bad fresh id (epilogue)") in
       Let pis := make_pseudo_epilogue ii X xs tys rs in
       ok (PI_lv (Lvar y) :: (PI_i r ty y) :: pis)
     | None =>
       Let pis :=  make_pseudo_epilogue ii X xs tys rs in
       ok (PI_lv r :: pis) 
     end
   | _, _, _ => Error (make_ref_error ii "assert false (epilogue)")
   end.

Definition mk_ep_i ii r ty y :=  MkI ii (Cassgn r AT_rename ty (Plvar y)).

Fixpoint noload (e:pexpr) := 
  match e with
  | Pload _ _ _ => false 
  | Pconst _ | Pbool _ | Parr_init _ | Pvar _ => true
  | Pget _ _ _ e | Psub _ _ _ _ e | Papp1 _ e => noload e
  | Papp2 _ e1 e2 => noload e1 && noload e2 
  | PappN _ es => all noload es 
  | Pif _ e1 e2 e3 => [&& noload e1, noload e2 & noload e3]
  end.

Definition wf_lv (lv:lval) :=
  match lv with
  | Lnone _ _ | Lmem _ _ _ | Laset _ _ _ _ => false 
  | Lvar _ => true 
  | Lasub _ _ _ _ e => noload e
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

Definition make_epilogue ii (X:Sv.t) xs tys rs := 
  Let pis := make_pseudo_epilogue ii X xs tys rs in
  swapable ii pis.

Definition update_c (update_i : instr -> cexec cmd) (c:cmd) :=
  Let ls := mapM update_i c in
  ok (flatten ls).

Fixpoint update_i (get_sig : funname -> seq var_i * seq stype * seq var_i * seq stype) 
                  (X:Sv.t) (i:instr) : cexec cmd :=
  let (ii,ir) := i in
  match ir with
  | Cassgn _ _ _ _ |  Copn _ _ _ _ => 
    ok [::i]
  | Cif b c1 c2 =>
    Let c1 := update_c (update_i get_sig X) c1 in
    Let c2 := update_c (update_i get_sig X) c2 in
    ok [::MkI ii (Cif b c1 c2)]
  | Cfor x r c =>
    Let c := update_c (update_i get_sig X) c in
    ok [::MkI ii (Cfor x r c)]
  | Cwhile a c e c' =>
    Let c  := update_c (update_i get_sig X) c in
    Let c' := update_c (update_i get_sig X) c' in
    ok [::MkI ii (Cwhile a c e c')]
  | Ccall ini xs fn es =>
    let: (params,tparams,returns,treturns) := get_sig fn in
    Let pres := make_prologue ii X params tparams es in
    let: (prologue, es) := pres in
    Let xsep := make_epilogue ii X returns treturns xs in
    let: (xs, epilogue) := xsep in 
    ok (prologue ++ MkI ii (Ccall ini xs fn es) :: epilogue)
  end.

Definition update_fd (get_sig : funname -> seq var_i * seq stype * seq var_i * seq stype) (fd: fundef) :=
  let body    := fd.(f_body) in
  let write   := write_c body in
  let read    := read_c  body in
  let returns := read_es (map Plvar fd.(f_res)) in
  let X := Sv.union returns (Sv.union write read) in
  Let body := update_c (update_i get_sig X) body in
  ok (with_body fd body).

Definition get_sig (p:prog) n :=
  if get_fundef p.(p_funcs) n is Some fd then
        (fd.(f_params), fd.(f_tyin), fd.(f_res), fd.(f_tyout))
  else ([::], [::], [::], [::]).

Definition makereference_prog : cexec prog :=
  Let funcs := map_cfprog (update_fd (get_sig p)) p.(p_funcs) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End Section.

