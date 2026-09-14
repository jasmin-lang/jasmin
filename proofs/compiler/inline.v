(* ** Imports and settings *)
From Coq Require Import ZArith Uint63.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import expr compiler_util.

Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "inlining".

  Definition inline_error msg := {|
    pel_msg := msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := None;
    pel_pass := Some pass;
    pel_internal := true
  |}.

End E.

(* ** inlining
 * -------------------------------------------------------------------- *)

Section INLINE.

Context
  {asm_op syscall_state : Type}
  {asmop:asmOp asm_op}
  (fresh_var_ident  : v_kind -> int -> string -> atype -> Ident.ident)
  (extend_iinfo : instr_info -> instr_info -> instr_info)
.

Definition get_flag (x:lval) flag :=
  match x with
  | Lvar x => if is_inline_var x then AT_inline else flag
  | _      => flag
  end.

Definition assgn_tuple iinfo (xs:lvals) flag (tys:seq atype) (es:pexprs) :=
  let assgn xe := MkI iinfo (Cassgn xe.1 (get_flag xe.1 flag) xe.2.1 xe.2.2) in
  map assgn (zip xs (zip tys es)).

Definition inline_c (inline_i: instr -> Sv.t -> cexec (Sv.t * cmd)) c s :=
  foldr (fun i r =>
    Let r := r in
    Let ri := inline_i i r.1 in
    ok (ri.1, ri.2 ++ r.2)) (ok (s,[::])) c.

Definition sparams (fd:ufundef) :=
  vrvs_rec Sv.empty (map Lvar fd.(f_params)).

Definition locals_p (fd:ufundef) :=
  let s := read_es (map Plvar fd.(f_res)) in
  let w := write_c_rec s fd.(f_body) in
  let r := read_c_rec w fd.(f_body) in
  vrvs_rec r (map Lvar fd.(f_params)).

Definition check_disjoint (fd:ufundef) (s:Sv.t) :=
  let s2 := locals_p fd in
  if disjoint s s2 then ok tt
  else Error (inline_error (pp_s "invalid refreshing in function")).

Definition get_fun (p:ufun_decls) (f:funname) :=
  match get_fundef p f with
  | Some fd => ok fd
  | None    => Error (inline_error (pp_box [::pp_s "Unknown function"; PPEfunname f]))
  end.

Fixpoint extend_iinfo_i ii i : instr :=
  let '(MkI iinfo ir) := i in
  let ir :=
    match ir with
    | Cassgn _ _ _ _
    | Copn _ _ _ _ _
    | Csyscall _ _ _
    | Cassert _
    | Ccall _ _ _ _ => ir
    | Cif e c1 c2 =>
      Cif e (map (extend_iinfo_i ii) c1) (map (extend_iinfo_i ii) c2)
    | Cfor x (d,lo,hi) c =>
      Cfor x (d,lo,hi) (map (extend_iinfo_i ii) c)
    | Cwhile a c e info c' =>
      Cwhile a (map (extend_iinfo_i ii) c) e info (map (extend_iinfo_i ii) c')
    end
  in
  let iinfo := extend_iinfo ii iinfo in
  MkI iinfo ir.

Definition extend_iinfo_cmd ii c := map (extend_iinfo_i ii) c.

Section SUBST.

Record subst_map := {
  m : Mvar.t var;
  vars : Sv.t; (* to check for freshness of variables *)
  counter : int;
}.
Definition empty_sm := {|
  m := Mvar.empty _;
  vars := Sv.empty;
  counter := 0;
|}.

(*
Definition mon A := subst_map -> cexec (subst_map * A).

Definition ret {A} (x: A) : mon A := fun sm => ok (sm, x).
Definition bind {A B} (x : mon A) (f : A -> mon B) : mon B :=
  fun sm =>
    Let: (sm, x) := x sm in
    f x sm.
Notation "'let%m' x ':=' m 'in' body" := (bind m (fun x => body)) (x name, at level 25) : result_scope.
Definition mapm {A B} (f : A -> mon B) (l : seq A) : mon (seq B) :=
  fun sm => fmapM (fun sm x => f x sm) sm l.
*)

Definition clone_with_ty (x:var) n ty :=
  let xn :=
    fresh_var_ident (Ident.id_kind x.(vname)) n (Ident.id_name x.(vname)) ty
  in
  {| vtype := ty; vname := xn |}.

Definition subst_al_err f al :=
  o2r (inline_error (pp_s "subst_al: failed substitution")) (subst_al f al).

Definition subst_ty_err f ty :=
  o2r (inline_error (pp_s "subst_ty: failed substitution")) (subst_ty f ty).

Fixpoint no_var_al (al : array_length) :=
  match al with
  | ALConst _ => true
  | ALVar _ _ => false
  | ALNeg al => no_var_al al
  | ALAdd al1 al2
  | ALSub al1 al2
  | ALMul al1 al2
  | ALDiv _ al1 al2
  | ALMod _ al1 al2
  | ALShl al1 al2
  | ALShr al1 al2 => no_var_al al1 && no_var_al al2
  end.

Definition no_var_ty ty :=
  match ty with
  | aarr _ al => no_var_al al
  | _ => true
  end.

Definition sm_add_var f sm x :=
  let ty := x.(vtype) in
  if no_var_ty ty then
    ok sm
  else
    Let ty := subst_ty_err f x.(vtype) in
    let y := clone_with_ty x sm.(counter) ty in
    Let _ := assert (~~ Sv.mem y sm.(vars)) (inline_error (pp_s "subst_var: not fresh")) in
    let sm := {| m := Mvar.set sm.(m) x y; vars := Sv.add y sm.(vars); counter := Uint63.succ sm.(counter) |} in
    ok sm.

Definition subst_var sm x :=
  match Mvar.get sm.(m) x with
  | Some y => y
  | None => x
  end.

Definition subst_var_i sm x :=
  let v := subst_var sm x.(v_var) in
  {| v_var := v; v_info := x.(v_info) |}.

Definition subst_gvar sm x :=
  if is_glob x then
    Let _ := assert (no_var_ty x.(gv).(vtype)) (inline_error (pp_s "get_gsubst: global with non-const length")) in
    ok x
  else
    let xv := subst_var_i sm x.(gv) in
    ok {| gv := xv; gs := x.(gs) |}.

Fixpoint subst_e f sm e :=
  match e with
  | Pconst _ | Pbool _ => ok e
  | Parr_init ws al =>
    Let al := subst_al_err f al in
    ok (Parr_init ws al)
  | Pvar x =>
    Let x := subst_gvar sm x in
    ok (Pvar x)
  | Pget al aa ws x e =>
    Let x := subst_gvar sm x in
    Let e := subst_e f sm e in
    ok (Pget al aa ws x e)
  | Psub aa ws len x e =>
    Let len := subst_al_err f len in
    Let x := subst_gvar sm x in
    Let e := subst_e f sm e in
    ok (Psub aa ws len x e)
  | Pload al ws e =>
    Let e := subst_e f sm e in
    ok (Pload al ws e)
  | Papp1 op e =>
    Let e := subst_e f sm e in
    ok (Papp1 op e)
  | Papp2 op e1 e2 =>
    Let e1 := subst_e f sm e1 in
    Let e2 := subst_e f sm e2 in
    ok (Papp2 op e1 e2)
  | PappN o es =>
    Let es := mapM (subst_e f sm) es in
    ok (PappN o es)
  | Pif t e e1 e2 =>
    Let t := subst_ty_err f t in
    Let e := subst_e f sm e in
    Let e1 := subst_e f sm e1 in
    Let e2 := subst_e f sm e2 in
    ok (Pif t e e1 e2)
  end.
Definition subst_es f sm := mapM (subst_e f sm).

Definition subst_lval f sm lv :=
  match lv with
  | Lnone vi ty =>
    Let ty := subst_ty_err f ty in
    ok (Lnone vi ty)
  | Lvar x =>
    let x := subst_var_i sm x in
    ok (Lvar x)
  | Lmem al ws vi e =>
    Let e := subst_e f sm e in
    ok (Lmem al ws vi e)
  | Laset al aa ws x e =>
    let x := subst_var_i sm x in
    Let e := subst_e f sm e in
    ok (Laset al aa ws x e)
  | Lasub aa ws len x e =>
    Let len := subst_al_err f len in
    let x := subst_var_i sm x in
    Let e := subst_e f sm e in
    ok (Lasub aa ws len x e)
  end.
Definition subst_lvals f sm := mapM (subst_lval f sm).

Fixpoint subst_a f sm (a : eassert) : result _ eassert :=
  match a with
  | Pexpr e =>
    Let e := subst_e f sm e in
    ok (Pexpr e)
  | PappN_safety o es =>
    Let es := subst_es f sm es in
    ok (PappN_safety o es)
  | Pis_var_init _ => ok a
  | Pis_mem_init e1 e2 =>
    Let e1 := subst_e f sm e1 in
    Let e2 := subst_e f sm e2 in
    ok (Pis_mem_init e1 e2)
  | Pand a1 a2 =>
    Let a1 := subst_a f sm a1 in
    Let a2 := subst_a f sm a2 in
    ok (Pand a1 a2)
  end.

Fixpoint subst_i f sm (i:instr) : result _ instr :=
  let (ii,ir) := i in
  match ir with
  | Copn xs tg op als es =>
    Let es := subst_es f sm es in
    Let als := mapM (subst_al_err f) als in
    Let xs := subst_lvals f sm xs in
    ok (MkI ii (Copn xs tg op als es))
  | Cassgn x tg ty e =>
    Let e := subst_e f sm e in
    Let ty := subst_ty_err f ty in
    Let x := subst_lval f sm x in
    ok (MkI ii (Cassgn x tg ty e))
  | Cif b c1 c2 =>
    Let b := subst_e f sm b in
    Let c1 := mapM (subst_i f sm) c1 in
    Let c2 := mapM (subst_i f sm) c2 in
    ok (MkI ii (Cif b c1 c2))
  | Cfor x r c =>
    let x := subst_var_i sm x in
    Let r12 := subst_e f sm r.1.2 in
    Let r2 := subst_e f sm r.2 in
    let r := (r.1.1, r12, r2) in
    Let c := mapM (subst_i f sm) c in
    ok (MkI ii (Cfor x r c))
  | Cwhile a c e info c' =>
    Let c := mapM (subst_i f sm) c in
    Let e := subst_e f sm e in
    Let c' := mapM (subst_i f sm) c' in
    ok (MkI ii (Cwhile a c e info c'))
  | Ccall xs fn alargs es =>
    Let es := subst_es f sm es in
    Let alargs := mapM (subst_al_err f) alargs in
    Let xs := subst_lvals f sm xs in
    ok (MkI ii (Ccall xs fn alargs es))
  | Csyscall xs o es =>
    Let es := subst_es f sm es in
    Let xs := subst_lvals f sm xs in
    ok (MkI ii (Csyscall xs o es))
  | Cassert (lbl, a) =>
    Let a := subst_a f sm a in
    ok (MkI ii (Cassert (lbl, a)))
  end.
Definition subst_c f sm := mapM (subst_i f sm).

Definition create_sm f X :=
  Let sm :=
    Sv.fold (fun x acc =>
      Let acc := acc in
      Let sm := sm_add_var f acc x in
      ok sm) X (ok empty_sm) in
  ok sm.

(* FIXME: locals_p vs vars_fd? *)
Definition subst_fd f (fd:ufundef) :=
  let X := locals_p fd in
  Let sm := create_sm f X in
  Let _ := assert (disjoint X sm.(vars))
                  (inline_error (pp_s "invalid refreshing in function"))
  in
  Let tyin := mapM (subst_ty_err f) fd.(f_tyin) in
  let params := map (subst_var_i sm) fd.(f_params) in
  Let body := subst_c f sm fd.(f_body) in
  Let tyout := mapM (subst_ty_err f) fd.(f_tyout) in
  let res := map (subst_var_i sm) fd.(f_res) in
  ok
    {| f_info := fd.(f_info);
       f_contract := fd.(f_contract); (* FIXME: is this correct? *)
       f_al := [::];
       f_tyin := tyin;
       f_params := params;
       f_body := body;
       f_tyout := tyout;
       f_res := res;
       f_extra := fd.(f_extra) |}.

End SUBST.

Fixpoint inline_i (p:ufun_decls) (i:instr) (X:Sv.t) : cexec (Sv.t * cmd) :=
  let '(MkI iinfo ir) := i in
  match ir with
  | Cassgn _ _ _ _
  | Copn _ _ _ _ _
  | Csyscall _ _ _
  | Cassert _
    => ok (Sv.union (read_i ir) X, [::i])
  | Cif e c1 c2  =>
    Let c1 := inline_c (inline_i p) c1 X in
    Let c2 := inline_c (inline_i p) c2 X in
    ok (read_e_rec (Sv.union c1.1 c2.1) e, [::MkI iinfo (Cif e c1.2 c2.2)])
  | Cfor x (d,lo,hi) c =>
    let X := Sv.union (read_i ir) X in
    Let c := inline_c (inline_i p) c X in
    ok (X, [::MkI iinfo (Cfor x (d, lo, hi) c.2)])
  | Cwhile a c e info c' =>
    let X := Sv.union (read_i ir) X in
    Let c := inline_c (inline_i p) c X in
    Let c' := inline_c (inline_i p) c' X in
    ok (X, [::MkI iinfo (Cwhile a c.2 e info c'.2)])
  | Ccall xs fn als es =>
    let X := Sv.union (read_i ir) X in
    if ii_is_inline iinfo then
      (* FIXME: update comment? *)
      (* we no longer rename the variables occurring in [fd], we rely on the
         compiler ensuring variable names are disjoint between functions *)
      Let fd := add_iinfo iinfo (get_fun p fn) in
      let f :=
        let als := zip (map fst fd.(f_al)) als in
        assoc als
      in
      (* FIXME: optim: when fd.(f_al) = [::], no subst *)
      Let fd' := subst_fd f fd in
      (* FIXME: why Sv.union (vrvs xs) while X already contains things about xs ? *)
      Let _ := add_iinfo iinfo (check_disjoint fd' (Sv.union (vrvs xs) X)) in
      let ii := ii_with_location iinfo in
      let rename_args :=
        assgn_tuple ii (map Lvar fd'.(f_params)) AT_rename fd'.(f_tyin) es
      in
      let body :=
        extend_iinfo_cmd iinfo fd'.(f_body)
      in
      let rename_res :=
        assgn_tuple ii xs AT_rename fd'.(f_tyout) (map Plvar fd'.(f_res))
      in
      ok (X, rename_args ++ body ++ rename_res)
    else ok (X, [::i])
  end.

Definition inline_fd (p:ufun_decls) (fd:ufundef) :=
  let s := read_es (map Plvar fd.(f_res)) in
  Let c := inline_c (inline_i p) fd.(f_body) s in
  ok (with_body fd c.2).

Definition inline_fd_cons (ffd:funname * ufundef) (p:cexec ufun_decls) :=
  Let p := p in
  let f := ffd.1 in
  Let fd := add_funname f (add_finfo ffd.2.(f_info) (inline_fd p ffd.2)) in
  ok ((f,fd):: p).

Definition inline_prog (p:ufun_decls) :=
  foldr inline_fd_cons (ok [::]) p.

Definition inline_prog_err (p:uprog) :=
  if uniq [seq x.1 | x <- p_funcs p] then
    Let fds := inline_prog (p_funcs p) in
    ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := fds |}
  else Error (inline_error (pp_s "two function declarations with the same name")).

End INLINE.
