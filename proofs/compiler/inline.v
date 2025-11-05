(* ** Imports and settings *)
From Coq Require Import ZArith Uint63.
From mathcomp Require Import ssreflect ssrfun ssrbool.
Require Import expr compiler_util allocation.

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
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {asmop:asmOp asm_op}
  (fresh_var_ident  : v_kind -> int -> string -> atype -> Ident.ident)
  (rename_fd : instr_info -> funname -> ufundef -> ufundef)
  (dead_vars_fd : ufun_decl -> instr_info -> Sv.t)
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

Definition locals fd :=
  Sv.diff (locals_p fd) (sparams fd).

Definition check_rename (fn:funname) (fd1 fd2:ufundef) (s:Sv.t) :=
(*   Let _ := check_ufundef dead_vars_fd tt tt (f,fd1) (f,fd2) tt in *)
  let s2 := locals_p fd2 in
  if disjoint s s2 then ok tt
  else Error (inline_error (pp_s "invalid refreshing in function")).

Definition get_fun (p:ufun_decls) (f:funname) :=
  match get_fundef p f with
  | Some fd => ok fd
  | None    => Error (inline_error (pp_box [::pp_s "Unknown function"; PPEfunname f]))
  end.

Section SUBST.

Record subst_map := {
  m : Mvar.t var;
  counter : int;
}.
Definition empty_sm := {|
  m := Mvar.empty _;
  counter := 0;
|}.

Definition mon A := subst_map -> subst_map * A.

Definition ret {A} (x: A) : mon A := fun sm => (sm, x).
Definition bind {A B} (x : mon A) (f : A -> mon B) : mon B :=
  fun sm =>
    let (sm, x) := x sm in
    f x sm.
Notation "'let%m' x ':=' m 'in' body" := (bind m (fun x => body)) (x name, at level 25) : result_scope.
Definition mapm {A B} (f : A -> mon B) (l : seq A) : mon (seq B) :=
  fun sm => fmap (fun sm x => f x sm) sm l.

Fixpoint subst_al (f: length_var -> array_length) al :=
  match al with
  | ALConst _ => al
  | ALVar x => f x
  | ALAdd al1 al2 =>
    let al1 := subst_al f al1 in
    let al2 := subst_al f al2 in
    ALAdd al1 al2
  | ALMul al1 al2 =>
    let al1 := subst_al f al1 in
    let al2 := subst_al f al2 in
    ALMul al1 al2
  end.
Definition subst_ty f ty :=
  match ty with
  | aarr ws al =>
    let al := subst_al f al in
    aarr ws al
  | _ => ty
  end.
Definition clone_with_ty (x:var) n ty :=
  let xn :=
    fresh_var_ident (Ident.id_kind x.(vname)) n (Ident.id_name x.(vname)) ty
  in
  {| vtype := ty; vname := xn |}.
Definition subst_var f x : mon _ := fun sm =>
  match Mvar.get sm.(m) x with
  | Some y => (sm, y)
  | None =>
    let y := clone_with_ty x sm.(counter) (subst_ty f x.(vtype)) in
    let m := Mvar.set sm.(m) x y in
    let sm := {| m := m; counter := Uint63.succ sm.(counter) |} in
    (sm, y)
  end.
Definition subst_var_i f x :=
  let%m v := subst_var f x.(v_var) in
  ret {| v_var := v; v_info := x.(v_info) |}.
Definition subst_gvar f x :=
  if is_glob x then ret x
  else
    let%m xv := subst_var_i f x.(gv) in
    ret {| gv := xv; gs := x.(gs) |}.

Fixpoint subst_e f e :=
  match e with
  | Pconst _ | Pbool _ => ret e
  | Parr_init ws al =>
    let al := subst_al f al in
    ret (Parr_init ws al)
  | Pvar x =>
    let%m x := subst_gvar f x in
    ret (Pvar x)
  | Pget al aa ws x e =>
    let%m x := subst_gvar f x in
    let%m e := subst_e f e in
    ret (Pget al aa ws x e)
  | Psub aa ws len x e =>
    let len := subst_al f len in
    let%m x := subst_gvar f x in
    let%m e := subst_e f e in
    ret (Psub aa ws len x e)
  | Pload al ws e =>
    let%m e := subst_e f e in
    ret (Pload al ws e)
  | Papp1 op e =>
    let%m e := subst_e f e in
    ret (Papp1 op e)
  | Papp2 op e1 e2 =>
    let%m e1 := subst_e f e1 in
    let%m e2 := subst_e f e2 in
    ret (Papp2 op e1 e2)
  | PappN o es =>
    let%m es := mapm (subst_e f) es in
    ret (PappN o es)
  | Pif t e e1 e2 =>
    let t := subst_ty f t in
    let%m e := subst_e f e in
    let%m e1 := subst_e f e1 in
    let%m e2 := subst_e f e2 in
    ret (Pif t e e1 e2)
  end.
Definition subst_es f := mapm (subst_e f).

Definition subst_lval f lv :=
  match lv with
  | Lnone vi ty =>
    let ty := subst_ty f ty in
    ret (Lnone vi ty)
  | Lvar x =>
    let%m x := subst_var_i f x in
    ret (Lvar x)
  | Lmem al ws vi e =>
    let%m e := subst_e f e in
    ret (Lmem al ws vi e)
  | Laset al aa ws x e =>
    let%m x := subst_var_i f x in
    let%m e := subst_e f e in
    ret (Laset al aa ws x e)
  | Lasub aa ws len x e =>
    let len := subst_al f len in
    let%m x := subst_var_i f x in
    let%m e := subst_e f e in
    ret (Lasub aa ws len x e)
  end.
Definition subst_lvals f := mapm (subst_lval f).

Fixpoint subst_i f (i:instr) : mon instr :=
  let (ii,ir) := i in
  match ir with
  | Copn xs tg op es =>
    (* TODO: subst in op too *)
    let%m xs := subst_lvals f xs in
    let%m es := subst_es f es in
    ret (MkI ii (Copn xs tg op es))
  | Cassgn x tg ty e =>
    let%m x := subst_lval f x in
    let ty := subst_ty f ty in
    let%m e := subst_e f e in
    ret (MkI ii (Cassgn x tg ty e))
  | Cif b c1 c2 =>
    let%m b := subst_e f b in
    let%m c1 := mapm (subst_i f) c1 in
    let%m c2 := mapm (subst_i f) c2 in
    ret (MkI ii (Cif b c1 c2))
  | Cfor x r c =>
    let%m x := subst_var_i f x in
    let%m r12 := subst_e f r.1.2 in
    let%m r2 := subst_e f r.2 in
    let r := (r.1.1, r12, r2) in
    let%m c := mapm (subst_i f) c in
    ret (MkI ii (Cfor x r c))
  | Cwhile a c e info c' =>
    let%m c := mapm (subst_i f) c in
    let%m e := subst_e f e in
    let%m c' := mapm (subst_i f) c' in
    ret (MkI ii (Cwhile a c e info c'))
  | Ccall xs fn alargs es =>
    let%m xs := subst_lvals f xs in
    let alargs := map (subst_al f) alargs in
    let%m es := subst_es f es in
    ret (MkI ii (Ccall xs fn alargs es))
  | Csyscall xs o es =>
    (* TODO: subst in o too *)
    let%m xs := subst_lvals f xs in
    let%m es := subst_es f es in
    ret (MkI ii (Csyscall xs o es))
  end.
Definition subst_c f := mapm (subst_i f).

Definition subst_fd f (fd:ufundef) :=
  let%m params := mapm (subst_var_i f) fd.(f_params) in
  let%m res := mapm (subst_var_i f) fd.(f_res) in
  let%m body := subst_c f fd.(f_body) in
  ret
    {| f_info := fd.(f_info);
       f_al := [::];
       f_tyin := map (subst_ty f) fd.(f_tyin);
       f_params := params;
       f_body := body;
       f_tyout := map (subst_ty f) fd.(f_tyout);
       f_res := res;
       f_extra := fd.(f_extra) |}.

End SUBST.

Fixpoint inline_i (p:ufun_decls) (i:instr) (X:Sv.t) : cexec (Sv.t * cmd) :=
  let '(MkI iinfo ir) := i in
  match ir with
  | Cassgn _ _ _ _
  | Copn _ _ _ _
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
  | Ccall xs fn alargs es =>
    (* we have to substitute f_al with alargs and to clone the function to
       avoid collisions, in that order or the other one.
       But we cannot change the type of variables on Coq side, so we have
       to call some OCaml code at some point. *)
    let X := Sv.union (read_i ir) X in
    if ii_is_inline iinfo then
      Let fd := add_iinfo iinfo (get_fun p fn) in
      let f :=
        let als := zip fd.(f_al) alargs in
        fun x => odflt (ALVar x) (assoc als x)
      in
      let (_, fd') := subst_fd f fd empty_sm in
      (* no real need to rename, but it changes the instr_info, so we keep it *)
      let fd' := rename_fd iinfo fn fd' in
      Let _ := add_iinfo iinfo (check_rename fn fd fd' (Sv.union (vrvs xs) X)) in
      let ii := ii_with_location iinfo in
      let rename_args :=
        assgn_tuple ii (map Lvar fd'.(f_params)) AT_rename fd'.(f_tyin) es
      in
      let rename_res :=
        assgn_tuple ii xs AT_rename fd'.(f_tyout) (map Plvar fd'.(f_res))
      in
      let c := rename_args ++ fd'.(f_body) ++ rename_res in
      ok (X, c)
    else ok (X, [::i])
  end.

Definition inline_fd (p:ufun_decls) (fd:ufundef) :=
  match fd with
  | MkFun ii al tyin params c tyout res ef =>
    let s := read_es (map Plvar res) in
    Let c := inline_c (inline_i p) c s in
    ok (MkFun ii al tyin params c.2 tyout res ef)
  end.

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
