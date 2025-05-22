(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Import expr sem_op_typed compiler_util.
Require Export safety_shared.
Import Utf8.
Import oseq.
Require Import flag_combination.
Import pseudo_operator.

Local Open Scope seq_scope.
Local Open Scope Z_scope.


Module Import E.

  Definition pass : string := "wint_to_int".

  Definition ierror_s := pp_internal_error_s pass.

  Definition ierror := pp_internal_error pass.

  Definition ierror_e e :=
    ierror (pp_nobox [:: pp_s "ill typed expression"; pp_e e]).

  Definition pp_user_error (pp : pp_error) :=
    {| pel_msg := pp; pel_fn := None; pel_fi := None; pel_ii := None; pel_vi := None;
       pel_pass := Some pass; pel_internal := false |}.

  Definition error_e msg e :=
    pp_user_error (pp_nobox [:: pp_s msg; pp_e e]).

  Definition ierror_lv lv :=
    ierror (pp_nobox [:: pp_s "ill typed left value"; pp_lv lv]).

End E.

Section WITH_PARAMS.

Context `{asmop:asmOp} {msfsz : MSFsize} {pd: PointerData}.

Definition sc_op1 := sc_op1 (fun _ _ e => e).

Definition sc_op2 o e1 e2 :=
  match is_wi2 o with
  | Some (sg, sz, o) => sc_wiop2 sg sz o e1 e2
  | _ => [::]
  end.

#[local]
Existing Instance progUnit.

Definition wi2i_op2 (o : sop2) : sop2 :=
  match is_wi2 o with
  | Some (s, sz, op) =>
    match op with
    | WIadd => Oadd Op_int
    | WImul => Omul Op_int
    | WIsub => Osub Op_int
    | WIdiv => Odiv s Op_int
    | WImod => Omod s Op_int
    | WIshl => Olsl Op_int
    | WIshr => Oasr Op_int
    | WIeq  => Oeq  Op_int
    | WIneq => Oneq Op_int
    | WIlt  => Olt  Cmp_int
    | WIle  => Ole  Cmp_int
    | WIgt  => Ogt  Cmp_int
    | WIge  => Oge  Cmp_int
    end
  | None => o
  end.

Definition wi2i_op1_e (o : sop1) (e : pexpr) :=
  match is_wi1 o with
  | Some (s, o) =>
    match o with
    | WIwint_of_int ws => e
    | WIint_of_wint ws => e
    | WIword_of_wint ws =>
      (* We use WIwint_of_int to remember that the int argument is bounded,
         this allows to simplify int_of_word (WIword_of_int i) into i during extraction
         of memory address *)
      Papp1 (Owi1 s (WIwint_of_int ws)) e
    | WIwint_of_word ws => Papp1 (Oint_of_word s ws) e
    | WIwint_ext szo szi =>
      if (szi <= szo)%CMP then e
      else
      Papp1 (Oint_of_word s szo)
       (Papp1 (signed (Ozeroext szo szi) (Osignext szo szi) s)
         (Papp1 (Oword_of_int szi) e))

    | WIneg ws => Papp1 (Oneg Op_int) e
    end
  | None => Papp1 o e
  end.

Definition wi2i_op2_e (o : sop2) (e1 e2 : pexpr) :=
  let o := wi2i_op2 o in
  Papp2 o e1 e2.

Section Section.

Context (m: var -> option (signedness * var)).
Context (FV: Sv.t).

Definition wi2i_var (x:var) :=
  match m x with
  | Some (_, xi) => xi
  | None => x
  end.

Definition in_FV_var (x:var) :=
 Sv.mem x FV.

Definition wi2i_vari (x:var_i) :=
  Let _ := assert (in_FV_var x) (E.ierror_e (Plvar x)) in
  ok {|v_var := wi2i_var x; v_info := v_info x |}.

Definition wint_contract_condition (x:var_i) :=
  Let xi := wi2i_vari x in
  match m x.(v_var) , x.(v_var).(vtype) with
  | Some (s,_) , aword sz  =>
    ok [::(safety_lbl,  sc_wi_range s sz (Plvar xi))]
  | _ , _ => ok [::]
  end.

Definition wi2i_gvar (x: gvar) :=
  if is_lvar x then
    Let xi := wi2i_vari (gv x) in
    ok (mk_lvar xi)
  else ok x.

Definition wi2i_type (sg : option signedness) ty :=
  if sg == None then ty else aint.

Definition safety_cond := seq pexpr.

Definition wi2i_es (wi2i_e : pexpr -> cexec (safety_cond * pexpr)) (es : pexprs) : cexec (safety_cond * pexprs) :=
  Let es := mapM wi2i_e es in
  ok (flatten (unzip1 es), unzip2 es).

Fixpoint wi2i_e (e0:pexpr) : cexec (safety_cond * pexpr) :=
  match e0 with
  | Pconst _ | Pbool _ | Parr_init _ _ => ok ([::], e0)

  | Pvar x =>
    Let x := wi2i_gvar x in
    ok ([::], Pvar x)

  | Pget al aa ws x e =>
    Let _ := assert (sign_of_expr m e == None)
                    (E.ierror_e e0) in
    Let x := wi2i_gvar x in
    Let e := wi2i_e e in
    ok (e.1, Pget al aa ws x e.2)

  | Psub al ws len x e =>
    Let _ := assert (sign_of_expr m e == None)
                    (E.ierror_e e0) in
    Let x := wi2i_gvar x in
    Let e := wi2i_e e in
    ok (e.1, Psub al ws len x e.2)

  | Pload al ws e =>
    Let _ := assert (sign_of_expr m e == None)
                    (E.ierror_e e0) in
    Let e := wi2i_e e in
    ok (e.1, Pload al ws e.2)

  | Papp1 o e =>
    Let _ := assert (esubtype (etype_of_op1 o).1 (etype_of_expr m e))
                    (E.ierror_e e0) in
    Let e := wi2i_e e in
    let sc := sc_op1 o e.2 in
    ok (e.1 ++ sc, wi2i_op1_e o e.2)

  | Papp2 o e1 e2 =>
    let ty := etype_of_op2 o in
    Let _ := assert [&& esubtype ty.1.1 (etype_of_expr m e1) &
                        esubtype ty.1.2 (etype_of_expr m e2)]
                    (E.ierror_e e0) in
    Let e1 := wi2i_e e1 in
    Let e2 := wi2i_e e2 in
    let sc := sc_op2 o e1.2 e2.2 in
    ok (e1.1 ++ e2.1 ++ sc, wi2i_op2_e o e1.2 e2.2)

  | PappN o es =>
    Let _ := assert (all (fun e => sign_of_expr m e == None) es)
                    (E.ierror_e e0) in
    Let es := wi2i_es wi2i_e es in
    ok (es.1, PappN o es.2)

  | Pif ty e1 e2 e3 =>
    let ety := etype_of_expr m e0 in
    Let _ := assert [&& esubtype ety (etype_of_expr m e2) &
                        esubtype ety (etype_of_expr m e3)]
                    (E.ierror_e e0) in
    let ty := wi2i_type (sign_of_expr m e2) ty in
    Let e1 := wi2i_e e1 in
    Let e2 := wi2i_e e2 in
    Let e3 := wi2i_e e3 in
    ok (e1.1 ++ e2.1 ++ e3.1, Pif ty e1.2 e2.2 e3.2)

  | Pbig ei o v e es el =>

    let ty := etype_of_op2 o in
    Let _ := assert [&& esubtype ty.2 (etype_of_expr m ei)
                      , esubtype ty.1.1 ty.2
                      , esubtype ty.1.2 (etype_of_expr m e)
                      , vtype v == aint
                      , etype_of_expr m es == ETint _
                      & etype_of_expr m el == ETint _]
                     (E.ierror_e e0) in
     Let _ := assert (if is_wi2 o is None then true else false)
                (E.error_e "can not use bigop on wint operator" e0) in
     Let ei := wi2i_e ei in
     Let e := wi2i_e e in
     Let es := wi2i_e es in
     Let el := wi2i_e el in
     Let v := wi2i_vari v in
     ok (ei.1 ++ es.1 ++ el.1 ++ sc_all e.1 v es.2 el.2,
         Pbig ei.2 (wi2i_op2 o) v e.2 es.2 el.2)

  | Pis_var_init x =>
    Let x := wi2i_vari x in
    ok ([::], Pis_var_init x)

  | Pis_mem_init e1 e2 =>
    Let _ := assert [&& etype_of_expr m e1 == ETword _ None Uptr
                      & etype_of_expr m e2 == ETint _] (E.ierror_e e0) in
    Let e1 := wi2i_e e1 in
    Let e2 := wi2i_e e2 in
    ok (e1.1 ++ e2.1, Pis_mem_init e1.2 e2.2)
  end.

Definition wi2i_lvar (ety : extended_type positive) (x : var_i) : cexec var_i :=
  Let _ := assert (esubtype (etype_of_var m x) ety)
                  (E.ierror_lv (Lvar x)) in
  wi2i_vari x.

Definition wi2i_lv (ety : extended_type positive) (lv : lval) : cexec (safety_cond * lval) :=
  let s := sign_of_etype ety in
  match lv with
  | Lnone vi ty =>
    Let _ := assert (esubtype (to_etype (sign_of_etype ety) ty) ety) (E.ierror_lv lv) in
    ok ([::], Lnone vi (wi2i_type s ty))

  | Lvar x =>
    Let x := wi2i_lvar ety x in
    ok ([::], Lvar x)

  | Lmem al ws vi e =>
    Let _ := assert [&& sign_of_expr m e == None & s == None]
                    (E.ierror_lv lv) in
    Let e := wi2i_e e in
    ok (e.1, Lmem al ws vi e.2)

  | Laset al aa ws x e =>
    Let _ := assert [&& in_FV_var x, sign_of_expr m e == None & s == None]
                     (E.ierror_lv lv) in
    Let e := wi2i_e e in
    ok (e.1, Laset al aa ws x e.2)

  | Lasub aa ws len x e =>
    Let _ := assert [&& in_FV_var x, sign_of_expr m e == None & s == None]
                     (E.ierror_lv lv) in
    Let e := wi2i_e e in
    ok (e.1, Lasub aa ws len x e.2)
  end.

Definition wi2i_lvs msg okmem xtys xs :=
  let err := E.ierror_s msg in
  Let scxs := mapM2 err wi2i_lv xtys xs in
  let scs := unzip1 scxs in
  let xs := unzip2 scxs in
  (* FIXME : is it really an internal error ? *)
  Let _ := assert (check_xs okmem Sv.empty xs scs) err in
  ok (flatten scs, xs).


Definition wi2i_a_and (a : assertion) :=
  Let e := wi2i_e a.2 in
  ok (a.1, eands (rcons e.1 e.2)).

Context (sigs : funname -> option (list (extended_type positive) * list (extended_type positive))).

Definition get_sig f :=
  match sigs f with
  | Some sig => ok sig
  | None => Error (E.ierror_s "unknown function")
  end.

Definition wi2i_c (wi2i : instr -> cexec cmd) c :=
  Let c := mapM wi2i c in
  ok (flatten c).

Definition is_spill o := 
  match o with
  | Opseudo_op (Ospill k tys) => Some (k, tys)
  | _ => None
  end.

Fixpoint wi2i_ir (ir:instr_r) : cexec (safety_cond * instr_r) :=
  match ir with
  | Cassgn x tag ty e =>
    let ety := etype_of_expr m e in
    let sg  := sign_of_etype ety in
    let tyr := to_etype sg ty in
    Let _ := assert (esubtype tyr ety)
                    (E.ierror_s "invalid type in assignment") in
    Let x := wi2i_lv tyr x in
    Let e := wi2i_e e in
    let ty := wi2i_type sg ty in
    ok (e.1 ++ x.1, Cassgn x.2 tag ty e.2)

  | Copn xs t o es => 
    Let es' := wi2i_es wi2i_e es in
    let xtys := map (to_etype None) (sopn_tout o) in
    Let xs := wi2i_lvs "invalid dest in Copn" true xtys xs in
    Let o := 
     (* FIXME: should we do that for other operators ? maybe for swap ? *)
     match is_spill o with
     | None => 
       Let _ := assert (all (fun e => sign_of_expr m e == None) es)
                    (E.ierror_s "invalid expr in Copn") in
       ok o 
     | Some (k, tys) => 
       (* We check that the operator is well type *)
       let etys := map (etype_of_expr m) es in
       let tys' := map2 (fun ety ty => to_etype (sign_of_etype ety) ty) etys tys in
       Let _ := assert (size tys == size es) (E.ierror_s "ill typed Copn") in
       Let _ := assert (all2 esubtype tys' etys) (E.ierror_s "ill typed Copn (arguments)") in
       (* We patch the type of the operator *)
       let tys := map2 (fun ty e => wi2i_type (sign_of_expr m e) ty) tys es in
       ok (Opseudo_op (Ospill k tys))
     end in
    ok (es'.1 ++ xs.1, Copn xs.2 t o es'.2)

  | Csyscall xs o es =>
    Let _ := assert (all (fun e => sign_of_expr m e == None) es)
                    (E.ierror_s "invalid args in Csyscall") in
    Let es := wi2i_es wi2i_e es in
    let xtys := map (to_etype None) (syscall_sig_u o).(scs_tout) in
    Let xs := wi2i_lvs "invalid dest in Csyscall" true xtys xs in
    ok (es.1 ++ xs.1, Csyscall xs.2 o es.2)

  | Cassert a =>
    Let a := wi2i_a_and a in
    ok ([::], Cassert a)

  | Cif b c1 c2 =>
    Let b := wi2i_e b in
    Let c1 := wi2i_c wi2i_i c1 in
    Let c2 := wi2i_c wi2i_i c2 in
    ok (b.1, Cif b.2 c1 c2)

  | Cfor x (dir, e1, e2) c =>
    Let _ := assert [&& in_FV_var x, vtype x == aint, etype_of_expr m e1 == ETint _ & etype_of_expr m e2 == ETint _]
                (E.ierror_s "invalid loop counter") in
    Let e1 := wi2i_e e1 in
    Let e2 := wi2i_e e2 in
    Let c := wi2i_c wi2i_i c in
    ok (e1.1 ++ e2.1, Cfor x (dir, e1.2, e2.2) c)

  | Cwhile a c e ii' c' =>
    Let e := wi2i_e e in
    Let c := wi2i_c wi2i_i c in
    Let c' := wi2i_c wi2i_i c' in
    ok ([::], Cwhile a (c ++ safe_assert ii' e.1) e.2 ii' c')

  | Ccall xs f es =>
    Let sig := get_sig f in
    Let _ := assert (all2 (fun ety e => esubtype ety (etype_of_expr m e)) sig.1 es)
                    (E.ierror_s "invalid args in Ccall") in
    Let es := wi2i_es wi2i_e es in
    Let xs := wi2i_lvs "invalid dest in Ccall" false sig.2 xs in
    ok (es.1 ++ xs.1, Ccall xs.2 f es.2)
  end

with wi2i_i (i:instr) : cexec cmd :=
  let (ii,ir) := i in
  Let ir := add_iinfo ii (wi2i_ir ir) in
  ok (rcons (safe_assert ii ir.1) (MkI ii ir.2)).

Definition wi2i_ci ci sig :=
  Let ci_pre := mapM wi2i_a_and ci.(f_pre) in
  Let wint_precond := mapM wint_contract_condition ci.(f_iparams) in
  let ci_pre := ci_pre ++ flatten wint_precond in
  Let ci_post := mapM wi2i_a_and ci.(f_post) in
  Let wint_postcond := mapM wint_contract_condition ci.(f_ires) in
  let ci_post := ci_post ++ flatten wint_postcond in
  Let p := mapM2 (E.ierror_s "bad params in fun") wi2i_lvar sig.1 ci.(f_iparams) in
  Let r := mapM2 (E.ierror_s "bad return in fun") wi2i_lvar sig.2 ci.(f_ires) in
  ok (MkContra p r ci_pre ci_post).

Definition wi2i_fun (fn:funname) (f: fundef) :=
  add_funname fn (
  Let sig := get_sig fn in
  let 'MkFun ii ci si p c so r ev := f in
  Let ci :=
    match ci with
    | None => ok None (*TODO: add conditions for params and return values that are wint*)
    | Some ci =>
      Let ci := wi2i_ci ci sig in
      ok (Some ci)
    end
  in
  Let _ := assert ((size p == size si) && (size r == size so))
                  (E.ierror_s "bad signature in fun") in
  Let p := mapM2 (E.ierror_s "bad params in fun") wi2i_lvar sig.1 p in
  Let c := wi2i_c wi2i_i c in
  Let r :=
    mapM2 (E.ierror_s "bad return in fun")
      (fun ety x => assert (esubtype ety (etype_of_var m x)) (E.ierror_lv x) >> wi2i_vari x)
      sig.2 r in
  let mk := map (fun ety => wi2i_type (sign_of_etype ety) (to_atype ety)) in
  let tin := mk sig.1 in
  let tout := mk sig.2 in
  ok (MkFun ii ci tin p c tout r ev)).

Definition build_sig (fd : funname * fundef) :=
 let 'MkFun ii ci si p c so r ev := fd.2 in
 let mk := map2 (fun (x:var_i) ty => to_etype (sign_of_var m x) ty) in
 (fd.1, (mk p si, mk r so)).

End Section.


Definition build_info (info:var -> option (signedness * var)) (fv : Sv.t) :=
  Let fvm :=
    foldM (fun x (fvm: Sv.t * Mvar.t (signedness * var)) =>
      match info x with
      | None => ok fvm
      | Some (s, xi) =>
        Let w :=
          match is_word_type (vtype x) with
          | Some w => ok w
          | None => Error (E.ierror_s "invalid info")
          end in
        Let _ := assert (convertible (vtype xi) aint && ~~Sv.mem xi fvm.1) (E.ierror_s "invalid info") in
        ok (Sv.add xi fvm.1, Mvar.set fvm.2 x (s, xi))
      end)
      (fv, Mvar.empty _)
      (Sv.elements fv) in
   ok (Mvar.get fvm.2).

(* FIXME: why get_info return a Sv.t, that should be include in (vars_p (p_funcs p)) ?
          why we don't use (vars_p (p_funcs p)) directly ? *)
Context (get_info : _uprog -> (Sv.t * (var -> option (signedness * var)))).

Definition wi2i_prog (p:_uprog) : cexec _uprog :=
  let (FV,info) := get_info p in
  Let m := build_info info FV in
  Let _ := assert (Sv.subset (vars_p (p_funcs p)) FV) (E.ierror_s "FV is not included in vars_p") in
  let sigs := map (build_sig info) (p_funcs p) in
  Let funcs := map_cfprog_name (wi2i_fun m FV (get_fundef sigs)) (p_funcs p) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End WITH_PARAMS.
