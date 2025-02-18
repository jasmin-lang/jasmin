(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Import expr sem_op_typed compiler_util.
Import Utf8.
Import oseq.
Require Import flag_combination.

Local Open Scope seq_scope.
Local Open Scope Z_scope.


Module Import E.

  Definition pass : string := "wint_to_int".

  Definition ierror_s := pp_internal_error_s pass.

  Definition ierror := pp_internal_error pass.

  Definition ierror_e e :=
    ierror (pp_nobox [:: pp_s "ill typed expression"; pp_e e]).

  Definition ierror_lv lv :=
    ierror (pp_nobox [:: pp_s "ill typed left value"; pp_lv lv]).

End E.

Section WITH_PARAMS.

Context `{asmop:asmOp} {msfsz : MSFsize}.

#[local]
Existing Instance progUnit.

Definition is_wi1 (o: sop1) :=
  if o is Owi1 s op then Some (s, op) else None.

Definition is_wi2 (o: sop2) :=
  if o is Owi2 s _ op then Some (s, op) else None.

Definition wi2i_op2 (o : sop2) : sop2 :=
  match is_wi2 o with
  | Some (s, op) =>
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

Definition esubtype (ty1 ty2 : extended_type positive) :=
 match ty1, ty2 with
 | ETword None w, ETword None w' => (w ≤ w')%CMP
 | ETword (Some sg) w, ETword (Some sg') w' => (sg == sg') && (w == w')
 | ETint, ETint => true
 | ETbool, ETbool => true
 | ETarr l, ETarr l' => l == l'
 | _, _ => false
 end.

Definition wi2i_op1_e (o : sop1) (e : pexpr) :=
  match is_wi1 o with
  | Some (s, o) =>
    match o with
    | WIwint_of_int ws => e
    | WIint_of_wint ws => e
    | WIword_of_wint ws => Papp1 (Oword_of_int ws) e
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

Definition to_etype sg (t:stype) : extended_type positive:=
  match t with
  | sbool    => tbool
  | sint     => tint
  | sarr l   => tarr l
  | sword ws => ETword _ sg ws
  end.

Definition sign_of_var x := Option.map fst (m x).

Definition etype_of_var x : extended_type positive :=
  to_etype (sign_of_var x) (vtype x).

Definition sign_of_gvar (x : gvar) :=
  if is_lvar x then sign_of_var (gv x)
  else None.

Definition etype_of_gvar x := to_etype (sign_of_gvar x) (vtype (gv x)).

Definition sign_of_etype (ty: extended_type positive) : option signedness :=
  match ty with
  | ETword (Some s) _ => Some s
  | _ => None
  end.

Fixpoint etype_of_expr (e:pexpr) : extended_type positive :=
  match e with
  | Pconst _ => tint
  | Pbool _ => tbool
  | Parr_init len => tarr len
  | Pvar x => etype_of_gvar x
  | Pget al aa ws x e => tword ws
  | Psub al ws len x e => tarr (Z.to_pos (arr_size ws len))
  | Pload al ws x e => tword ws
  | Papp1 o e => (etype_of_op1 o).2
  | Papp2 o e1 e2 => (etype_of_op2 o).2
  | PappN o es => to_etype None (type_of_opN o).2
  | Pif ty e1 e2 e3 => to_etype (sign_of_etype (etype_of_expr e2)) ty
  end.

Definition sign_of_expr (e:pexpr) : option signedness :=
  sign_of_etype (etype_of_expr e).

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

Definition wi2i_gvar (x: gvar) :=
  if is_lvar x then
    Let xi := wi2i_vari (gv x) in
    ok (mk_lvar xi)
  else ok x.

Definition wi2i_type (sg : option signedness) ty :=
  if sg == None then ty else sint.

Fixpoint wi2i_e (e0:pexpr) : cexec pexpr :=
  match e0 with
  | Pconst _ | Pbool _ | Parr_init _ => ok e0
  | Pvar x =>
    Let x := wi2i_gvar x in
    ok (Pvar x)
  | Pget al aa ws x e =>
    Let x := wi2i_gvar x in
    Let e := wi2i_e e in
    ok (Pget al aa ws x e)
  | Psub al ws len x e =>
    Let x := wi2i_gvar x in
    Let e := wi2i_e e in
    ok (Psub al ws len x e)
  | Pload al ws x e =>
    Let _ := assert [&& m x == None & sign_of_expr e == None]
                    (E.ierror_e e0) in
    Let x := wi2i_vari x in
    Let e := wi2i_e e in
    ok (Pload al ws x e)
  | Papp1 o e =>
    Let _ := assert (esubtype (etype_of_op1 o).1 (etype_of_expr e))
                    (E.ierror_e e0) in
    Let e := wi2i_e e in
    ok (wi2i_op1_e o e)
  | Papp2 o e1 e2 =>
    let ty := etype_of_op2 o in
    Let _ := assert [&& esubtype ty.1.1 (etype_of_expr e1) &
                        esubtype ty.1.2 (etype_of_expr e2)]
                    (E.ierror_e e0) in
    Let e1 := wi2i_e e1 in
    Let e2 := wi2i_e e2 in
    ok (wi2i_op2_e o e1 e2)

  | PappN o es =>
    Let _ := assert (all (fun e => sign_of_expr e == None) es)
                    (E.ierror_e e0) in
    Let es := mapM wi2i_e es in
    ok (PappN o es)

  | Pif ty e1 e2 e3 =>
    let ety := etype_of_expr e0 in
    Let _ := assert [&& esubtype ety (etype_of_expr e2) &
                        esubtype ety (etype_of_expr e3)]
                    (E.ierror_e e0) in
    let ty := wi2i_type (sign_of_expr e2) ty in
    Let e1 := wi2i_e e1 in
    Let e2 := wi2i_e e2 in
    Let e3 := wi2i_e e3 in
    ok (Pif ty e1 e2 e3)
  end.

Definition wi2i_lvar (ety : extended_type positive) (x : var_i) : cexec var_i :=
  Let _ := assert (esubtype (etype_of_var x) ety)
                  (E.ierror_lv (Lvar x)) in
  wi2i_vari x.

Definition wi2i_lv (ety : extended_type positive) (lv : lval) : cexec lval :=
  let s := sign_of_etype ety in
  match lv with
  | Lnone vi ty =>
    ok (Lnone vi (wi2i_type s ty))

  | Lvar x =>
    Let x := wi2i_lvar ety x in
    ok (Lvar x)

  | Lmem al ws x e =>
    Let _ := assert [&& in_FV_var x, m x == None, sign_of_expr e == None & s == None]
                    (E.ierror_lv lv) in
    Let e := wi2i_e e in
    ok (Lmem al ws x e)

  | Laset al aa ws x e =>
    Let _ := assert [&& in_FV_var x, sign_of_expr e == None & s == None]
                     (E.ierror_lv lv) in
    Let e := wi2i_e e in
    ok (Laset al aa ws x e)

  | Lasub aa ws len x e =>
    Let _ := assert [&& in_FV_var x, sign_of_expr e == None & s == None]
                     (E.ierror_lv lv) in
    Let e := wi2i_e e in
    ok (Lasub aa ws len x e)
  end.

Context (sigs : funname -> option (list (extended_type positive) * list (extended_type positive))).

Definition get_sig f :=
  match sigs f with
  | Some sig => ok sig
  | None => Error (E.ierror_s "unknown function")
  end.

Fixpoint wi2i_ir (ir:instr_r) : cexec instr_r :=
  match ir with
  | Cassgn x tag ty e =>
    let ety := etype_of_expr e in
    let sg  := sign_of_etype ety in
    let tyr := to_etype sg ty in
    Let _ := assert (esubtype tyr ety)
                    (E.ierror_s "invalid type in assigned") in
    Let x := wi2i_lv tyr x in
    Let e := wi2i_e e in
    let ty := wi2i_type sg ty in
    ok (Cassgn x tag ty e)

  | Copn xs t o es =>
    Let _ := assert (all (fun e => sign_of_expr e == None) es)
                    (E.ierror_s "invalid expr in Copn") in

    Let es := mapM wi2i_e es in
    let xtys := map (to_etype None) (sopn_tout o) in
    Let xs := mapM2 (E.ierror_s "invalid dest in Copn") wi2i_lv xtys xs in
    ok (Copn xs t o es)

  | Csyscall xs o es =>
    Let _ := assert (all (fun e => sign_of_expr e == None) es)
                    (E.ierror_s "invalid args in Csyscall") in
    Let es := mapM wi2i_e es in
    let xtys := map (to_etype None) (syscall_sig_u o).(scs_tout) in
    Let xs := mapM2 (E.ierror_s "invalid dest in Copn") wi2i_lv xtys xs in
    ok (Csyscall xs o es)

  | Cif b c1 c2 =>
    Let b := wi2i_e b in
    Let c1 := mapM wi2i_i c1 in
    Let c2 := mapM wi2i_i c2 in
    ok (Cif b c1 c2)

  | Cfor x (dir, e1, e2) c =>
    Let _ := assert (in_FV_var x) (E.ierror_s "invalid loop counter") in
    Let e1 := wi2i_e e1 in
    Let e2 := wi2i_e e2 in
    Let c := mapM wi2i_i c in
    ok (Cfor x (dir, e1, e2) c)

  | Cwhile a c e info c' =>
    Let e := wi2i_e e in
    Let c := mapM wi2i_i c in
    Let c' := mapM wi2i_i c' in
    ok (Cwhile a c e info c')

  | Ccall xs f es =>
    Let sig := get_sig f in
    Let _ := assert (all2 (fun ety e => esubtype ety (etype_of_expr e)) sig.1 es)
                    (E.ierror_s "invalid args in Ccall") in
    Let xs := mapM2 (E.ierror_s "bad xs length in Ccall") wi2i_lv sig.2 xs in
    Let es := mapM wi2i_e es in
    ok (Ccall xs f es)
  end

with wi2i_i (i:instr) : cexec instr :=
  let (ii,ir) := i in
  Let ir := add_iinfo ii (wi2i_ir ir) in
  ok (MkI ii ir).


Definition wi2i_fun (fn:funname) (f: fundef) :=
  add_funname fn (
  Let sig := get_sig fn in
  let 'MkFun ii si p c so r ev := f in
  Let p := mapM2 (E.ierror_s "bad params in fun") wi2i_lvar sig.1 p in
  Let c := mapM wi2i_i c in
  Let r := mapM2 (E.ierror_s "bad return in fun") (fun ety x =>
                    Let _ := assert (esubtype ety (etype_of_var x))
                                    (E.ierror_e (Plvar x)) in
                    wi2i_vari x) sig.2 r in
  let mk := map (fun ety => wi2i_type (sign_of_etype ety) (to_stype ety)) in
  let tin := mk sig.1 in
  let tout := mk sig.2 in
  ok (MkFun ii tin p c tout r ev)).

Definition build_sig (fd : funname * fundef) :=
 let 'MkFun ii si p c so r ev := fd.2 in
 let mk := map2 (fun (x:var_i) ty => to_etype (sign_of_var x) ty) in
 (fd.1, (mk p si, mk r so)).

End Section.

Context (info : var -> option (signedness * var)).

Definition build_info (fv : Sv.t) :=
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
        Let _ := assert ((vtype xi == sint) && ~~Sv.mem xi fvm.1) (E.ierror_s "invalid info") in
        ok (Sv.add xi fvm.1, Mvar.set fvm.2 x (s, xi))
      end)
      (fv, Mvar.empty _)
      (Sv.elements fv) in
   ok (Mvar.get fvm.2).

Definition wi2i_prog (p:_uprog) : cexec _uprog :=
  let FV := vars_p (p_funcs p) in
  Let m := build_info FV in
  let sigs := map (build_sig info) (p_funcs p) in
  Let funcs := map_cfprog_name (wi2i_fun m FV (get_fundef sigs)) (p_funcs p) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End WITH_PARAMS.
