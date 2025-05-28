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

Context `{asmop:asmOp} {msfsz : MSFsize} {pd: PointerData}.

#[local]
Existing Instance progUnit.

Definition is_wi1 (o: sop1) :=
  if o is Owi1 s op then Some (s, op) else None.

Definition is_wi2 (o: sop2) :=
  if o is Owi2 s sw op then Some (s, sw, op) else None.

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

Definition esubtype (ty1 ty2 : extended_type positive) :=
 match ty1, ty2 with
 | ETword None w, ETword None w' => (w ≤ w')%CMP
 | ETword (Some sg) w, ETword (Some sg') w' => (sg == sg') && (w == w')
 | ETint, ETint => true
 | ETbool, ETbool => true
 | ETarr l, ETarr l' => l == l'
 | _, _ => false
 end.

(* All arguments should have type int *)
Definition elti e1 e2 := Papp2 (Olt Cmp_int) e1 e2.
Definition elei e1 e2 := Papp2 (Ole Cmp_int) e1 e2.
Definition eeqi e1 e2 := Papp2 (Oeq Op_int) e1 e2.
Definition eneqi e1 e2 := Papp2 (Oneq Op_int) e1 e2.
Definition elsli e1 e2 := Papp2 (Olsl Op_int) e1 e2.

Definition emin_signed sz := Pconst (wmin_signed sz).
Definition emax_signed sz := Pconst (wmax_signed sz).
Definition ezero := Pconst 0.
Definition emax_unsigned sz := Pconst (wmax_unsigned sz).

Definition etrue := Pbool true.

Fixpoint eands es :=
  match es with
  | [::] => etrue
  | [::e] => e
  | e::es => eand e (eands es)
  end.

Definition sc_all cond v start len :=
  if cond is nil then [::]
  else [:: Pbig etrue Oand v (eands cond) start len].

(* All arguments should have type int *)
Definition sc_in_range lo hi e := eand (elei lo e) (elei e hi).
Definition sc_uint_range sz e := sc_in_range ezero (emax_unsigned sz) e.
Definition sc_sint_range sz e := sc_in_range (emin_signed sz) (emax_signed sz) e.
Definition sc_wi_range sg sz e := signed (sc_uint_range sz) (sc_sint_range sz) sg e.

Definition sc_wiop1 sg (o : wiop1) e :=
  match o with
  | WIwint_of_int sz => [:: sc_wi_range sg sz e]
  | WIint_of_wint sz => [::]
  | WIword_of_wint sz => [::]
  | WIwint_of_word sz => [::]
  | WIwint_ext szo szi => [::]
  | WIneg sz =>
      signed  [::eeqi e ezero ]
              [::eneqi e (emin_signed sz)] sg
  end.

Definition sc_op1 (op1 : sop1) e :=
  match is_wi1 op1 with
  | Some (sg, o) => sc_wiop1 sg o e
  | None => [::]
  end.

(* [op : int -> int -> int] [e1 e2 : int] *)
Definition sc_wi_range_op2 sg sz op e1 e2 :=
  sc_wi_range sg sz (Papp2 op e1 e2).

(* [e1 e2 : int] *)
Definition sc_divmod sg sz e1 e2 :=
 let sc := signed [::]
                  [:: enot (eand (eeqi e1 (emin_signed sz)) (eeqi e2 (Pconst (-1)))) ] sg in
 [:: eneqi e2 ezero & sc].

Definition sc_wiop2 sg sz o e1 e2 :=
  match o with
  | WIadd => [:: sc_wi_range_op2 sg sz (Oadd Op_int) e1 e2]
  | WImul => [:: sc_wi_range_op2 sg sz (Omul Op_int) e1 e2]
  | WIsub => [:: sc_wi_range_op2 sg sz (Osub Op_int) e1 e2]
  | WIdiv => sc_divmod sg sz e1 e2
  | WImod => sc_divmod sg sz e1 e2
  | WIshl => [:: sc_wi_range sg sz (elsli e1 e2) ]
  | WIshr => [::]
  | WIeq | WIneq | WIlt | WIle | WIgt | WIge  => [::]
  end.

Definition sc_op2 o e1 e2 :=
  match is_wi2 o with
  | Some (sg, sz, o) => sc_wiop2 sg sz o e1 e2
  | _ => [::]
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
  | Pload al ws e => tword ws
  | Papp1 o e => (etype_of_op1 o).2
  | Papp2 o e1 e2 => (etype_of_op2 o).2
  | PappN o es => to_etype None (type_of_opN o).2
  | Pif ty e1 e2 e3 => to_etype (sign_of_etype (etype_of_expr e2)) ty
  | Pbig ei o v e es el => (etype_of_op2 o).2
  | Parr_init_elem e len => tarr len
  | Pis_var_init _ => tbool
  | Pis_arr_init _ _ _ => tbool
  | Pis_barr_init _ _ _ => tbool
  | Pis_mem_init _ _ => tbool
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

Definition safety_cond := seq pexpr.

Definition wi2i_es (wi2i_e : pexpr -> cexec (safety_cond * pexpr)) (es : pexprs) : cexec (safety_cond * pexprs) :=
  Let es := mapM wi2i_e es in
  ok (flatten (unzip1 es), unzip2 es).

Fixpoint wi2i_e (e0:pexpr) : cexec (safety_cond * pexpr) :=
  match e0 with
  | Pconst _ | Pbool _ | Parr_init _ => ok ([::], e0)

  | Pvar x =>
    Let x := wi2i_gvar x in
    ok ([::], Pvar x)

  | Pget al aa ws x e =>
    Let _ := assert (sign_of_expr e == None)
                    (E.ierror_e e0) in
    Let x := wi2i_gvar x in
    Let e := wi2i_e e in
    ok (e.1, Pget al aa ws x e.2)

  | Psub al ws len x e =>
    Let _ := assert (sign_of_expr e == None)
                    (E.ierror_e e0) in
    Let x := wi2i_gvar x in
    Let e := wi2i_e e in
    ok (e.1, Psub al ws len x e.2)

  | Pload al ws e =>
    Let _ := assert (sign_of_expr e == None)
                    (E.ierror_e e0) in
    Let e := wi2i_e e in
    ok (e.1, Pload al ws e.2)

  | Papp1 o e =>
    Let _ := assert (esubtype (etype_of_op1 o).1 (etype_of_expr e))
                    (E.ierror_e e0) in
    Let e := wi2i_e e in
    let sc := sc_op1 o e.2 in
    ok (e.1 ++ sc, wi2i_op1_e o e.2)

  | Papp2 o e1 e2 =>
    let ty := etype_of_op2 o in
    Let _ := assert [&& esubtype ty.1.1 (etype_of_expr e1) &
                        esubtype ty.1.2 (etype_of_expr e2)]
                    (E.ierror_e e0) in
    Let e1 := wi2i_e e1 in
    Let e2 := wi2i_e e2 in
    let sc := sc_op2 o e1.2 e2.2 in
    ok (e1.1 ++ e2.1 ++ sc, wi2i_op2_e o e1.2 e2.2)

  | PappN o es =>
    Let _ := assert (all (fun e => sign_of_expr e == None) es)
                    (E.ierror_e e0) in
    Let es := wi2i_es wi2i_e es in
    ok (es.1, PappN o es.2)

  | Pif ty e1 e2 e3 =>
    let ety := etype_of_expr e0 in
    Let _ := assert [&& esubtype ety (etype_of_expr e2) &
                        esubtype ety (etype_of_expr e3)]
                    (E.ierror_e e0) in
    let ty := wi2i_type (sign_of_expr e2) ty in
    Let e1 := wi2i_e e1 in
    Let e2 := wi2i_e e2 in
    Let e3 := wi2i_e e3 in
    ok (e1.1 ++ e2.1 ++ e3.1, Pif ty e1.2 e2.2 e3.2)

  | Pbig ei o v e es el =>

    let ty := etype_of_op2 o in
    Let _ := assert [&& esubtype ty.2 (etype_of_expr ei)
                      , esubtype ty.1.1 ty.2
                      , esubtype ty.1.2 (etype_of_expr e)
                      , etype_of_expr es == ETint _
                      & etype_of_expr el == ETint _]
                     (E.ierror_e e0) in
     Let ei := wi2i_e ei in
     Let e := wi2i_e e in
     Let es := wi2i_e es in
     Let el := wi2i_e el in
     Let v := wi2i_vari v in
     ok (ei.1 ++ es.1 ++ el.1 ++ sc_all e.1 v es.2 el.2,
         Pbig ei.2 (wi2i_op2 o) v e.2 es.2 el.2)

  | Parr_init_elem e len =>
    Let _ := assert (etype_of_expr e == ETword _ None U8) (E.ierror_e e0) in
    Let e := wi2i_e e in
    ok (e.1, Parr_init_elem e.2 len)

  | Pis_var_init x =>
    Let x := wi2i_vari x in
    ok ([::], Pis_var_init x)

  | Pis_arr_init x e1 e2 =>
    Let _ := assert [&& is_sarr (vtype x), etype_of_expr e1 == ETint _
                     & etype_of_expr e2 == ETint _] (E.ierror_e e0) in
    Let x := wi2i_vari x in
    Let e1 := wi2i_e e1 in
    Let e2 := wi2i_e e2 in
    ok (e1.1 ++ e2.1, Pis_arr_init x e1.2 e2.2)

  | Pis_barr_init x e1 e2 =>
    Let _ := assert [&& is_sarr (vtype x), etype_of_expr e1 == ETint _
                     & etype_of_expr e2 == ETint _ ] (E.ierror_e e0) in
    Let x := wi2i_vari x in
    Let e1 := wi2i_e e1 in
    Let e2 := wi2i_e e2 in
    ok (e1.1 ++ e2.1, Pis_barr_init x e1.2 e2.2)

  | Pis_mem_init e1 e2 =>
    Let _ := assert [&& etype_of_expr e1 == ETword _ None Uptr
                      & etype_of_expr e2 == ETint _] (E.ierror_e e0) in
    Let e1 := wi2i_e e1 in
    Let e2 := wi2i_e e2 in
    ok (e1.1 ++ e2.1, Pis_mem_init e1.2 e2.2)
  end.

Definition wi2i_lvar (ety : extended_type positive) (x : var_i) : cexec var_i :=
  Let _ := assert (esubtype (etype_of_var x) ety)
                  (E.ierror_lv (Lvar x)) in
  wi2i_vari x.

Definition wi2i_lv (ety : extended_type positive) (lv : lval) : cexec (safety_cond * lval) :=
  let s := sign_of_etype ety in
  match lv with
  | Lnone vi ty =>
    ok ([::], Lnone vi (wi2i_type s ty))

  | Lvar x =>
    Let x := wi2i_lvar ety x in
    ok ([::], Lvar x)

  | Lmem al ws vi e =>
    Let _ := assert [&& sign_of_expr e == None & s == None]
                    (E.ierror_lv lv) in
    Let e := wi2i_e e in
    ok (e.1, Lmem al ws vi e.2)

  | Laset al aa ws x e =>
    Let _ := assert [&& in_FV_var x, sign_of_expr e == None & s == None]
                     (E.ierror_lv lv) in
    Let e := wi2i_e e in
    ok (e.1, Laset al aa ws x e.2)

  | Lasub aa ws len x e =>
    Let _ := assert [&& in_FV_var x, sign_of_expr e == None & s == None]
                     (E.ierror_lv lv) in
    Let e := wi2i_e e in
    ok (e.1, Lasub aa ws len x e.2)
  end.

Fixpoint check_xs W xs scs :=
  match xs, scs with
  | [::], [::] => true
  | x :: xs, sc :: scs =>
    disjoint (read_es sc) W && check_xs (vrv_rec W x) xs scs
  | _, _ => false (* Should never occurs *)
  end.

Definition wi2i_lvs msg xtys xs :=
  let err := E.ierror_s msg in
  Let scxs := mapM2 err wi2i_lv xtys xs in
  let scs := unzip1 scxs in
  let xs := unzip2 scxs in
  Let _ := assert (check_xs Sv.empty xs scs) err in
  ok (flatten scs, xs).

Definition wi2i_a (a : assertion) :=
  Let e := wi2i_e a.2 in
  ok (e.1, (a.1, e.2)).

Definition wi2i_a_and (a : assertion) :=
  Let e := wi2i_e a.2 in
  ok (a.1, eands (rcons e.1 e.2)).

Context (sigs : funname -> option (list (extended_type positive) * list (extended_type positive))).

Definition get_sig f :=
  match sigs f with
  | Some sig => ok sig
  | None => Error (E.ierror_s "unknown function")
  end.

(* TODO : Move this *)
Definition safety_lbl := "safety"%string.

(* TODO : Move this *)
Definition safe_assert ii (sc:safety_cond) : cmd :=
  map (fun e => MkI ii (Cassert (safety_lbl, e))) sc.

Definition wi2i_c (wi2i : instr -> cexec cmd) c :=
  Let c := mapM wi2i c in
  ok (flatten c).

Fixpoint wi2i_ir (ir:instr_r) : cexec (safety_cond * instr_r) :=
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
    ok (x.1 ++ e.1, Cassgn x.2 tag ty e.2)

  | Copn xs t o es =>
    Let _ := assert (all (fun e => sign_of_expr e == None) es)
                    (E.ierror_s "invalid expr in Copn") in

    Let es := wi2i_es wi2i_e es in
    let xtys := map (to_etype None) (sopn_tout o) in
    Let xs := wi2i_lvs "invalid dest in Copn" xtys xs in
    ok (es.1 ++ xs.1, Copn xs.2 t o es.2)

  | Csyscall xs o es =>
    Let _ := assert (all (fun e => sign_of_expr e == None) es)
                    (E.ierror_s "invalid args in Csyscall") in
    Let es := wi2i_es wi2i_e es in
    let xtys := map (to_etype None) (syscall_sig_u o).(scs_tout) in
    Let xs := wi2i_lvs "invalid dest in Csyscall" xtys xs in
    ok (es.1 ++ xs.1, Csyscall xs.2 o es.2)

  | Cassert a =>
    Let a := wi2i_a a in
    ok (a.1, Cassert a.2)

  | Cif b c1 c2 =>
    Let b := wi2i_e b in
    Let c1 := wi2i_c wi2i_i c1 in
    Let c2 := wi2i_c wi2i_i c2 in
    ok (b.1, Cif b.2 c1 c2)

  | Cfor x (dir, e1, e2) c =>
    Let _ := assert (in_FV_var x) (E.ierror_s "invalid loop counter") in
    Let e1 := wi2i_e e1 in
    Let e2 := wi2i_e e2 in
    Let c := wi2i_c wi2i_i c in
    ok (e1.1 ++ e2.1, Cfor x (dir, e1.2, e2.2) c)

  | Cwhile a c e info c' =>
    Let e := wi2i_e e in
    Let c := wi2i_c wi2i_i c in
    Let c' := wi2i_c wi2i_i c' in
    ok (e.1, Cwhile a c e.2 info c')

  | Ccall xs f es =>
    Let sig := get_sig f in
    Let _ := assert (all2 (fun ety e => esubtype ety (etype_of_expr e)) sig.1 es)
                    (E.ierror_s "invalid args in Ccall") in
    Let es := wi2i_es wi2i_e es in
    Let xs := wi2i_lvs "invalid dest in Ccall" sig.2 xs in
    ok (es.1 ++ xs.1, Ccall xs.2 f es.2)
  end

with wi2i_i (i:instr) : cexec cmd :=
  let (ii,ir) := i in
  Let ir := add_iinfo ii (wi2i_ir ir) in
  ok (rcons (safe_assert ii ir.1) (MkI ii ir.2)).


Definition wi2i_ci ci sig :=
  Let ci_pre := mapM wi2i_a_and ci.(f_pre) in
  Let ci_post := mapM wi2i_a_and ci.(f_post) in
  Let p := mapM2 (E.ierror_s "bad params in fun") wi2i_lvar sig.1 ci.(f_iparams) in
  Let r := mapM2 (E.ierror_s "bad return in fun") (fun ety x =>
                    Let _ := assert (esubtype ety (etype_of_var x))
                                    (E.ierror_e (Plvar x)) in
                    wi2i_vari x) sig.2 ci.(f_ires) in
  ok (MkContra p r ci_pre ci_post).

Definition wi2i_fun (fn:funname) (f: fundef) :=
  add_funname fn (
  Let sig := get_sig fn in
  let 'MkFun ii ci si p c so r ev := f in
  Let ci :=
    match ci with
    | None => ok None
    | Some ci =>
      Let ci := wi2i_ci ci sig in
      ok (Some ci)
    end
  in
  Let p := mapM2 (E.ierror_s "bad params in fun") wi2i_lvar sig.1 p in
  Let c := wi2i_c wi2i_i c in
  Let r := mapM2 (E.ierror_s "bad return in fun") (fun ety x =>
                    Let _ := assert (esubtype ety (etype_of_var x))
                                    (E.ierror_e (Plvar x)) in
                    wi2i_vari x) sig.2 r in
  let mk := map (fun ety => wi2i_type (sign_of_etype ety) (to_stype ety)) in
  let tin := mk sig.1 in
  let tout := mk sig.2 in
  ok (MkFun ii ci tin p c tout r ev)).

Definition build_sig (fd : funname * fundef) :=
 let 'MkFun ii ci si p c so r ev := fd.2 in
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
  (* FIXME : we need to add the variables of the pre and post *)
  let FV := vars_p (p_funcs p) in
  Let m := build_info FV in
  let sigs := map (build_sig info) (p_funcs p) in
  Let funcs := map_cfprog_name (wi2i_fun m FV (get_fundef sigs)) (p_funcs p) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End WITH_PARAMS.
