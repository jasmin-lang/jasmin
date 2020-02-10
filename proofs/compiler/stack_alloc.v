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
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word utils type var expr low_memory sem.
Require Import constant_prop.
Require Import compiler_util.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Variant saved_stack :=
| SavedStackNone
| SavedStackReg of var
| SavedStackStk of Z.

Definition saved_stack_beq (x y : saved_stack) :=
  match x, y with
  | SavedStackNone, SavedStackNone => true
  | SavedStackReg v1, SavedStackReg v2 => v1 == v2
  | SavedStackStk z1, SavedStackStk z2 => z1 == z2
  | _, _ => false
  end.

Lemma saved_stack_eq_axiom : Equality.axiom saved_stack_beq.
Proof.
  move=> [ | v1 | z1] [ | v2 | z2] /=; try constructor => //.
  + apply (@equivP (v1 = v2)); first by apply eqP.
    by intuition congruence.
  apply (@equivP (z1 = z2)); first by apply eqP.
  by intuition congruence.
Qed.

Definition saved_stack_eqMixin   := Equality.Mixin saved_stack_eq_axiom.
Canonical  saved_stack_eqType      := Eval hnf in EqType saved_stack saved_stack_eqMixin.

Record sfundef := MkSFun {
  sf_iinfo  : instr_info;
  sf_stk_sz : Z;
  sf_stk_id : Ident.ident;
  sf_tyin   : seq stype;
  sf_params : seq var_i;
  sf_body   : cmd;
  sf_tyout  : seq stype;
  sf_res    : seq var_i;
  sf_extra  : list var * saved_stack;
}.

Definition sfundef_beq fd1 fd2 :=
  match fd1, fd2 with
  | MkSFun ii1 sz1 id1 ti1 p1 c1 to1 r1 e1, MkSFun ii2 sz2 id2 ti2 p2 c2 to2 r2 e2=>
    (ii1 == ii2) && (sz1 == sz2) && (id1 == id2) &&
    (ti1 == ti2) && (p1 == p2) && (c1 == c2) && (to1 == to2) && (r1 == r2) && (e1 == e2)
  end.

Lemma sfundef_eq_axiom : Equality.axiom sfundef_beq.
Proof.
  move=> [i1 s1 id1 ti1 p1 c1 to1 r1 e1] [i2 s2 id2 ti2 p2 c2 to2 r2 e2] /=.
  apply (@equivP ((i1 == i2) && (s1 == s2) && (id1 == id2) && (ti1 == ti2) && (p1 == p2) && (c1 == c2) && (to1 == to2) && (r1 == r2) && (e1 == e2)));first by apply idP.
  by split=> [ /andP[] /andP[] /andP[] /andP[] /andP[] /andP[] /andP[] /andP[] | [] ] /eqP -> /eqP->/eqP->/eqP->/eqP->/eqP->/eqP->/eqP->/eqP->.
Qed.

Definition sfundef_eqMixin   := Equality.Mixin sfundef_eq_axiom.
Canonical  sfundef_eqType      := Eval hnf in EqType sfundef sfundef_eqMixin.

Definition sprog := seq (funname * sfundef).

Definition map := (Mvar.t Z * Ident.ident)%type.

Definition size_of (t:stype) :=
  match t with
  | sword sz => ok (wsize_size sz)
  | sarr n   => ok (Zpos n)
  | _      => cerror (Cerr_stk_alloc "size_of")
  end.

Definition aligned_for (ty: stype) (ofs: Z) : bool :=
  match ty with
  | sarr _ => true
  | sword sz => is_align (wrepr _ ofs) sz
  | sbool | sint => false
  end.

Definition init_map (sz:Z) (nstk:Ident.ident) (l:list (var * Z)):=
  let add (vp:var*Z) (mp:Mvar.t Z * Z) :=
      let '(v, p) := vp in
    if (mp.2 <=? p)%Z then
      let ty := vtype v in
      if aligned_for ty vp.2 then
      Let s := size_of ty in
      cok (Mvar.set mp.1 v p, p + s)%Z
    else cerror (Cerr_stk_alloc "not aligned")
    else cerror (Cerr_stk_alloc "overlap") in
  Let mp := foldM add (Mvar.empty Z, 0%Z) l in
  if (mp.2 <=? sz)%Z then cok (mp.1, nstk)
  else cerror (Cerr_stk_alloc "stack size").

Definition is_in_stk (m:map) (x:var) :=
  match Mvar.get m.1 x with
  | Some _ => true
  | None   => false
  end.

Definition vstk (m:map) :=  {|vtype := sword Uptr; vname := m.2|}.

Definition is_vstk (m:map) (x:var) :=
  x == (vstk m).

Definition check_var m (x:var_i) :=
  ~~ is_in_stk m x && ~~is_vstk m x.

(* TODO: move *)
Definition is_word_type (t:stype) :=
  if t is sword sz then Some sz else None.

Definition cast_w ws := Papp1 (Oword_of_int ws).

Definition cast_ptr := cast_w Uptr.

Definition cast_const z := cast_ptr (Pconst z).

Definition mul := Papp2 (Omul (Op_w Uptr)).
Definition add := Papp2 (Oadd (Op_w Uptr)).

Definition cast_word e :=
  match e with
  | Papp1 (Oint_of_word U64) e1 => e1
  | _  => cast_ptr e
  end.

(* End TODO *)

Definition stk_not_fresh {A} :=
  @cerror (Cerr_stk_alloc "the stack variable is not fresh") A.

Definition not_a_word_v {A} :=
  @cerror (Cerr_stk_alloc "not a word variable") A.

Definition not_aligned {A} :=
  @cerror (Cerr_stk_alloc "array variable not aligned") A.

Definition invalid_var {A} :=
  @cerror (Cerr_stk_alloc "invalid variable") A.

Definition mk_ofs ws e1 ofs :=
  let sz := wsize_size ws in
  if is_const e1 is Some i then
    cast_const (i * sz + ofs)%Z
  else
    add (mul (cast_const sz) (cast_word e1)) (cast_const ofs).

Fixpoint alloc_e (m:map) (e: pexpr) :=
  match e with
  | Pconst _ | Pbool _ | Parr_init _ | Pglobal _ => ok e
  | Pvar   x =>
    match Mvar.get m.1 x with
    | Some ofs =>
      if is_word_type (vtype x) is Some ws then
        let ofs := cast_const ofs in
        let stk := {| v_var := vstk m; v_info := x.(v_info) |} in
        ok (Pload ws stk ofs)
      else not_a_word_v
    | None     =>
      if is_vstk m x then stk_not_fresh
      else ok e
    end
  | Pget ws x e1 =>
    Let e1 := alloc_e m e1 in
    match Mvar.get m.1 x with
    | Some ofs =>
      if is_align (wrepr _ ofs) ws then
        let stk := {| v_var := vstk m; v_info := x.(v_info) |} in
        let ofs := mk_ofs ws e1 ofs in
        ok (Pload ws stk ofs)
      else not_aligned

    | None =>
      if is_vstk m x then stk_not_fresh
      else ok (Pget ws x e1)
    end

  | Pload ws x e1 =>
    if check_var m x then
      Let e1 := alloc_e m e1 in
      ok (Pload ws x e1)
    else invalid_var

  | Papp1 o e1 =>
    Let e1 := alloc_e m e1 in
    ok (Papp1 o e1)

  | Papp2 o e1 e2 =>
    Let e1 := alloc_e m e1 in
    Let e2 := alloc_e m e2 in
    ok (Papp2 o e1 e2)

  | PappN o es =>
    Let es := mapM (alloc_e m) es in
    ok (PappN o es)

  | Pif t e e1 e2 =>
    Let e := alloc_e m e in
    Let e1 := alloc_e m e1 in
    Let e2 := alloc_e m e2 in
    ok (Pif t e e1 e2)
  end.

Definition alloc_lval (m:map) (r:lval) ty :=
  match r with
  | Lnone _ _ => ok r

  | Lvar x =>
    match Mvar.get m.1 x with
    | Some ofs =>
      if is_word_type (vtype x) is Some ws then
        if ty == sword ws then
          let ofs := cast_const ofs in
          let stk := {| v_var := vstk m; v_info := x.(v_info) |} in
          ok (Lmem ws stk ofs)
        else cerror (Cerr_stk_alloc "invalid type for Lvar")
      else not_a_word_v
    | None     =>
      if is_vstk m x then stk_not_fresh
      else ok r
    end

  | Lmem ws x e1 =>
    if check_var m x then
      Let e1 := alloc_e m e1 in
      ok (Lmem ws x e1)
    else invalid_var

  | Laset ws x e1 =>
    Let e1 := alloc_e m e1 in
    match Mvar.get m.1 x with
    | Some ofs =>
      if is_align (wrepr _ ofs) ws then
        let stk := {| v_var := vstk m; v_info := x.(v_info) |} in
        let ofs := mk_ofs ws e1 ofs in
        ok (Lmem ws stk ofs)
      else not_aligned

    | None =>
      if is_vstk m x then stk_not_fresh
      else ok (Laset ws x e1)
    end

  end.

Definition bad_lval_number := Cerr_stk_alloc "invalid number of lval".

Fixpoint alloc_i (m: map) (i: instr) :=
  let (ii, ir) := i in
  Let ir :=
    match ir with
    | Cassgn r t ty e =>
      Let r := add_iinfo ii (alloc_lval m r ty) in
      Let e := add_iinfo ii (alloc_e m e) in
      ok (Cassgn r t ty e)

    | Copn rs t o e =>
      Let rs := add_iinfo ii (mapM2 bad_lval_number (alloc_lval m) rs (sopn_tout o)) in
      Let e  := add_iinfo ii (mapM  (alloc_e m) e) in
      ok (Copn rs t o e)

    | Cif e c1 c2 =>
      Let e := add_iinfo ii (alloc_e m e) in
      Let c1 := mapM (alloc_i m) c1 in
      Let c2 := mapM (alloc_i m) c2 in
      ok (Cif e c1 c2)

    | Cwhile a c1 e c2 =>
      Let e := add_iinfo ii (alloc_e m e) in
      Let c1 := mapM (alloc_i m) c1 in
      Let c2 := mapM (alloc_i m) c2 in
      ok (Cwhile a c1 e c2)

    | Cfor _ _ _  => cierror ii (Cerr_stk_alloc "don't deal with for loop")
    | Ccall _ _ _ _ => cierror ii (Cerr_stk_alloc "don't deal with call")
    end in
  ok (MkI ii ir).


Definition add_err_fun (A : Type) (f : funname) (r : cexec A) :=
  match r with
  | ok _ a => ok a
  | Error e => Error (Ferr_fun f e)
  end.

Definition alloc_fd (stk_alloc_fd :
   fun_decl -> Z * Ident.ident * list (var * Z) * (list var * saved_stack))
    (f: fun_decl) :=
  let info := stk_alloc_fd f in
  let (fn, fd) := f in
  Let sfd :=
    let: (((size, stkid), l), saved):= info in
    Let m := add_err_fun fn (init_map size stkid l) in
    Let body := add_finfo fn fn (mapM (alloc_i m) fd.(f_body)) in
    if all (check_var m) fd.(f_params) && all (check_var m) fd.(f_res) then
      ok {| sf_iinfo  := fd.(f_iinfo);
            sf_stk_sz := size;
            sf_stk_id := stkid;
            sf_tyin   := fd.(f_tyin);
            sf_params := fd.(f_params);
            sf_body   := body;
            sf_tyout  := fd.(f_tyout);
            sf_res    := fd.(f_res);
            sf_extra  := saved;
         |}
    else add_err_fun fn invalid_var in
  ok (fn, sfd).

Definition alloc_prog stk_alloc_fd P :=
  mapM (alloc_fd stk_alloc_fd) P.(p_funcs).



