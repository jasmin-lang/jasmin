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

(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word utils type var expr memory.

Require Import compiler_util.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Record sfundef := MkSFun {
  sf_iinfo  : instr_info;
  sf_stk_sz : Z;
  sf_stk_id : Ident.ident; 
  sf_params : seq var_i;
  sf_body   : cmd;
  sf_res    : seq var_i;
}.

Definition sfundef_beq fd1 fd2 :=
  match fd1, fd2 with
  | MkSFun ii1 sz1 id1 p1 c1 r1, MkSFun ii2 sz2 id2 p2 c2 r2 =>
    (ii1 == ii2) && (sz1 == sz2) && (id1 == id2) &&
    (p1 == p2) && (c1 == c2) && (r1 == r2)
  end.

Lemma sfundef_eq_axiom : Equality.axiom sfundef_beq.
Proof.
  move=> [i1 s1 id1 p1 c1 r1] [i2 s2 id2 p2 c2 r2] /=.
  apply (@equivP ((i1 == i2) && (s1 == s2) && (id1 == id2) && (p1 == p2) && (c1 == c2) && (r1 == r2)));first by apply idP.
  by split=> [/andP[]/andP[]/andP[]/andP[]/andP[] | []] /eqP->/eqP->/eqP->/eqP->/eqP->/eqP->.
Qed.

Definition sfundef_eqMixin   := Equality.Mixin sfundef_eq_axiom.
Canonical  sfundef_eqType      := Eval hnf in EqType sfundef sfundef_eqMixin.

Definition sprog := seq (funname * sfundef).

Definition map := (Mvar.t Z * Ident.ident)%type.

Definition size_of (t:stype) := 
  match t with
  | sword  => ok 1%Z
  | sarr n => ok (Zpos n)
  | _      => cerror (Cerr_stk_alloc "size_of")
  end.

Definition init_map (sz:Z) (nstk:Ident.ident) (l:list (var * Z)):=
  let add (vp:var*Z) (mp:Mvar.t Z * Z) :=
    if (mp.2 <=? vp.2)%Z then 
      Let s := size_of (vtype vp.1) in
      cok (Mvar.set mp.1 vp.1 vp.2, vp.2 + s)%Z
    else cerror (Cerr_stk_alloc "overlap") in
  Let mp := foldM add (Mvar.empty Z, 0%Z) l in 
  if (mp.2 <=? sz)%Z then cok (mp.1, nstk)
  else cerror (Cerr_stk_alloc "stack size").

Definition is_in_stk (m:map) (x:var) :=
  match Mvar.get m.1 x with 
  | Some _ => true
  | None   => false
  end.

Definition vstk (m:map) :=  {|vtype := sword; vname := m.2|}.
Definition estk (m:map) := Pvar {|v_var := vstk m; v_info := xH|}.

Definition is_vstk (m:map) (x:var) :=
  x == (vstk m).

Definition check_var (m:map) (x1 x2:var_i) :=
  ~~ is_in_stk m x1 && (v_var x1 == v_var x2) && ~~is_vstk m x1.

Definition check_var_stk (m:map) (x1 x2:var_i) (e2:pexpr) := 
  is_vstk m x2 && (vtype x1 == sword) &&
    match Mvar.get m.1 x1 with
    | Some ofs => e2 == (Pcast (Pconst ofs))
    | _ => false
    end.

Definition is_arr_type (t:stype) := 
  match t with
  | sarr _ => true
  | _      => false
  end.

Definition check_arr_stk' check_e (m:map) (x1:var_i) (e1:pexpr) (x2:var_i) (e2:pexpr) :=
  is_vstk m x2 && is_arr_type (vtype x1) &&
    match Mvar.get m.1 x1 with
    | Some ofs =>
      match e2 with
      | Pcast (Papp2 (Oadd Op_int) (Pconst ofs') e2') => (ofs == ofs') && check_e m e1 e2'
      | _ => false
      end ||
      match e2 with
      | Pcast (Papp2 (Oadd Op_int) e2' (Pconst ofs')) => (ofs == ofs') && check_e m e1 e2'
      | _ => false
      end ||
      match e1 with
      | Pconst n => e2 == Pcast (Pconst (ofs + n)) 
      | _        => false
      end
    | _ => false
    end.

Fixpoint check_e (m:map) (e1 e2: pexpr) :=
  match e1, e2 with 
  | Pconst n1, Pconst n2 => n1 == n2 
  | Pbool  b1, Pbool  b2 => b1 == b2 
  | Pcast  e1, Pcast  e2 => check_e m e1 e2 
  | Pvar   x1, Pvar   x2 => check_var m x1 x2 
  | Pvar   x1, Pload x2 e2 => check_var_stk m x1 x2 e2
  | Pget  x1 e1, Pget x2 e2 => check_var m x1 x2 && check_e m e1 e2
  | Pget  x1 e1, Pload x2 e2 => check_arr_stk' check_e m x1 e1 x2 e2
  | Pload x1 e1, Pload x2 e2 => check_var m x1 x2 && check_e m e1 e2
  | Papp1 o1 e1, Papp1 o2 e2 => (o1 == o2) && check_e m e1 e2 
  | Papp2 o1 e11 e12, Papp2 o2 e21 e22 =>
    (o1 == o2) && check_e m e11 e21 && check_e m e12 e22
  | Pif e e1 e2, Pif e' e1' e2' => check_e m e e'  && check_e m e1 e1' && check_e m e2 e2' 
  | _, _ => false
  end.

Definition check_arr_stk := check_arr_stk' check_e.

Definition check_lval (m:map) (r1 r2:lval) := 
  match r1, r2 with
  | Lnone _, Lnone _ => true
  | Lvar x1, Lvar x2 => check_var m x1 x2
  | Lvar x1, Lmem x2 e2 => check_var_stk m x1 x2 e2
  | Lmem x1 e1, Lmem x2 e2 => check_var m x1 x2 && check_e m e1 e2
  | Laset x1 e1, Laset x2 e2 => check_var m x1 x2 && check_e m e1 e2
  | Laset x1 e1, Lmem x2 e2 => check_arr_stk m x1 e1 x2 e2
  | _, _ => false
  end.

Fixpoint check_i (m: map) (i1 i2: instr) : bool :=
  let (_, ir1) := i1 in
  let (_, ir2) := i2 in
  match ir1, ir2 with
  | Cassgn r1 _ e1, Cassgn r2 _ e2 => check_lval m r1 r2 && check_e m e1 e2
  | Copn rs1 o1 e1, Copn rs2 o2 e2 => all2 (check_lval m) rs1 rs2 && (o1 == o2) && all2 (check_e m) e1 e2
  | Cif e1 c1 c1', Cif e2 c2 c2' => check_e m e1 e2 && all2 (check_i m) c1 c2 && all2 (check_i m) c1' c2'
  | Cwhile c1 e1 c1', Cwhile c2 e2 c2' => all2 (check_i m) c1 c2 && check_e m e1 e2 && all2 (check_i m) c1' c2'
  | _, _ => false
  end.

Definition check_fd (l:list (var * Z))
    (fd: fundef) (fd': sfundef) :=
  match init_map (sf_stk_sz fd') (sf_stk_id fd') l with 
  | Ok m =>
     all2 (check_var m) (f_params fd) (sf_params fd') &&
     all2 (check_var m) (f_res fd) (sf_res fd') &&
     all2 (check_i m) (f_body fd) (sf_body fd')
  | _ => false
  end.

Definition check_prog P SP ll := all_prog P SP ll check_fd.
