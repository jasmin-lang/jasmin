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

(* * New semantic which is "unsafe" (may not fail on invalid code) but simplifies the Hoare logic *)

(* ** Imports and settings *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import ZArith.

Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr dmasm_sem.
Require Import memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope string_scope.

(* ** Type interpretation
 * -------------------------------------------------------------------- *)

Definition ssem_t (t : stype) : Type :=
  match t with
  | sbool  => bool
  | sint   => Z
  | sarr n => FArray.array word
  | sword  => word
  end.

Definition sdflt_val st : ssem_t st :=
  match st with
  | sbool         => false
  | sint          => Z0
  | sarr n        => FArray.cnst (n2w 0)
  | sword         => I64.repr Z0
  end.

(* ** Values
  * -------------------------------------------------------------------- *)

Inductive svalue : Type :=
  | SVbool :> bool -> svalue
  | SVint  :> Z    -> svalue
  | SVarr  : forall n : positive, FArray.array word -> svalue
  | SVword :> word -> svalue.

Definition svalues := seq svalue.

Definition sto_bool v :=
  match v with
  | SVbool b => ok b
  | _        => type_error
  end.

Definition sto_int v :=
  match v with
  | SVint z => ok z
  | _       => type_error
  end.

Definition sto_arr v :=
  match v with
  | SVarr n t => ok t
  | _         => type_error
  end.

Definition sto_word v :=
  match v with
  | SVword w => ok w
  | _        => type_error
  end.

Definition of_sval t : svalue -> exec (ssem_t t) :=
  match t return svalue -> exec (ssem_t t) with
  | sbool  => sto_bool
  | sint   => sto_int
  | sarr n => sto_arr
  | sword  => sto_word
  end.

Definition to_sval t : ssem_t t -> svalue :=
  match t return ssem_t t -> svalue with
  | sbool  => SVbool
  | sint   => SVint
  | sarr n => @SVarr n
  | sword  => SVword
  end.

(* ** Variable map
 * -------------------------------------------------------------------- *)

Notation svmap    := (Fv.t ssem_t).
Notation svmap0   := (@Fv.empty ssem_t (fun x => sdflt_val x.(vtype))).

Definition sget_var (m:svmap) x :=
  @to_sval (vtype x) (m.[x]%vmap).

Definition sset_var (m:svmap) x v :=
  Let v := @of_sval (vtype x) v in
  ok (m.[x<-v]%vmap).

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Definition ssem_prod ts tr := lprod (map ssem_t ts) tr.

Definition mk_ssem_sop2 t1 t2 tr (o:ssem_t t1 -> ssem_t t2 -> ssem_t tr) v1 v2 :=
  Let v1 := of_sval t1 v1 in
  Let v2 := of_sval t2 v2 in
  ok (@to_sval tr (o v1 v2)).

Definition ssem_op2_b  := @mk_ssem_sop2 sbool sbool sbool.
Definition ssem_op2_i  := @mk_ssem_sop2 sint  sint  sint.
Definition ssem_op2_ib := @mk_ssem_sop2 sint  sint  sbool.

Definition ssem_sop2 (o:sop2) :=
  match o with
  | Oand => ssem_op2_b andb
  | Oor  => ssem_op2_b orb

  | Oadd => ssem_op2_i Z.add
  | Omul => ssem_op2_i Z.mul
  | Osub => ssem_op2_i Z.sub

  | Oeq  => ssem_op2_ib Z.eqb
  | Oneq => ssem_op2_ib (fun x y => negb (Z.eqb x y))
  | Olt  => ssem_op2_ib Z.ltb
  | Ole  => ssem_op2_ib Z.leb
  | Ogt  => ssem_op2_ib Z.gtb
  | Oge  => ssem_op2_ib Z.geb
  end.

Record sestate := SEstate {
  semem : mem;
  sevm  : svmap
}.

Definition son_arr_var A (s:sestate) (x:var) (f:forall n, FArray.array word -> A) :=
  match vtype x as t return ssem_t t -> A with
  | sarr n => f n
  | _ => fun _ => f xH (FArray.cnst (n2w 0))
  end  (s.(sevm).[ x ]%vmap).

Notation "'SLet' ( n , t ) ':=' s '.[' x ']' 'in' body" :=
  (@son_arr_var _ s x (fun n (t:FArray.array word) => body)) (at level 25, s at level 0).

Definition sread_mem m w :=
  match (read_mem m w) with
  | Ok v => v
  | _ => I64.repr Z0
  end.

Definition swrite_mem m w w' :=
  match (write_mem m w w') with
  | Ok v => v
  | _ => m
  end.

Fixpoint ssem_pexpr (s:sestate) (e : pexpr) : exec svalue :=
  match e with
  | Pconst z => ok (SVint z)
  | Pbool b  => ok (SVbool b)
  | Pcast e  =>
    Let z := ssem_pexpr s e >>= sto_int in
    ok (SVword (I64.repr z))
  | Pvar v => ok (sget_var s.(sevm) v)
  | Pget x e =>
      SLet (n,t) := s.[x] in
      Let i := ssem_pexpr s e >>= sto_word in
      ok (SVword (FArray.get t i))
  | Pload x e =>
    (* FIXME: use x as offset *)
    Let x := ssem_pexpr s e >>= sto_word in
    let w := sread_mem s.(semem) x in
    ok (@to_sval sword w)
  | Pnot e =>
    Let b := ssem_pexpr s e >>= sto_bool in
    ok (SVbool (negb b))
  | Papp2 o e1 e2 =>
    Let v1 := ssem_pexpr s e1 in
    Let v2 := ssem_pexpr s e2 in
    ssem_sop2 o v1 v2
  end.

Definition ssem_pexprs s := mapM (ssem_pexpr s).

Definition swrite_var (x:var_i) (v:svalue) (s:sestate) : exec sestate :=
  Let vm := sset_var s.(sevm) x v in
  ok {| semem := s.(semem); sevm := vm |}.

Definition swrite_vars xs vs s :=
  fold2 ErrType swrite_var xs vs s.

Definition swrite_rval  (l:rval) (v:svalue) (s:sestate) : exec sestate :=
  match l with
  | Rnone _ => ok s
  | Rvar x => swrite_var x v s
  | Rmem x e =>
    Let vx := sto_word (sget_var (sevm s) x) in
    Let ve := ssem_pexpr s e >>= sto_word in
    let p := wadd vx ve in (* should we add the size of value, i.e vx + sz * se *)
    Let w := sto_word v in
    let m := swrite_mem s.(semem) p w in
    ok {|semem := m;  sevm := s.(sevm) |}
  | Raset x i =>
    SLet (n,t) := s.[x] in
    Let i := ssem_pexpr s i >>= sto_word in
    Let v := sto_word v in
    let t := FArray.set t i v in
    Let vm := sset_var s.(sevm) x (@to_sval (sarr n) t) in
    ok {| semem := s.(semem); sevm := vm |}
  end.

Definition swrite_rvals (s:sestate) xs vs :=
   fold2 ErrType swrite_rval xs vs s.

Fixpoint sapp_sopn ts : ssem_prod ts svalues -> svalues -> exec svalues :=
  match ts return ssem_prod ts svalues -> svalues -> exec svalues with
  | [::] => fun (o:svalues) (vs:svalues) =>
    match vs with
    | [::] => ok o
    | _    => type_error
    end
  | t::ts => fun (o:ssem_t t -> ssem_prod ts svalues) (vs:svalues) =>
    match vs with
    | [::]  => type_error
    | v::vs =>
      Let v := of_sval t v in
      sapp_sopn (o v) vs
    end
  end.
Arguments sapp_sopn ts o l:clear implicits.

Definition spval t1 t2 (p: ssem_t t1 * ssem_t t2) :=
  [::to_sval p.1; to_sval p.2].

Notation soww o  := (sapp_sopn [::sword] (fun x => [::SVword (o x)])).
Notation sowww o := (sapp_sopn [:: sword; sword] (fun x y => [::SVword (o x y)])).

Definition ssem_sopn (o:sopn) : svalues -> exec svalues :=
  match o with
  | Olnot => soww I64.not
  | Oxor  => sowww I64.xor
  | Oland => sowww I64.and
  | Olor  => sowww I64.or
  | Olsr  => sowww I64.shru
  | Olsl  => sowww I64.shl
  | Omuli => sowww (fun x y => let (h,l) := wumul x y in l) (* FIXME: check imul INTEL manual *)
  | Oif   =>
    sapp_sopn [::sbool; sword; sword] (fun b x y => [::SVword (if b then x else y)])
  | Omulu =>
    sapp_sopn [::sword; sword] (fun x y => @spval sword sword (wumul x y))
  | Oaddcarry =>
    sapp_sopn [::sword; sword; sbool] (fun x y c => @spval sbool sword (waddcarry x y c))
  | Osubcarry =>
    sapp_sopn [::sword; sword; sbool] (fun x y c => @spval sbool sword (wsubcarry x y c))
  end.

(* ** Instructions
 * -------------------------------------------------------------------- *)

Section SEM.

Variable P:prog.

Definition get_fundef f :=
  let pos := find (fun ffd => f == fst ffd) P in
  if pos <= size P then
    Some (snd (nth (xH,dummy_fundef) P pos))
  else None.

Inductive ssem : sestate -> cmd -> sestate -> Prop :=
| SEskip s :
    ssem s [::] s

| SEseq s1 s2 s3 i c :
    ssem_I s1 i s2 -> ssem s2 c s3 -> ssem s1 (i::c) s3

with ssem_I : sestate -> instr -> sestate -> Prop :=
| SEmkI ii i s1 s2:
    ssem_i s1 i s2 ->
    ssem_I s1 (MkI ii i) s2

with ssem_i : sestate -> instr_r -> sestate -> Prop :=
| SEassgn s1 s2 (x:rval) tag e:
    (Let v := ssem_pexpr s1 e in swrite_rval x v s1) = ok s2 ->
    ssem_i s1 (Cassgn x tag e) s2

| SEopn s1 s2 o xs es:
    ssem_pexprs s1 es >>= ssem_sopn o >>= (swrite_rvals s1 xs) = ok s2 ->
    ssem_i s1 (Copn xs o es) s2

| SEif_true s1 s2 e c1 c2 :
    ssem_pexpr s1 e >>= sto_bool = ok true ->
    ssem s1 c1 s2 ->
    ssem_i s1 (Cif e c1 c2) s2

| SEif_false s1 s2 e c1 c2 :
    ssem_pexpr s1 e >>= sto_bool = ok false ->
    ssem s1 c2 s2 ->
    ssem_i s1 (Cif e c1 c2) s2

| SEwhile_true s1 s2 s3 e c :
    ssem_pexpr s1 e >>= sto_bool = ok true ->
    ssem s1 c s2 ->
    ssem_i s2 (Cwhile e c) s3 ->
    ssem_i s1 (Cwhile e c) s3

| SEwhile_false s e c :
    ssem_pexpr s e >>= sto_bool = ok false ->
    ssem_i s (Cwhile e c) s

| SEfor s1 s2 (i:var_i) d lo hi c vlo vhi :
    ssem_pexpr s1 lo >>= sto_int = ok vlo ->
    ssem_pexpr s1 hi >>= sto_int = ok vhi ->
    ssem_for i (wrange d vlo vhi) s1 c s2 ->
    ssem_i s1 (Cfor i (d, lo, hi) c) s2

| SEcall s1 m2 s2 ii xs f fd args vargs vs :
    get_fundef f = Some fd ->
    ssem_pexprs s1 args = ok vargs ->
    ssem_call s1.(semem) fd vargs m2 vs ->
    swrite_rvals {|semem:= m2; sevm := s1.(sevm) |} xs vs = ok s2 ->
    ssem_i s1 (Ccall ii xs f args) s2

with ssem_for : var -> seq Z -> sestate -> cmd -> sestate -> Prop :=
| SEForDone s i c :
    ssem_for i [::] s c s

| SEForOne s1 s1' s2 s3 i w ws c :
    swrite_var i (SVint w) s1 = ok s1' ->
    ssem s1' c s2 ->
    ssem_for i ws s2 c s3 ->
    ssem_for i (w :: ws) s1 c s3

with ssem_call : mem -> fundef -> seq svalue -> mem -> seq svalue -> Prop :=
| SEcallRun m1 m2 f vargs vres:
    (* semantics defined for all vm0 *)
    (forall vm0, (* TODO: check: all_empty_arr vm0 -> *)
       exists s1 vm2, [/\
        swrite_vars f.(f_params) vargs (SEstate m1 vm0) = ok s1,
        ssem s1 f.(f_body) (SEstate m2 vm2) &
        map (fun (x:var_i) => sget_var vm2 x) f.(f_res) = vres]) ->
    (*TODO: check: List.Forall is_full_array vres -> *)
    ssem_call m1 f vargs m2 vres.

End SEM.
