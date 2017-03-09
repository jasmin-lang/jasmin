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

(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import ZArith.

Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Interpretation of types
 * -------------------------------------------------------------------- *)

Module FArray.

  Definition array (T:Type) := Z -> T.

  Definition cnst {T} (t:T) : array T := fun i => t.

  Definition get {T} (a:array T) (i:Z) := a i.

  Definition set {T} (a:array T) (i:Z) (v:T) :=
    fun j => if i == j  then v else a j.
  
  Lemma setP {T} (a:array T) (w1 w2:Z) (t:T):
    get (set a w1 t) w2 = if w1 == w2 then t else get a w2.
  Proof. done. Qed.

  Lemma setP_eq {T} (a:array T) w (t:T):
    get (set a w t) w = t.
  Proof. by rewrite setP eq_refl. Qed.

  Lemma setP_neq {T} (a:array T) w1 w2 (t:T): 
    w1 != w2 -> get (set a w1 t) w2 = get a w2.
  Proof. by rewrite setP=> /negPf ->. Qed.

  (* FIXME *)
  Axiom eq_ext : forall T (t1 t2:array T), (forall x, get t1 x = get t2 x) -> t1 = t2.

End FArray.

Module Array.

  Definition array (s:positive) T := FArray.array (exec T).

  Definition empty {T:Type} (s:positive) : array s T := FArray.cnst (Error ErrAddrUndef).

  Definition make {T:Type} (s:positive) (t:T) : array s T :=  FArray.cnst (ok t). 

  Definition get {T} {s} (a:array s T) w : result error T := 
    if ((0 <=? w) && (w <? Zpos s))%Z then FArray.get a w
    else Error ErrOob.

  Definition set {T} s (a:array s T) x (v:T) : result error (array s T):=
    if ((0 <=? x) && (x <? Zpos s))%Z then ok (FArray.set a x (ok v))
    else Error ErrOob.

  Lemma getP_inv T s (a:array s T) x t: 
    get a x = ok t -> ((0 <=? x) && (x <? Zpos s))%Z.
  Proof. by rewrite /get;case: ifP. Qed.

  Lemma getP_empty T s x w: get (@empty T s) x <> ok w.
  Proof. by rewrite /get/empty;case:ifP. Qed.

  (* FIXME *)
  Axiom eq_ext : forall T s (t1 t2:array s T), (forall x, get t1 x = get t2 x) -> t1 = t2.

End Array.

Definition sem_t (t : stype) : Type :=   
  match t with
  | sbool  => bool
  | sint   => Z
  | sarr n => Array.array n word 
  | sword  => word
  end.

(* ** Default values
 * -------------------------------------------------------------------- *)

Definition dflt_val (t : stype) : sem_t t :=
  match t with
  | sbool         => false
  | sint          => Z0
  | sarr n        => @Array.empty word n
  | sword         => I64.repr Z0
  end.

Definition rdflt_ (t : stype) e (r : result e (sem_t t)) : sem_t t :=
  rdflt (dflt_val t) r.

(* ** Values
  * -------------------------------------------------------------------- *)

Inductive value : Type := 
  | Vbool :> bool -> value
  | Vint  :> Z    -> value
  | Varr  : forall n, Array.array n word -> value 
  | Vword :> word -> value.

Definition values := seq value.

Definition type_error {t} := @Error _ t ErrType.

Definition to_bool v :=
  match v with
  | Vbool b => ok b
  | _       => type_error
  end.

Definition to_int v :=
  match v with
  | Vint z => ok z
  | _      => type_error
  end.

Definition to_arr n v : exec (Array.array n word) :=
  match v with
  | Varr n' t => 
    match CEDecStype.pos_dec n' n with
    | left H => 
      ok (eq_rect n' (fun p => Array.array p word) t n H)
    | _      => type_error
    end
  | _ => type_error
  end.

Definition to_word v := 
  match v with
  | Vword w => ok w
  | _       => type_error
  end.

Definition of_val t : value -> exec (sem_t t) :=
  match t return value -> exec (sem_t t) with
  | sbool  => to_bool
  | sint   => to_int
  | sarr n => to_arr n
  | sword  => to_word
  end.

Definition to_val t : sem_t t -> value := 
  match t return sem_t t -> value with 
  | sbool  => Vbool
  | sint   => Vint
  | sarr n => @Varr n
  | sword  => Vword
  end.

(* ** Variable map
 * -------------------------------------------------------------------- *)

Notation vmap     := (Fv.t (fun t => exec (sem_t t))).

Definition undef_addr t := 
  match t return exec (sem_t t) with
  | sbool | sint | sword => Error ErrAddrUndef
  | sarr n => ok (Array.empty n)
  end.

Definition vmap0  := 
  @Fv.empty (fun t => exec (sem_t t)) (fun x => undef_addr x.(vtype)).

Definition get_var (m:vmap) x := 
  Let v := (m.[x]%vmap) in ok (@to_val (vtype x) v).

Definition set_var (m:vmap) x v := 
  Let v := @of_val (vtype x) v in
  ok (m.[x<-ok v]%vmap).

Definition is_full_array v := 
  match v with
  | Varr n t => 
    forall p, (0 <= p < Zpos n)%Z -> exists w, Array.get t p = ok w
  | _ => True
  end.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Definition lprod ts tr := 
  foldr (fun t tr => t -> tr) tr ts.

Definition sem_prod ts tr := lprod (map sem_t ts) tr.
 
Definition mk_sem_sop2 t1 t2 tr (o:sem_t t1 -> sem_t t2 -> sem_t tr) v1 v2 :=
  Let v1 := of_val t1 v1 in
  Let v2 := of_val t2 v2 in
  ok (@to_val tr (o v1 v2)).

Definition sem_op2_b  := @mk_sem_sop2 sbool sbool sbool.
Definition sem_op2_i  := @mk_sem_sop2 sint  sint  sint.
Definition sem_op2_ib := @mk_sem_sop2 sint  sint  sbool.

Definition sem_sop2 (o:sop2) :=
  match o with
  | Oand => sem_op2_b andb     
  | Oor  => sem_op2_b orb

  | Oadd => sem_op2_i Z.add
  | Omul => sem_op2_i Z.mul
  | Osub => sem_op2_i Z.sub

  | Oeq  => sem_op2_ib Z.eqb
  | Oneq => sem_op2_ib (fun x y => negb (Z.eqb x y))
  | Olt  => sem_op2_ib Z.ltb
  | Ole  => sem_op2_ib Z.leb
  | Ogt  => sem_op2_ib Z.gtb
  | Oge  => sem_op2_ib Z.geb
  end.

Import Memory.

Record estate := Estate {
  emem : mem;
  evm  : vmap
}.

Definition on_arr_var A (s:estate) (x:var) (f:forall n, Array.array n word -> exec A) :=
  Let v := get_var s.(evm) x in  
  match v with
  | Varr n t => f n t
  | _ => type_error
  end.
 
Notation "'Let' ( n , t ) ':=' s '.[' x ']' 'in' body" :=
  (@on_arr_var _ s x (fun n (t:Array.array n word) => body)) (at level 25, s at level 0).

Lemma on_arr_varP A (f : forall n : positive, Array.array n word -> exec A) v s x P:
  (forall n t, vtype x = sarr n -> 
               get_var (evm s) x = ok (@Varr n t) ->
               f n t = ok v -> P) -> 
  on_arr_var s x f = ok v -> P.
Proof. 
  rewrite /on_arr_var=> H;apply: rbindP => vx.
  rewrite /get_var;case: x H => -[ | | n | ] nx H; apply:rbindP => ? Hnx [] <- //.
  by apply H;rewrite // /get_var Hnx.
Qed.

Definition Varr_inj n n' t t' : @Varr n t = @Varr n' t' -> n = n' /\ t = t' :=
  fun e => let 'Logic.eq_refl := e in conj Logic.eq_refl Logic.eq_refl.

Lemma Varr_inj1 n t t' : @Varr n t = @Varr n t' -> t = t'.
Proof. by move=> /Varr_inj []. Qed.

Fixpoint sem_pexpr (s:estate) (e : pexpr) : exec value :=
  match e with
  | Pconst z => ok (Vint z)
  | Pbool b  => ok (Vbool b)
  | Pcast e  => 
    Let z := sem_pexpr s e >>= to_int in
    ok (Vword (I64.repr z))  
  | Pvar v => get_var s.(evm) v
  | Pget x e => 
      Let (n,t) := s.[x] in
      Let i := sem_pexpr s e >>= to_int in
      Let w := Array.get t i in
      ok (Vword w)
  | Pload x e =>
    (* FIXME: use x as offset *)
    Let w := sem_pexpr s e >>= to_word >>= read_mem s.(emem) in
    ok (@to_val sword w)
  | Pnot e => 
    Let b := sem_pexpr s e >>= to_bool in 
    ok (Vbool (negb b))
  | Papp2 o e1 e2 =>
    Let v1 := sem_pexpr s e1 in
    Let v2 := sem_pexpr s e2 in
    sem_sop2 o v1 v2
  end.

Definition sem_pexprs s := mapM (sem_pexpr s).

Definition write_var (x:var_i) (v:value) (s:estate) : exec estate :=
  Let vm := set_var s.(evm) x v in
  ok ({| emem := s.(emem); evm := vm |}).

Definition write_vars xs vs s := 
  fold2 ErrType write_var xs vs s.

Definition write_rval (l:rval) (v:value) (s:estate) : exec estate :=
  match l with 
  | Rnone _ => ok s
  | Rvar x => write_var x v s
  | Rmem x e =>  
    Let vx := get_var (evm s) x >>= to_word in
    Let ve := sem_pexpr s e >>= to_word in
    let p := wadd vx ve in (* should we add the size of value, i.e vx + sz * se *)
    Let w := to_word v in
    Let m :=  write_mem s.(emem) p w in
    ok {|emem := m;  evm := s.(evm) |}
  | Raset x i =>
    Let (n,t) := s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let v := to_word v in
    Let t := Array.set t i v in
    Let vm := set_var s.(evm) x (@to_val (sarr n) t) in 
    ok ({| emem := s.(emem); evm := vm |})
  end.
 
Definition write_rvals (s:estate) xs vs := 
   fold2 ErrType write_rval xs vs s.

Fixpoint app_sopn ts : sem_prod ts values -> values -> exec values := 
  match ts return sem_prod ts values -> values -> exec values with
  | [::] => fun (o:values) (vs:values) => 
    match vs with 
    | [::] => ok o
    | _    => type_error
    end
  | t::ts => fun (o:sem_t t -> sem_prod ts values) (vs:values) =>
    match vs with
    | [::]  => type_error
    | v::vs => 
      Let v := of_val t v in
      app_sopn (o v) vs
    end
  end.
Arguments app_sopn ts o l:clear implicits.

Definition pval t1 t2 (p: sem_t t1 * sem_t t2) :=
  [::to_val p.1; to_val p.2].

Notation oww o  := (app_sopn [::sword] (fun x => [::Vword (o x)])).
Notation owww o := (app_sopn [:: sword; sword] (fun x y => [::Vword (o x y)])).

Definition sem_sopn (o:sopn) :  values -> exec values :=
  match o with
  | Olnot => oww I64.not
  | Oxor  => owww I64.xor
  | Oland => owww I64.and 
  | Olor  => owww I64.or
  | Olsr  => owww I64.shru
  | Olsl  => owww I64.shl
  | Omuli => owww (fun x y => let (h,l) := wumul x y in l) (* FIXME: check imul INTEL manual *)
  | Oif   => 
    app_sopn [::sbool; sword; sword] (fun b x y => [::Vword (if b then x else y)])
  | Omulu => 
    app_sopn [::sword; sword] (fun x y => @pval sword sword (wumul x y))
  | Oaddcarry =>
    app_sopn [::sword; sword; sbool] (fun x y c => @pval sbool sword (waddcarry x y c))
  | Osubcarry =>
    app_sopn [::sword; sword; sbool] (fun x y c => @pval sbool sword (wsubcarry x y c))
  end.

(* ** Instructions
 * -------------------------------------------------------------------- *)

Section SEM. 

Variable P:prog.

Definition wrange d (n1 n2 : Z) :=
  if (n1 <? n2)%Z then 
    let idxs := mkseq (fun n => n1 + Z.of_nat n)%Z (Z.to_nat (n2 - n1)) in
    match d with
    | UpTo   => idxs
    | DownTo => rev idxs
    end
  else [::].

Definition sem_range (s : estate) (r : range) :=
  let: (d,pe1,pe2) := r in
  Let i1 := sem_pexpr s pe1 >>= to_int in
  Let i2 := sem_pexpr s pe2 >>= to_int in 
  ok (wrange d i1 i2).
 
Inductive sem : estate -> cmd -> estate -> Prop :=
| Eskip s :
    sem s [::] s

| Eseq s1 s2 s3 i c :
    sem_I s1 i s2 -> sem s2 c s3 -> sem s1 (i::c) s3

with sem_I : estate -> instr -> estate -> Prop :=
| EmkI ii i s1 s2: 
    sem_i s1 i s2 ->
    sem_I s1 (MkI ii i) s2

with sem_i : estate -> instr_r -> estate -> Prop :=
| Eassgn s1 s2 (x:rval) tag e:
    (Let v := sem_pexpr s1 e in write_rval x v s1) = ok s2 -> 
    sem_i s1 (Cassgn x tag e) s2

| Eopn s1 s2 o xs es:
    sem_pexprs s1 es >>= sem_sopn o >>= (write_rvals s1 xs) = ok s2 ->
    sem_i s1 (Copn xs o es) s2

| Eif_true s1 s2 e c1 c2 :
    sem_pexpr s1 e >>= to_bool = ok true ->
    sem s1 c1 s2 ->
    sem_i s1 (Cif e c1 c2) s2

| Eif_false s1 s2 e c1 c2 :
    sem_pexpr s1 e >>= to_bool = ok false ->
    sem s1 c2 s2 ->
    sem_i s1 (Cif e c1 c2) s2

| Ewhile_true s1 s2 s3 e c :
    sem_pexpr s1 e >>= to_bool = ok true ->
    sem s1 c s2 ->
    sem_i s2 (Cwhile e c) s3 ->
    sem_i s1 (Cwhile e c) s3

| Ewhile_false s e c :
    sem_pexpr s e >>= to_bool = ok false ->
    sem_i s (Cwhile e c) s

| Efor s1 s2 (i:var_i) d lo hi c vlo vhi :
    sem_pexpr s1 lo >>= to_int = ok vlo ->
    sem_pexpr s1 hi >>= to_int = ok vhi ->
    sem_for i (wrange d vlo vhi) s1 c s2 ->
    sem_i s1 (Cfor i (d, lo, hi) c) s2

| Ecall s1 m2 s2 ii xs f args vargs vs : 
    sem_pexprs s1 args = ok vargs ->
    sem_call s1.(emem) f vargs m2 vs ->
    write_rvals {|emem:= m2; evm := s1.(evm) |} xs vs = ok s2 ->
    sem_i s1 (Ccall ii xs f args) s2

with sem_for : var_i -> seq Z -> estate -> cmd -> estate -> Prop :=
| EForDone s i c :
    sem_for i [::] s c s

| EForOne s1 s1' s2 s3 i w ws c :
    write_var i (Vint w) s1 = ok s1' ->
    sem s1' c s2 ->
    sem_for i ws s2 c s3 ->
    sem_for i (w :: ws) s1 c s3

with sem_call : mem -> funname -> seq value -> mem -> seq value -> Prop := 
| EcallRun m1 m2 fn f vargs s1 vm2 vres:
    get_fundef P fn = Some f ->
    write_vars f.(f_params) vargs (Estate m1 vmap0) = ok s1 -> 
    sem s1 f.(f_body) (Estate m2 vm2) ->
    mapM (fun (x:var_i) => get_var vm2 x) f.(f_res) = ok vres ->
    List.Forall is_full_array vres ->
    sem_call m1 fn vargs m2 vres.

(* -------------------------------------------------------------------- *)
(* The generated scheme is borring to use *)
(*
Scheme sem_Ind    := Induction for sem      Sort Prop
with sem_i_Ind    := Induction for sem_i    Sort Prop
with sem_I_Ind    := Induction for sem_I    Sort Prop
with sem_for_Ind  := Induction for sem_for  Sort Prop
with sem_call_Ind := Induction for sem_call Sort Prop.
*)

Section SEM_IND.
  Variables
    (Pc   : estate -> cmd -> estate -> Prop)
    (Pi_r : estate -> instr_r -> estate -> Prop)
    (Pi : estate -> instr -> estate -> Prop)
    (Pfor : var_i -> seq Z -> estate -> cmd -> estate -> Prop)
    (Pfun : mem -> funname -> seq value -> mem -> seq value -> Prop).
 
  Hypothesis Hnil : forall s : estate, Pc s [::] s.

  Hypothesis Hcons : forall (s1 s2 s3 : estate) (i : instr) (c : cmd),
    sem_I s1 i s2 -> Pi s1 i s2 -> sem s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.

  Hypothesis HmkI : forall (ii : instr_info) (i : instr_r) (s1 s2 : estate),
    sem_i s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.

  Hypothesis Hasgn : forall (s1 s2 : estate) (x : rval) (tag : assgn_tag) (e : pexpr),
    Let v := sem_pexpr s1 e in write_rval x v s1 = Ok error s2 ->
    Pi_r s1 (Cassgn x tag e) s2.

  Hypothesis Hopn : forall (s1 s2 : estate) (o : sopn) (xs : rvals) (es : pexprs),
    Let x := Let x := sem_pexprs s1 es in sem_sopn o x in write_rvals s1 xs x = Ok error s2 -> 
    Pi_r s1 (Copn xs o es) s2.

  Hypothesis Hif_true : forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.

  Hypothesis Hif_false : forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    Let x := sem_pexpr s1 e in to_bool x = Ok error false ->
    sem s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.

  Hypothesis Hwhile_true : forall (s1 s2 s3 : estate) (e : pexpr) (c : cmd),
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem s1 c s2 -> Pc s1 c s2 ->
    sem_i s2 (Cwhile e c) s3 -> Pi_r s2 (Cwhile e c) s3 -> Pi_r s1 (Cwhile e c) s3.

  Hypothesis Hwhile_false : forall (s : estate) (e : pexpr) (c : cmd),
    Let x := sem_pexpr s e in to_bool x = Ok error false ->
    Pi_r s (Cwhile e c) s.

  Hypothesis Hfor : forall (s1 s2 : estate) (i : var_i) (d : dir) 
         (lo hi : pexpr) (c : cmd) (vlo vhi : Z),
    Let x := sem_pexpr s1 lo in to_int x = Ok error vlo ->
    Let x := sem_pexpr s1 hi in to_int x = Ok error vhi ->
    sem_for i (wrange d vlo vhi) s1 c s2 ->
    Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.

  Hypothesis Hfor_nil : forall (s : estate) (i : var_i) (c : cmd), Pfor i [::] s c s.

  Hypothesis Hfor_cons : forall (s1 s1' s2 s3 : estate) (i : var_i) 
         (w : Z) (ws : seq Z) (c : cmd),
    write_var i w s1 = Ok error s1' ->
    sem s1' c s2 -> Pc s1' c s2 ->
    sem_for i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.

  Hypothesis Hcall : forall (s1 : estate) (m2 : mem) (s2 : estate) 
         (ii : inline_info) (xs : rvals) 
         (fn : funname) (args : pexprs) (vargs vs : seq value),
    sem_pexprs s1 args = Ok error vargs ->
    sem_call (emem s1) fn vargs m2 vs -> Pfun (emem s1) fn vargs m2 vs ->
    write_rvals {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
    Pi_r s1 (Ccall ii xs fn args) s2.

  Hypothesis Hproc : forall (m1 m2 : mem) (fn:funname) (f : fundef) (vargs : seq value)
         (s1 : estate) (vm2 : vmap) (vres : seq value),
    get_fundef P fn = Some f ->
    write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
    sem s1 (f_body f) {| emem := m2; evm := vm2 |} -> 
    Pc s1 (f_body f) {| emem := m2; evm := vm2 |} ->
    mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
    List.Forall is_full_array vres -> 
    Pfun m1 fn vargs m2 vres.

  Fixpoint sem_Ind (e : estate) (l : cmd) (e0 : estate) (s : sem e l e0) {struct s} :
    Pc e l e0 :=
    match s in (sem e1 l0 e2) return (Pc e1 l0 e2) with
    | Eskip s0 => Hnil s0
    | @Eseq s1 s2 s3 i c s0 s4 =>
        @Hcons s1 s2 s3 i c s0 (@sem_I_Ind s1 i s2 s0) s4 (@sem_Ind s2 c s3 s4)
    end

  with sem_i_Ind (e : estate) (i : instr_r) (e0 : estate) (s : sem_i e i e0) {struct s} :
    Pi_r e i e0 :=
    match s in (sem_i e1 i0 e2) return (Pi_r e1 i0 e2) with
    | @Eassgn s1 s2 x tag e1 e2 => @Hasgn s1 s2 x tag e1 e2
    | @Eopn s1 s2 o xs es e1 => @Hopn s1 s2 o xs es e1
    | @Eif_true s1 s2 e1 c1 c2 e2 s0 => 
      @Hif_true s1 s2 e1 c1 c2 e2 s0 (@sem_Ind s1 c1 s2 s0)
    | @Eif_false s1 s2 e1 c1 c2 e2 s0 => 
      @Hif_false s1 s2 e1 c1 c2 e2 s0 (@sem_Ind s1 c2 s2 s0)
    | @Ewhile_true s1 s2 s3 e1 c e2 s0 s4 =>
      @Hwhile_true s1 s2 s3 e1 c e2 s0 (@sem_Ind s1 c s2 s0) s4 
      (@sem_i_Ind s2 (Cwhile e1 c) s3 s4)
    | @Ewhile_false s0 e1 c e2 => @Hwhile_false s0 e1 c e2
    | @Efor s1 s2 i0 d lo hi c vlo vhi e1 e2 s0 =>
      @Hfor s1 s2 i0 d lo hi c vlo vhi e1 e2 s0
        (@sem_for_Ind i0 (wrange d vlo vhi) s1 c s2 s0)
    | @Ecall s1 m2 s2 ii xs f13 args vargs vs e2 s0 e3 =>
      @Hcall s1 m2 s2 ii xs f13 args vargs vs e2 s0
        (@sem_call_Ind (emem s1) f13 vargs m2 vs s0) e3
    end

  with sem_I_Ind (e : estate) (i : instr) (e0 : estate) (s : sem_I e i e0) {struct s} :
    Pi e i e0 :=
    match s in (sem_I e1 i0 e2) return (Pi e1 i0 e2) with
    | @EmkI ii i0 s1 s2 s0 => @HmkI ii i0 s1 s2 s0 (@sem_i_Ind s1 i0 s2 s0)
    end

  with sem_for_Ind (v : var_i) (l : seq Z) (e : estate) (l0 : cmd) (e0 : estate)
         (s : sem_for v l e l0 e0) {struct s} : Pfor v l e l0 e0 :=
    match s in (sem_for v0 l1 e1 l2 e2) return (Pfor v0 l1 e1 l2 e2) with
    | EForDone s0 i c => Hfor_nil s0 i c
    | @EForOne s1 s1' s2 s3 i w ws c e1 s0 s4 =>
      @Hfor_cons s1 s1' s2 s3 i w ws c e1 s0 (@sem_Ind s1' c s2 s0)
         s4 (@sem_for_Ind i ws s2 c s3 s4)
    end

  with sem_call_Ind (m : mem) (f13 : funname) (l : seq value) (m0 : mem) 
         (l0 : seq value) (s : sem_call m f13 l m0 l0) {struct s} : Pfun m f13 l m0 l0 :=
    match s with 
    | @EcallRun m1 m2 fn f vargs s1 vm2 vres Hget Hw Hsem Hmap Hvres =>
       @Hproc m1 m2 fn f vargs s1 vm2 vres Hget Hw Hsem (sem_Ind Hsem) Hmap Hvres 
    end.

End SEM_IND. 

(* -------------------------------------------------------------------- *)

Lemma sem_app l1 l2 s1 s2 s3:
  sem s1 l1 s2 -> sem s2 l2 s3 ->
  sem s1 (l1 ++ l2) s3.
Proof.
  elim: l1 s1;first by move=> s1 H1;inversion H1.
  move=> a l Hrec s1 H1;inversion H1;subst;clear H1 => /= Hl2.
  by apply (Eseq H3);apply Hrec.
Qed.

Lemma sem_seq1 i s1 s2:
  sem_I s1 i s2 -> sem s1 [::i] s2.
Proof.
  move=> Hi; apply (Eseq Hi);constructor.
Qed.

Definition vmap_eq_except (s : Sv.t) (vm1 vm2 : vmap) :=
  forall x, ~Sv.In x s -> vm1.[x]%vmap = vm2.[x]%vmap.

Notation "vm1 = vm2 [\ s ]" := (vmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Lemma vmap_eq_exceptT vm2 s vm1 vm3:
  vm1 = vm2 [\s] -> vm2 = vm3 [\s] -> vm1 = vm3 [\s].
Proof. by move=> H1 H2 x Hin;rewrite H1 ?H2. Qed.

Lemma vmap_eq_exceptI s1 s2 vm1 vm2 : Sv.Subset s1 s2 -> vm1 = vm2 [\s1] -> vm1 = vm2 [\s2].
Proof. move=> Hs Heq x Hin;apply Heq;SvD.fsetdec. Qed.

Lemma vmap_eq_exceptS vm1 s vm2 : vm1 = vm2 [\s] -> vm2 = vm1 [\s].
Proof. by move=> Heq x Hin;rewrite Heq. Qed.

Global Instance equiv_vmap_eq_except s: Equivalence (vmap_eq_except s).
Proof.
  constructor=> //.
  move=> ??;apply: vmap_eq_exceptS.
  move=> ???;apply: vmap_eq_exceptT.
Qed.

Global Instance vmap_eq_except_impl :
  Proper (Sv.Subset ==> eq ==> eq ==> Basics.impl) vmap_eq_except.
Proof. by move=> s1 s2 H vm1 ? <- vm2 ? <-;apply: vmap_eq_exceptI. Qed.

Global Instance vmap_eq_except_m : Proper (Sv.Equal ==> eq ==> eq ==> iff) vmap_eq_except.
Proof. by move=> s1 s2 Heq vm1 ? <- vm2 ? <-;split;apply: vmap_eq_exceptI;rewrite Heq. Qed.

Lemma vrvP_var (x:var_i) v s1 s2 :
  write_var x v s1 = ok s2 -> 
  s1.(evm) = s2.(evm) [\ Sv.add x Sv.empty].
Proof.
  rewrite /write_var /set_var; case: of_val => //= v' [<-] /=.
  by move=> z Hz;rewrite Fv.setP_neq //;apply /eqP; SvD.fsetdec.
Qed.

Lemma vrvP (x:rval) v s1 s2 : 
  write_rval x v s1 = ok s2 -> 
  s1.(evm) = s2.(evm) [\ vrv x].
Proof. 
  case x => /= [ _ [<-] | ? /vrvP_var| y e| y e] //.
  + by t_rbindP => -[<-].
  apply: on_arr_varP => n t; case:y => -[] ty yn yi /= -> Hy.
  apply: rbindP => we;apply: rbindP => ve He Hve.
  apply: rbindP => v0 Hv0;apply rbindP => t' Ht'.
  rewrite /set_var /=.
  case: CEDecStype.pos_dec => //= H [<-] /=.
  by move=> z Hz;rewrite Fv.setP_neq //;apply /eqP; SvD.fsetdec.
Qed.

Lemma vrvsP xs vs s1 s2 :
  write_rvals s1 xs vs = ok s2 -> 
  s1.(evm) = s2.(evm) [\ vrvs xs].
Proof.
  elim: xs vs s1 s2 => [|x xs Hrec] [|v vs] s1 s2 //=.
  + by move=> [<-].
  apply: rbindP => s /vrvP Hrv /Hrec Hrvs.
  rewrite vrvs_cons;apply: (@vmap_eq_exceptT (evm s)).
  + by apply: vmap_eq_exceptI Hrv;SvD.fsetdec.
  by apply: vmap_eq_exceptI Hrvs;SvD.fsetdec.
Qed.

Lemma writeP c s1 s2 : 
   sem s1 c s2 -> s1.(evm) = s2.(evm) [\ write_c c].
Proof.
  apply (@sem_Ind (fun s1 c s2 => s1.(evm) = s2.(evm) [\ write_c c])
                  (fun s1 i s2 => s1.(evm) = s2.(evm) [\ write_i i])
                  (fun s1 i s2 => s1.(evm) = s2.(evm) [\ write_I i])
                  (fun x ws s1 c s2 => 
                     s1.(evm) = s2.(evm) [\ (Sv.union (Sv.singleton x) (write_c c))])
                  (fun _ _ _ _ _ => True)) => {c s1 s2} //.
  + move=> s1 s2 s3 i c _ Hi _ Hc z;rewrite write_c_cons => Hnin.
    by rewrite Hi ?Hc //;SvD.fsetdec.
  + move=> s1 s2 x tag e; case: sem_pexpr => //= v Hw z.
    by rewrite write_i_assgn;apply (vrvP Hw).
  + move=> s1 s2 o xs es; case: (Let _ := sem_pexprs _ _ in _) => //= vs Hw z.
    by rewrite write_i_opn;apply (vrvsP Hw).
  + by move=> s1 s2 e c1 c2 _ _ Hrec z;rewrite write_i_if => Hnin;apply Hrec;SvD.fsetdec.
  + by move=> s1 s2 e c1 c2 _ _ Hrec z;rewrite write_i_if => Hnin;apply Hrec;SvD.fsetdec.
  + by move=> s1 s2 s3 e c _ _ Hc _ Hw z Hnin; rewrite Hc ?Hw.
  + by move=> s1 s2 i d lo hi c vlo vhi _ _ _ Hrec z;rewrite write_i_for;apply Hrec.
  + move=> s1 s1' s2 s3 i w ws c Hw _ Hc _ Hf z Hnin.
    by rewrite (vrvP_var Hw) ?Hc ?Hf //;SvD.fsetdec.
  + move=> s1 m2 s2 ii xs fn args vargs vs _ _ _ Hw z.
    by rewrite write_i_call;apply (vrvsP Hw).
Qed.

Lemma write_IP i s1 s2 : 
   sem_I s1 i s2 -> s1.(evm) = s2.(evm) [\ write_I i].
Proof.
  move=> /sem_seq1 /writeP.
  have := write_c_cons i [::].
  move=> Heq H x Hx;apply H; SvD.fsetdec. 
Qed.

Lemma write_iP i s1 s2 : 
   sem_i s1 i s2 -> s1.(evm) = s2.(evm) [\ write_i i].
Proof. by move=> /EmkI -/(_ 1%positive) /write_IP. Qed.

Definition eq_on (s : Sv.t) (vm1 vm2 : vmap) :=
  forall x, Sv.In x s -> vm1.[x]%vmap = vm2.[x]%vmap.

Notation "vm1 '=[' s ']' vm2" := (eq_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  =[ s ]  '/'  vm2 ']'").

Lemma eq_onT s vm1 vm2 vm3:
  vm1 =[s] vm2 -> vm2 =[s] vm3 -> vm1 =[s] vm3.
Proof. by move=> H1 H2 x Hin;rewrite H1 ?H2. Qed.

Lemma eq_onI s1 s2 vm1 vm2 : Sv.Subset s1 s2 -> vm1 =[s2] vm2 -> vm1 =[s1] vm2.
Proof. move=> Hs Heq x Hin;apply Heq;SvD.fsetdec. Qed.

Lemma eq_onS vm1 s vm2 : vm1 =[s] vm2 -> vm2 =[s] vm1.
Proof. by move=> Heq x Hin;rewrite Heq. Qed.

Global Instance equiv_eq_on s: Equivalence (eq_on s).
Proof.
  constructor=> //.
  move=> ??;apply: eq_onS.
  move=> ???;apply: eq_onT.
Qed.

Global Instance eq_on_impl : Proper (Basics.flip Sv.Subset ==> eq ==> eq ==> Basics.impl) eq_on.
Proof. by move=> s1 s2 H vm1 ? <- vm2 ? <-;apply: eq_onI. Qed.

Global Instance eq_on_m : Proper (Sv.Equal ==> eq ==> eq ==> iff) eq_on.
Proof. by move=> s1 s2 Heq vm1 ? <- vm2 ? <-;split;apply: eq_onI;rewrite Heq. Qed.

Lemma disjoint_eq_on s r s1 s2 v: 
  disjoint s (vrv r) ->
  write_rval r v s1 = ok s2 ->
  s1.(evm) =[s] s2.(evm).
Proof.
  move=> Hd /vrvP H z Hnin;apply H.
  move:Hd;rewrite /disjoint /is_true Sv.is_empty_spec;SvD.fsetdec.
Qed.

Lemma disjoint_eq_ons s r s1 s2 v: 
  disjoint s (vrvs r) ->
  write_rvals s1 r v = ok s2 ->
  s1.(evm) =[s] s2.(evm).
Proof.
  move=> Hd /vrvsP H z Hnin;apply H.
  move:Hd;rewrite /disjoint /is_true Sv.is_empty_spec;SvD.fsetdec.
Qed.

Lemma get_var_eq_on s vm' vm v: Sv.In v s -> vm =[s]  vm' -> get_var vm v = get_var vm' v.
Proof. by move=> Hin Hvm;rewrite /get_var Hvm. Qed.

Lemma on_arr_var_eq_on s' X s A x (f:forall n, Array.array n word -> exec A) :
   evm s =[X] evm s' -> Sv.In x X ->
   on_arr_var s x f = on_arr_var s' x f.
Proof. 
  by move=> Heq Hin;rewrite /on_arr_var;rewrite (get_var_eq_on Hin Heq).
Qed.

Lemma read_e_eq_on s vm' vm m e:
  vm =[read_e_rec s e] vm'->
  sem_pexpr (Estate m vm) e = sem_pexpr (Estate m vm') e.
Proof.
  elim:e s => //= [e He | v | v e He |v e He | e He | o e1 He1 e2 He2] s.
  + by move=> /He ->. 
  + move=> /get_var_eq_on -> //;SvD.fsetdec. 
  + move=> Heq;rewrite (He _ Heq)=> {He}.
    rewrite (@on_arr_var_eq_on 
      {| emem := m; evm := vm' |} _ {| emem := m; evm := vm |} _ _ _ Heq) ?read_eE //.
    by SvD.fsetdec.
  + by move=> /He ->.
  + by move=> /He ->.
  move=> Heq;rewrite (He1 _ Heq) (He2 s) //.
  by move=> z Hin;apply Heq;rewrite read_eE;SvD.fsetdec.
Qed.

Lemma read_es_eq_on es s m vm vm':
  vm =[read_es_rec s es] vm'->
  sem_pexprs (Estate m vm) es = sem_pexprs (Estate m vm') es.
Proof.
  rewrite /sem_pexprs;elim: es s => //= e es Hes s Heq.
  rewrite (@read_e_eq_on s vm'). 
  + by case:sem_pexpr => //= v;rewrite (Hes (read_e_rec s e)).
  by move=> z Hin;apply Heq;rewrite read_esE;SvD.fsetdec.
Qed.

Lemma set_var_eq_on s x v vm1 vm2 vm1': 
  set_var vm1 x v = ok vm2 ->
  vm1 =[s]  vm1' ->
  exists vm2' : vmap,
     vm2 =[Sv.union (Sv.add x Sv.empty) s]  vm2' /\
     set_var vm1' x v = ok vm2'.
Proof.
  rewrite /set_var;case: of_val => //= v' [<-] Heq.
  exists (vm1'.[x <- ok v'])%vmap;split=>// z Hin.
  case: (x =P z) => [<- | /eqP Hxz];first by rewrite !Fv.setP_eq.
  rewrite !Fv.setP_neq ?Heq //;move/eqP:Hxz; SvD.fsetdec.
Qed.

Lemma write_var_eq_on X x v s1 s2 vm1:
  write_var x v s1 = ok s2 ->
  evm s1 =[X] vm1 ->
  exists vm2 : vmap,
    evm s2 =[Sv.add x X]  vm2 /\
    write_var x v {| emem := emem s1; evm := vm1 |} = ok {| emem := emem s2; evm := vm2 |}.
Proof.
  rewrite /write_var /=;apply: rbindP => vm2 Hset [<-].          
  move=> /(set_var_eq_on Hset) [vm2' [Hvm2 ->]];exists vm2';split=>//=.
  by apply: eq_onI Hvm2;SvD.fsetdec. 
Qed.

Lemma write_rval_eq_on X x v s1 s2 vm1 : 
  Sv.Subset (read_rv x) X ->
  write_rval x v s1 = ok s2 ->
  evm s1 =[X] vm1 ->
  exists vm2 : vmap,
   evm s2 =[Sv.union (vrv x) X] vm2 /\
   write_rval x v {|emem:= emem s1; evm := vm1|} = ok {|emem:= emem s2; evm := vm2|}.
Proof.
  case:x => [vi | x | x e | x e ] /=.
  + by move=> ? [<-] ?;exists vm1.
  + move=> _ Hw /(write_var_eq_on Hw) [vm2 [Hvm2 Hx]];exists vm2;split=>//.
    by apply: eq_onI Hvm2;SvD.fsetdec. 
  + rewrite read_eE => Hsub Hsem Hvm;move:Hsem. 
    rewrite -(get_var_eq_on _ Hvm);last by SvD.fsetdec.
    rewrite (get_var_eq_on _ Hvm);last by SvD.fsetdec.
    case: s1 Hvm => sm1 svm1 Hvm1.
    rewrite (@read_e_eq_on Sv.empty vm1 svm1);first last.
    + by apply: eq_onI Hvm1;rewrite read_eE;SvD.fsetdec.
    apply: rbindP => vx ->;apply: rbindP => ve ->;apply: rbindP => w /= ->.
    by apply: rbindP => m /= -> [<-] /=;exists vm1.
  rewrite read_eE=> Hsub Hsem Hvm;move:Hsem.
  rewrite (@on_arr_var_eq_on {| emem := emem s1; evm := vm1 |} X s1 _ _ _ Hvm);
    last by SvD.fsetdec.
  case: s1 Hvm => sm1 svm1 Hvm1.
  rewrite (@read_e_eq_on (Sv.add x Sv.empty) vm1) /=;first last.
  + by apply: eq_onI Hvm1;rewrite read_eE.
  apply: on_arr_varP => n t Htx;rewrite /on_arr_var => -> /=.  
  apply: rbindP => i -> /=;apply: rbindP => ? -> /=;apply: rbindP => ? -> /=.
  apply: rbindP => ? /set_var_eq_on -/(_ _ _ Hvm1) [vm2' [Heq' ->]] [] <-.
  by exists vm2'. 
Qed.

Lemma write_rvals_eq_on X xs vs s1 s2 vm1 :
  Sv.Subset (read_rvs xs) X ->
  write_rvals s1 xs vs = ok s2 ->
  evm s1 =[X] vm1 ->
  exists vm2 : vmap,
    evm s2 =[Sv.union (vrvs xs) X] vm2 /\
    write_rvals {|emem:= emem s1; evm := vm1|} xs vs = ok {|emem:= emem s2; evm := vm2|}.
Proof.
  elim: xs vs X s1 s2 vm1 => [ | x xs Hrec] [ | v vs] //= X s1 s2 vm1.
  + by move=> _ [<-] ?;exists vm1.
  rewrite read_rvs_cons => Hsub.
  apply: rbindP => s1' Hw Hws /(write_rval_eq_on _ Hw) [ |vm1' [Hvm1' ->]].
  + by SvD.fsetdec.
  have [ |vm2 [Hvm2 /= ->]]:= Hrec _ _ _ _ _ _ Hws Hvm1';first by SvD.fsetdec.
  by exists vm2;split => //;rewrite vrvs_cons;apply: eq_onI Hvm2;SvD.fsetdec.
Qed.

End SEM.

Notation "vm1 = vm2 [\ s ]" := (vmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Notation "vm1 '=[' s ']' vm2" := (eq_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  =[ s ]  '/'  vm2 ']'").

Definition val_uincl (t:stype) : sem_t t -> sem_t t -> Prop := 
  match t as t0 return sem_t t0 -> sem_t t0 -> Prop with
  | sbool => fun b1 b2 => b1 = b2
  | sint  => fun i1 i2 => i1 = i2
  | sword => fun w1 w2 => w1 = w2
  | sarr n => fun (t1 t2:Array.array n word) => 
      (forall i v, Array.get t1 i = ok v -> Array.get t2 i = ok v)
  end.

Definition eval_uincl (t:stype) (v1 v2: exec (sem_t t)) := 
  match v1, v2 with 
  | Ok  v1 , Ok   v2 => val_uincl v1 v2
  | Error _, Ok    _ => True
  | Error _, Error _ => True
  | _      , _       => False
  end.

Definition vm_uincl (vm1 vm2:vmap) :=
  forall x, eval_uincl (vm1.[x])%vmap (vm2.[x])%vmap.

Lemma val_uincl_refl t v: @val_uincl t v v.
Proof. by elim: t v => //=. Qed.

Hint Resolve val_uincl_refl.    

Lemma eval_uincl_refl t v: @eval_uincl t v v.
Proof. case: v=> //=. Qed.

Hint Resolve eval_uincl_refl.    

Lemma vm_uincl_refl vm: @vm_uincl vm vm.
Proof. by done. Qed.

Hint Resolve vm_uincl_refl.    

Definition value_uincl (v1 v2:value) := 
  match v1, v2 with
  | Vbool b1, Vbool b2 => b1 = b2
  | Vint n1, Vint n2   => n1 = n2
  | Varr n1 t1, Varr n2 t2 => 
    n1 = n2 /\ (forall i v, Array.get t1 i = ok v -> Array.get t2 i = ok v)
  | Vword w1, Vword w2 => w1 = w2
  | _, _ => False
  end.

Lemma value_uincl_refl v: @value_uincl v v.
Proof. by case v. Qed.

Hint Resolve value_uincl_refl.    

Lemma is_full_array_uincl v1 v2: 
  is_full_array v1 -> value_uincl v1 v2 -> v1 = v2.
Proof.
  case: v1 v2 => [?|?|??|?] [?|?|??|?] //= H; try by move=> ->.
  move=> [] <- Hget;f_equal;apply Array.eq_ext => w.
  rewrite /Array.get;case:ifPn => //.
  move=> H1;move: (H1) => /andP [] /Zle_is_le_bool H2 /Zlt_is_lt_bool H3.
  have [w' Heq]:= H _ (conj H2 H3); have := Hget _ _ Heq.
  by move: Heq;rewrite /Array.get H1 => -> ->.
Qed.

Lemma is_full_array_uincls vs1 vs2: 
  List.Forall is_full_array vs1 -> 
  List.Forall2 value_uincl vs1 vs2 -> vs1 = vs2.
Proof.
  move=> H1 H2;elim: H2 H1 => //= v1 v2 {vs1 vs2} vs1 vs2 Hv Hvs Hrec H;sinversion H.
  f_equal;auto using is_full_array_uincl.
Qed.

Lemma of_val_uincl v v' t z:
  value_uincl v v' ->
  of_val t v = ok z ->
  exists z', of_val t v' = ok z' /\ val_uincl z z'.
Proof.
  case: v v'=> [b | n | n a | w] [b' | n' | n' a' | w'] //=.
  + by move=> <- ?;exists z.
  + by move=> <- ?;exists z.
  + move=> [<- H];case: t z => //= p a1.
    by case: CEDecStype.pos_dec => //= Heq;subst=> /= -[] <-;exists a'.
  by move=> <- ?;exists z. 
Qed.

Lemma to_val_uincl t (z z' : sem_t t) :
  val_uincl z z' <-> value_uincl (to_val z) (to_val z').
Proof. by case: t z z'=> //=;tauto. Qed.

Lemma value_uincl_int ve ve' z :
  value_uincl ve ve' -> to_int ve = ok z -> ve = z /\ ve' = z.
Proof. by case:ve ve' => //= z0 [] //= z1 -> [] ->. Qed.

Lemma value_uincl_word ve ve' w :
  value_uincl ve ve' -> to_word ve = ok w -> ve = w /\ ve' = w.
Proof. by case:ve ve' => //= z0 [] //= z1 -> [] ->. Qed.

Lemma value_uincl_bool ve ve' b :
  value_uincl ve ve' -> to_bool ve = ok b -> ve = b /\ ve' = b.
Proof. by case:ve ve' => //= z0 [] //= z1 -> [] ->. Qed.

Lemma get_var_uincl x vm1 vm2 v1: 
  vm_uincl vm1 vm2 -> 
  get_var vm1 x = ok v1 ->
  exists v2, get_var vm2 x = ok v2 /\ value_uincl v1 v2.
Proof. 
  move=> /(_ x);rewrite /get_var=> H H1.
  apply: rbindP H1=> z1 Heq1 [] <-.
  move: H;rewrite Heq1=> {Heq1}.
  case: (vm2.[x])%vmap => //= z2 Hz2;exists (to_val z2);split=> //.
  by case: (vtype x) z1 z2 Hz2.
Qed.

Lemma  get_vars_uincl (xs:seq var_i) vm1 vm2 vs1:
  vm_uincl vm1 vm2 -> 
  mapM (fun x => get_var vm1 (v_var x)) xs = ok vs1 ->
  exists vs2, 
    mapM (fun x => get_var vm2 (v_var x)) xs = ok vs2 /\ List.Forall2 value_uincl vs1 vs2.
Proof.
  move=> Hvm;elim: xs vs1 => [ | x xs Hrec] /= ?.
  + move=> [<-];exists [::];split=>//; constructor.
  apply: rbindP => v1 /(get_var_uincl Hvm) [v2 [-> ?]].
  apply: rbindP => vs1 /Hrec [vs2 [-> ?]] [] <- /=;exists (v2::vs2);split=>//.
  by constructor.
Qed.

Lemma vuincl_sem_op2_b o ve1 ve1' ve2 ve2' v1 : 
  value_uincl ve1 ve1' -> value_uincl ve2 ve2' -> sem_op2_b o ve1 ve2 = ok v1 ->
  exists v2 : value, sem_op2_b o ve1' ve2' = ok v2 /\ value_uincl v1 v2.
Proof.
  rewrite /sem_op2_b /= /mk_sem_sop2 => Hvu1 Hvu2.
  apply: rbindP => z1 /(value_uincl_bool Hvu1) [] _ ->.
  apply: rbindP => z2 /(value_uincl_bool Hvu2) [] _ -> [] <- /=.
  by exists (o z1 z2). 
Qed.

Lemma vuincl_sem_op2_i o ve1 ve1' ve2 ve2' v1 : 
  value_uincl ve1 ve1' -> value_uincl ve2 ve2' -> sem_op2_i o ve1 ve2 = ok v1 ->
  exists v2 : value, sem_op2_i o ve1' ve2' = ok v2 /\ value_uincl v1 v2.
Proof.
  rewrite /sem_op2_i /= /mk_sem_sop2 => Hvu1 Hvu2.
  apply: rbindP => z1 /(value_uincl_int Hvu1) [] _ ->.
  apply: rbindP => z2 /(value_uincl_int Hvu2) [] _ -> [] <- /=.
  by exists (o z1 z2). 
Qed.

Lemma vuincl_sem_op2_ib o ve1 ve1' ve2 ve2' v1 : 
  value_uincl ve1 ve1' -> value_uincl ve2 ve2' -> sem_op2_ib o ve1 ve2 = ok v1 ->
  exists v2 : value, sem_op2_ib o ve1' ve2' = ok v2 /\ value_uincl v1 v2.
Proof.
  rewrite /sem_op2_ib /= /mk_sem_sop2 => Hvu1 Hvu2.
  apply: rbindP => z1 /(value_uincl_int Hvu1) [] _ ->.
  apply: rbindP => z2 /(value_uincl_int Hvu2) [] _ -> [] <- /=.
  by exists (o z1 z2). 
Qed.

Lemma vuincl_sem_sop2 o ve1 ve1' ve2 ve2' v1 :
  value_uincl ve1 ve1' -> value_uincl ve2 ve2' ->
  sem_sop2 o ve1 ve2 = ok v1 ->
  exists v2 : value, sem_sop2 o ve1' ve2' = ok v2 /\ value_uincl v1 v2.
Proof.
  case:o => /=;eauto using vuincl_sem_op2_i, vuincl_sem_op2_b, vuincl_sem_op2_ib.
Qed.

Lemma sem_pexpr_uincl s1 vm2 e v1:
  vm_uincl s1.(evm) vm2 ->
  sem_pexpr s1 e = ok v1 ->
  exists v2, sem_pexpr (Estate s1.(emem) vm2) e = ok v2 /\ value_uincl v1 v2.
Proof.
  move=> Hu; elim: e v1=>//=[z | b | e He | x | x p Hp | x p Hp | e Hp | o e1 He1 e2 He2] v1.
  + by move=> [] <-;exists z.
  + by move=> [] <-;exists b.
  + apply: rbindP => z;apply: rbindP => ve /He [] ve' [] -> Hvu Hto [] <-.
    by case: (value_uincl_int Hvu Hto) => ??;subst; exists (Vword (I64.repr z)).
  + by apply get_var_uincl.
  + apply on_arr_varP => n t Htx;rewrite /on_arr_var=> /(get_var_uincl Hu) [v2 [->]]. 
    case: v2 => //= ? t' [] ? Htt';subst.
    apply: rbindP => z;apply: rbindP => vp /Hp [] vp' [] -> /= Hvu Hto.
    case: (value_uincl_int Hvu Hto) => ??;subst.
    apply: rbindP=> w /Htt' Hget [] <- /=.
    by exists w;rewrite Hget.
  + apply: rbindP => w;apply: rbindP => wp;apply: rbindP => vp /Hp [] vp' [] -> Hvu Hto.
    by case: (value_uincl_word Hvu Hto) => ??;subst => /= -> [] <-;exists w.
  + apply: rbindP => b;apply: rbindP => vx /Hp [] vp' [] -> Hvu Hto [] <-.
    by case: (value_uincl_bool Hvu Hto) => ??;subst => /=;exists (~~b).
  apply: rbindP => ve1 /He1 [] ve1' [] -> Hvu1.
  apply: rbindP => ve2 /He2 [] ve2' [] -> Hvu2 {He1 He2}.
  by apply vuincl_sem_sop2.
Qed.

Lemma sem_pexprs_uincl s1 vm2 es vs1:
  vm_uincl s1.(evm) vm2 ->
  sem_pexprs s1 es  = ok vs1 ->
  exists vs2, sem_pexprs (Estate s1.(emem) vm2) es = ok vs2 /\ 
              List.Forall2 value_uincl vs1 vs2.
Proof.
  rewrite /sem_pexprs; move=> Hvm;elim: es vs1 => [ | e es Hrec] vs1 /=.
  + by move=> [] <-;eauto.
  apply: rbindP => ve /(sem_pexpr_uincl Hvm) [] ve' [] -> ?.
  by apply: rbindP => ys /Hrec [vs2 []] /= -> ? [] <- /=;eauto.
Qed.

Lemma vuincl_oww o vs vs' v : 
  List.Forall2 value_uincl vs vs' ->
  (oww o) vs = ok v ->
  exists v' : values,
     (oww o) vs' = ok v' /\ List.Forall2 value_uincl v v'.
Proof.
  move=> [] //= v1 v1' ?? Hv [] //=;last by move=> ??????;apply: rbindP.
  apply: rbindP => z /(value_uincl_word Hv) [] _ -> [] <- /=.
  by eexists;split;eauto;constructor.
Qed.

Lemma vuincl_owww o vs vs' v : 
  List.Forall2 value_uincl vs vs' ->
  (owww o) vs = ok v ->
  exists v' : values,
     (owww o) vs' = ok v' /\ List.Forall2 value_uincl v v'.
Proof.
  move=> [] //= v1 v1' ?? Hv [] //=; first by apply: rbindP.
  move=> ???? Hv' [] //=.
  + apply: rbindP => z /(value_uincl_word Hv) [] _ ->.
    apply: rbindP => z' /(value_uincl_word Hv') [] _ -> [] <- /=.
    by eexists;split;eauto;constructor.
  by move=> ??????;t_rbindP.
Qed.

Lemma vuincl_sem_opn o vs vs' v : 
  List.Forall2 value_uincl vs vs' -> sem_sopn o vs = ok v ->
  exists v', sem_sopn o vs' = ok v' /\ List.Forall2  value_uincl v v'.
Proof.
  rewrite /sem_sopn;case: o;eauto using vuincl_oww, vuincl_owww.
  + move=> [] //= v1 v1' ?? Hv1 [] //=; first by apply: rbindP.
    move=> v2 v2' ?? Hv2 [];first by t_rbindP.
    move=> v3 v3' ?? Hv3 [].
    + apply: rbindP=> ? /(value_uincl_bool Hv1) [] _ ->.
      apply: rbindP=> ? /(value_uincl_word Hv2) [] _ ->.
      apply: rbindP=> ? /(value_uincl_word Hv3) [] _ -> [] <- /=.
      by eexists;split;eauto;do 2 constructor.
    by move=> ??????;t_rbindP.   
  + move=> [] //= v1 v1' ?? Hv [] //=; first by apply: rbindP.
    move=> ???? Hv' [] //=.
    + apply: rbindP => z /(value_uincl_word Hv) [] _ ->.
      apply: rbindP => z' /(value_uincl_word Hv') [] _ -> [] <- /=.
      by eexists;split;eauto;constructor => //;constructor.
    by move=> ??????;t_rbindP.
  + move=> [] //= v1 v1' ?? Hv1 [] //=; first by apply: rbindP.
    move=> v2 v2' ?? Hv2 [];first by t_rbindP.
    move=> v3 v3' ?? Hv3 [].
    + apply: rbindP=> ? /(value_uincl_word Hv1) [] _ ->.
      apply: rbindP=> ? /(value_uincl_word Hv2) [] _ ->.
      apply: rbindP=> ? /(value_uincl_bool Hv3) [] _ -> [] <- /=.
      by eexists;split;eauto;do 2 constructor.
    by move=> ??????;t_rbindP. 
  + move=> [] //= v1 v1' ?? Hv1 [] //=; first by apply: rbindP.
    move=> v2 v2' ?? Hv2 [];first by t_rbindP.
    move=> v3 v3' ?? Hv3 [].
    + apply: rbindP=> ? /(value_uincl_word Hv1) [] _ ->.
      apply: rbindP=> ? /(value_uincl_word Hv2) [] _ ->.
      apply: rbindP=> ? /(value_uincl_bool Hv3) [] _ -> [] <- /=.
      by eexists;split;eauto;do 2 constructor.
    by move=> ??????;t_rbindP. 
Qed.

Lemma set_vm_uincl vm vm' x z z' : 
  vm_uincl vm vm' ->
  val_uincl z z' -> 
  vm_uincl (vm.[x <- ok z])%vmap (vm'.[x <- ok z'])%vmap.
Proof.
  move=> Hvm Hz y; case( x =P y) => [<- | /eqP Hneq];by rewrite ?Fv.setP_eq ?Fv.setP_neq.
Qed.

Lemma set_var_uincl vm1 vm1' vm2 x v v' :
  vm_uincl vm1 vm1' ->
  value_uincl v v' ->
  set_var vm1 x v = ok vm2 ->
  exists vm2', set_var vm1' x v' = ok vm2' /\ vm_uincl vm2 vm2'.
Proof.
  move=> Hvm Hv;rewrite /set_var.
  apply: rbindP=> z /(of_val_uincl Hv) [z' [-> ?]] [] <- /=.
  by exists (vm1'.[x <- ok z'])%vmap;split=>//; apply set_vm_uincl.
Qed.

Lemma Array_set_uincl n (a1 a2 a1':Array.array n word) i v: 
  @val_uincl (sarr n) a1 a2 ->
  Array.set a1 i v = ok a1' ->
  exists a2', Array.set a2 i v = ok a2' /\ @val_uincl (sarr n) a1' a2'.
Proof.
  rewrite /Array.set;case:ifP=> //= ? H [] <-.
  exists (FArray.set a2 i (ok v));split => // i' v';move: (H i' v').
  rewrite /Array.get;case:ifP=> //= Hbound.
  by rewrite !FArray.setP;case:ifP.
Qed.

Lemma write_var_uincl s1 s2 vm1 v1 v2 x :
  vm_uincl (evm s1) vm1 ->
  value_uincl v1 v2 ->
  write_var x v1 s1 = ok s2 ->
  exists vm2 : vmap,
    write_var x v2 {| emem := emem s1; evm := vm1 |} =
    ok {| emem := emem s2; evm := vm2 |} /\ vm_uincl (evm s2) vm2.
Proof.
  move=> Hvm1 Hv;rewrite /write_var;apply: rbindP=> vm2 /=.
  by move=> /(set_var_uincl Hvm1 Hv) [vm2' [-> ?]] [] <- /=;exists vm2'.
Qed.

Lemma write_vars_uincl s1 s2 vm1 vs1 vs2 xs :
  vm_uincl (evm s1) vm1 ->
  List.Forall2 value_uincl vs1 vs2 ->
  write_vars xs vs1 s1 = ok s2 ->
  exists vm2 : vmap,
    write_vars xs vs2 {| emem := emem s1; evm := vm1 |} =
    ok {| emem := emem s2; evm := vm2 |} /\ vm_uincl (evm s2) vm2.
Proof.
  elim: xs s1 vm1 vs1 vs2 => /= [ | x xs Hrec] s1 vm1 vs1 vs2 Hvm [] //=.
  + by move=> [] <-;eauto.
  move=> {vs1 vs2} v1 v2 vs1 vs2 Hv Hvs;apply: rbindP => s1'.
  by move=> /(write_var_uincl Hvm Hv) [] vm2 [] -> Hvm2 /(Hrec _ _ _ _ Hvm2 Hvs).
Qed.

Lemma write_uincl s1 s2 vm1 r v1 v2:
  vm_uincl s1.(evm) vm1 ->
  value_uincl v1 v2 ->
  write_rval r v1 s1 = ok s2 ->
  exists vm2, 
    write_rval r v2 (Estate (emem s1) vm1) = ok (Estate (emem s2) vm2) /\ 
    vm_uincl s2.(evm) vm2.
Proof.
  move=> Hvm1 Hv;case:r => [xi | x | x p | x p] /=.
  + by move=> [] <-;exists vm1.
  + by apply write_var_uincl.
  + apply: rbindP => vx1; apply: rbindP => vx /(get_var_uincl Hvm1) [vx2 [-> Hvx]].
    move=> /(value_uincl_word Hvx) [] _ -> {Hvx vx} /=.
    apply: rbindP => ve; apply: rbindP => ve' /(sem_pexpr_uincl Hvm1) [ve''] [] -> Hve.    
    move=> /(value_uincl_word Hve) [] _ -> /=.
    apply: rbindP => w /(value_uincl_word Hv) [] _ -> /=.
    by apply: rbindP => m' -> [] <- /=;eauto.
  apply: on_arr_varP => n a Htx /(get_var_uincl Hvm1).
  rewrite /on_arr_var => -[] vx [] /= -> /=;case: vx => //= n0 t0 [] ? Ht0;subst.
  apply: rbindP => i;apply: rbindP=> vp /(sem_pexpr_uincl Hvm1) [vp' [-> Hvp]] /=.
  move=>  /(value_uincl_int Hvp) [] _ -> /=.
  apply: rbindP => v /(value_uincl_word Hv) [] _ -> /=.
  apply: rbindP => t=> /(Array_set_uincl Ht0).
  move=> [] t' [-> Ht];apply: rbindP => vm'.
  have Hut: value_uincl (Varr t) (Varr t') by split.
  by move=> /(set_var_uincl Hvm1 Hut) /= [vm2' [-> ?]] [] <- /=;eauto.
Qed.

Lemma writes_uincl s1 s2 vm1 r v1 v2:
  vm_uincl s1.(evm) vm1 ->
  List.Forall2 value_uincl v1 v2 ->
  write_rvals s1 r v1 = ok s2 ->
  exists vm2, 
    write_rvals (Estate (emem s1) vm1) r v2 = ok (Estate (emem s2) vm2) /\ 
    vm_uincl s2.(evm) vm2.
Proof.
  elim: r v1 v2 s1 s2 vm1 => [ | r rs Hrec] ?? s1 s2 vm1 Hvm1 /= [] //=. 
  + by move=> [] <-;eauto.
  move=> v1 v2 vs1 vs2 Hv Hforall.
  apply: rbindP => z /(write_uincl Hvm1 Hv) [] vm2 [-> Hvm2].
  by move=> /(Hrec _ _ _ _ _ Hvm2 Hforall).
Qed.

Lemma write_vars_rvals xs vs s1: 
  write_vars xs vs s1 = write_rvals s1 [seq Rvar i | i <- xs] vs.
Proof.
  rewrite /write_vars /write_rvals.
  elim: xs vs s1 => [ | x xs Hrec] [ | v vs] //= s1.
  by case: write_var => //=.
Qed.

Lemma sem_pexprs_get_var s xs : 
  sem_pexprs s [seq Pvar i | i <- xs] = mapM (fun x : var_i => get_var (evm s) x) xs.
Proof.
  rewrite /sem_pexprs;elim: xs=> //= x xs Hrec.
  by case: get_var => //= v;rewrite Hrec.
Qed.

Lemma get_fundef_cons fnd p fn: 
  get_fundef (fnd :: p) fn = if fn == fnd.1 then Some fnd.2 else get_fundef p fn.
Proof.
  rewrite /get_fundef;case:ifP => /=; by case: ifPn => //= ?;rewrite ltnS => ->.
Qed.

Lemma get_fundef_in p f fd : get_fundef p f = Some fd -> f \in [seq x.1 | x <- p].
Proof.
  by elim: p => //= [f' fd'] Hrec;rewrite get_fundef_cons in_cons;case: ifP.
Qed.


Section UNDEFINCL.

Variable (p:prog).

Let Pc s1 c s2 := 
  forall vm1 , 
    vm_uincl (evm s1) vm1 ->
    exists vm2, 
      sem p {|emem := emem s1; evm := vm1|} c {|emem := emem s2; evm := vm2|} /\ 
      vm_uincl (evm s2) vm2.

Let Pi_r s1 i s2 :=
  forall vm1, 
    vm_uincl (evm s1) vm1 ->
    exists vm2, 
      sem_i p {|emem := emem s1; evm := vm1|} i {|emem := emem s2; evm := vm2|} /\ 
      vm_uincl (evm s2) vm2.

Let Pi s1 i s2 :=
  forall vm1, 
    vm_uincl (evm s1) vm1 ->
    exists vm2, 
      sem_I p {|emem := emem s1; evm := vm1|} i {|emem := emem s2; evm := vm2|} /\ 
      vm_uincl (evm s2) vm2.

Let Pfor (i:var_i) zs s1 c s2 := 
  forall vm1, 
    vm_uincl (evm s1) vm1 ->
    exists vm2, 
      sem_for p i zs {|emem := emem s1; evm := vm1|} c {|emem := emem s2; evm := vm2|} /\ 
      vm_uincl (evm s2) vm2.

Let Pfun m1 fd vargs m2 vres := 
  forall vargs', 
    List.Forall2 value_uincl vargs vargs' ->
    sem_call p m1 fd vargs' m2 vres.

Local Lemma Hnil s : @Pc s [::] s.
Proof. by move=> vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

Local Lemma Hcons s1 s2 s3 i c :
  sem_I p s1 i s2 -> Pi s1 i s2 -> 
  sem p s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.
Proof.
  move=> _ Hi _ Hc vm1 /Hi [vm2 []] Hsi /Hc [vm3 []] Hsc ?.
  by exists vm3;split=>//;econstructor;eauto.
Qed.

Local Lemma HmkI ii i s1 s2 : sem_i p s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.
Proof. by move=> _ Hi vm1 /Hi [vm2 []] Hsi ?;exists vm2. Qed.

Local Lemma Hasgn s1 s2 x tag e :
  Let v := sem_pexpr s1 e in write_rval x v s1 = ok s2 ->
  Pi_r s1 (Cassgn x tag e) s2.
Proof.
  move=> Hs2 vm1 Hvm1;apply:rbindP Hs2 => z /(sem_pexpr_uincl Hvm1) [] z' [] Hz' Hz.
  move=> /(write_uincl Hvm1 Hz) [vm2 []] Hw ?;exists vm2;split=> //.
  by constructor;rewrite Hz' /= Hw.
Qed.

Local Lemma Hopn s1 s2 o xs es:
  Let x := Let x := sem_pexprs s1 es in sem_sopn o x in 
  write_rvals s1 xs x = ok s2 -> Pi_r s1 (Copn xs o es) s2.
Proof.
  move=> H vm1 Hvm1; apply: rbindP H => rs;apply: rbindP => vs.
  move=> /(sem_pexprs_uincl Hvm1) [] vs' [] H1 H2.
  move=> /(vuincl_sem_opn H2) [] rs' [] H3 H4.
  move=> /(writes_uincl Hvm1 H4) [] vm2 [] ??.
  exists vm2;split => //;constructor.
  by rewrite H1 /= H3.
Qed.

Local Lemma Hif_true s1 s2 e c1 c2 :
  Let x := sem_pexpr s1 e in to_bool x = ok true ->
  sem p s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
Proof.
  move=> H _ Hc vm1 Hvm1;apply: rbindP H => v.
  move=> /(sem_pexpr_uincl Hvm1) [] v' [] H1 H2.
  move=> /(value_uincl_bool H2) [] ??;subst. 
  have [vm2 [??]]:= Hc _ Hvm1;exists vm2;split=>//.
  by apply Eif_true;rewrite // H1.
Qed.

Local Lemma Hif_false s1 s2 e c1 c2 :
  Let x := sem_pexpr s1 e in to_bool x = ok false ->
  sem p s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
Proof.
  move=> H _ Hc vm1 Hvm1;apply: rbindP H => v.
  move=> /(sem_pexpr_uincl Hvm1) [] v' [] H1 H2.
  move=> /(value_uincl_bool H2) [] ??;subst. 
  have [vm2 [??]]:= Hc _ Hvm1;exists vm2;split=>//.
  by apply Eif_false;rewrite // H1.
Qed.

Local Lemma Hwhile_true s1 s2 s3 e c :
  Let x := sem_pexpr s1 e in to_bool x = ok true ->
  sem p s1 c s2 -> Pc s1 c s2 ->
  sem_i p s2 (Cwhile e c) s3 -> Pi_r s2 (Cwhile e c) s3 -> Pi_r s1 (Cwhile e c) s3.
Proof.
  move=> H _ Hc _ Hw vm1 Hvm1;apply: rbindP H => v.
  move=> /(sem_pexpr_uincl Hvm1) [] v' [] H1 H2.
  move=> /(value_uincl_bool H2) [] ??;subst. 
  have [vm2 [H3 /Hw [vm3] [??]]]:= Hc _ Hvm1;exists vm3;split => //.
  by eapply Ewhile_true;eauto;rewrite H1.
Qed.
  
Local Lemma Hwhile_false s e c :
  Let x := sem_pexpr s e in to_bool x = ok false ->
  Pi_r s (Cwhile e c) s.
Proof.
  move=> H vm1 Hvm1;apply: rbindP H=> v.
  move=> /(sem_pexpr_uincl Hvm1) [] v' [] H1 H2.
  move=> /(value_uincl_bool H2) [] ??;subst. 
  by exists vm1;split=> //;apply Ewhile_false;rewrite H1.
Qed.
 
Local Lemma Hfor s1 s2 (i : var_i) d lo hi c (vlo vhi : Z) :
  Let x := sem_pexpr s1 lo in to_int x = ok vlo ->
  Let x := sem_pexpr s1 hi in to_int x = ok vhi ->
  sem_for p i (wrange d vlo vhi) s1 c s2 ->
  Pfor i (wrange d vlo vhi) s1 c s2 ->
  Pi_r s1 (Cfor i (d, lo, hi) c) s2.
Proof.
  move=> H H' _ Hfor vm1 Hvm1;apply: rbindP H => ?.
  move=> /(sem_pexpr_uincl Hvm1) [] ? [] H1 H2.
  move=> /(value_uincl_int H2) [] ??;subst. 
  apply: rbindP H' => ?.
  move=> /(sem_pexpr_uincl Hvm1) [] ? [] H3 H4.
  move=> /(value_uincl_int H4) [] ??;subst. 
  have [vm2 []??]:= Hfor _ Hvm1; exists vm2;split=>//.
  by econstructor;eauto;rewrite ?H1 ?H3.
Qed.

Local Lemma Hfor_nil s i c : Pfor i [::] s c s.
Proof. by move=> vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

Local Lemma Hfor_cons s1 s1' s2 s3 (i : var_i) (w : Z) (ws : seq Z) c :
  write_var i w s1 = ok s1' ->
  sem p s1' c s2 -> Pc s1' c s2 ->
  sem_for p i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.
Proof.
  move=> Hi _ Hc _ Hf vm1 Hvm1.
  have [vm1' [Hi' /Hc]] := write_var_uincl Hvm1 (value_uincl_refl _) Hi.
  move=> [vm2 [Hsc /Hf]] [vm3 [Hsf Hvm3]];exists vm3;split => //.
  by econstructor;eauto.
Qed.

Local Lemma Hcall s1 m2 s2 ii xs fn args vargs vs : 
  sem_pexprs s1 args = ok vargs ->
  sem_call p (emem s1) fn vargs m2 vs ->
  Pfun (emem s1) fn vargs m2 vs ->
  write_rvals {| emem := m2; evm := evm s1 |} xs vs = ok s2 ->
  Pi_r s1 (Ccall ii xs fn args) s2.
Proof.
  move=> Hargs Hcall Hfd Hxs vm1 Hvm1.
  have [vargs' [Hsa /Hfd Hc]]:= sem_pexprs_uincl Hvm1 Hargs.
  have Hvm1' : vm_uincl (evm {| emem := m2; evm := evm s1 |}) vm1 by done.
  have [vm2' [??]]:= writes_uincl Hvm1' (List_Forall2_refl vs value_uincl_refl) Hxs.
  exists vm2';split=>//;econstructor;eauto.
Qed.

Local Lemma Hproc m1 m2 fn fd vargs s1 vm2 vres: 
  get_fundef p fn = Some fd ->
  write_vars (f_params fd) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
  sem p s1 (f_body fd) {| emem := m2; evm := vm2 |} -> 
  Pc s1 (f_body fd) {| emem := m2; evm := vm2 |} ->
  mapM (fun x : var_i => get_var vm2 x) (f_res fd) = ok vres ->
  List.Forall is_full_array vres -> 
  Pfun m1 fn vargs m2 vres.
Proof.
  move=> Hget Hargs Hsem Hrec Hmap Hfull vargs' Uargs.   
  have [vm1 [Hargs' Hvm1]]:= write_vars_uincl (vm_uincl_refl _) Uargs Hargs.
  have [vm2' /= [] Hsem' Uvm2]:= Hrec _ Hvm1.
  have [vs2 [Hvs2]] := get_vars_uincl Uvm2 Hmap.
  move=> /(is_full_array_uincls Hfull) ?;subst.
  econstructor;eauto.
Qed.

Lemma sem_call_uincl vargs m1 f m2 vres vargs':
  List.Forall2 value_uincl vargs vargs' ->
  sem_call p m1 f vargs m2 vres ->
  sem_call p m1 f vargs' m2 vres.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_i_uincl s1 i s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem_i p s1 i s2 ->
  exists vm2, 
    sem_i p {|emem := emem s1; evm := vm1|} i {|emem := emem s2; evm := vm2|} /\ 
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_i_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_I_uincl s1 i s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem_I p s1 i s2 ->
  exists vm2, 
    sem_I p {|emem := emem s1; evm := vm1|} i {|emem := emem s2; evm := vm2|} /\ 
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_I_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_uincl s1 c s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem p s1 c s2 ->
  exists vm2, 
    sem p {|emem := emem s1; evm := vm1|} c {|emem := emem s2; evm := vm2|} /\ 
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

End UNDEFINCL.

