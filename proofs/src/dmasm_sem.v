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

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import JMeq ZArith.

Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Interpretation of types
 * -------------------------------------------------------------------- *)

Module FArray.

  Definition array (T:Type) := word -> T.

  Definition cnst {T} (t:T) : array T := fun i => t.

  Definition get {T} (a:array T) (i:word) := a i.

  Definition set {T} (a:array T) (i:word) (v:T) :=
    fun j => if i == j  then v else a j.
  
  Lemma setP {T} (a:array T) (w1 w2:word) (t:T):
    get (set a w1 t) w2 = if w1 == w2 then t else get a w2.
  Proof. done. Qed.

  Lemma setP_eq {T} (a:array T) (w:word) (t:T):
    get (set a w t) w = t.
  Proof. by rewrite setP eq_refl. Qed.

  Lemma setP_neq {T} (a:array T) (w1 w2:word) (t:T): 
    w1 != w2 -> get (set a w1 t) w2 = get a w2.
  Proof. by rewrite setP=> /negPf ->. Qed.

End FArray.

Module Array.

  Definition array (s:positive) T := FArray.array (exec T).

  Definition empty {T:Type} (s:positive) : array s T := FArray.cnst (Error ErrAddrUndef).

  Definition make {T:Type} (s:positive) (t:T) : array s T :=  FArray.cnst (ok t). 

  Definition get {T} {s} (a:array s T) (w:word) : result error T := 
    if ((0 <=? w) && (w <? Zpos s))%Z then FArray.get a w
    else Error ErrOob.

  Definition set {T} s (a:array s T) (x:word) (v:T) : result error (array s T):=
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

Notation vmap     := (Fv.t sem_t).
Notation vmap0    := (@Fv.empty sem_t (fun x => dflt_val x.(vtype))).

Definition get_var (m:vmap) x := 
  @to_val (vtype x) (m.[x]%vmap).

Definition set_var (m:vmap) x v := 
  Let v := @of_val (vtype x) v in
  ok (m.[x<-v]%vmap).

Definition is_empty_array (t:stype) := 
  match t return sem_t t -> Prop with
  | sbool  => fun _ => True
  | sint   => fun _ => True
  | sarr n => fun v => v =  Array.empty n
  | sword  => fun _ => True
  end.

Definition all_empty_arr (vm:vmap) := forall x, is_empty_array (vm.[x])%vmap.

Definition is_full_array v := 
  match v with
  | Varr n t => 
    forall (p:word), (0 <= p < Zpos n)%Z -> exists w, Array.get t p = ok w
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
  match vtype x as t return sem_t t -> exec A with
  | sarr n => f n
  | _ => fun _ => type_error 
  end  (s.(evm).[ x ]%vmap).

Notation "'Let' ( n , t ) ':=' s '.[' x ']' 'in' body" :=
  (@on_arr_var _ s x (fun n (t:Array.array n word) => body)) (at level 25, s at level 0).

Lemma on_arr_varP A (f : forall n : positive, Array.array n word -> exec A) v s x P:
  (forall n t, vtype x = sarr n -> f n t = ok v -> P) -> 
  on_arr_var s x f = ok v -> P.
Proof. by rewrite /on_arr_var;case: x => -[] //= ?? H /H H';apply H'. Qed.

Lemma on_arr_varP2 A (f : forall n : positive, Array.array n word -> exec A) v s x P:
  (forall n t, vtype x = sarr n -> 
               JMeq ((evm s).[x])%vmap t ->      
(*               @to_val (vtype x) ((evm s).[x])%vmap = @Varr n t -> *)
               f n t = ok v -> P) -> 
  on_arr_var s x f = ok v -> P.
Proof. by rewrite /on_arr_var;case: x => -[] //= ?? H /H H';apply H'. Qed.
 
Fixpoint sem_pexpr (s:estate) (e : pexpr) : exec value :=
  match e with
  | Pconst z => ok (Vint z)
  | Pbool b  => ok (Vbool b)
  | Pcast e  => 
    Let z := sem_pexpr s e >>= to_int in
    ok (Vword (I64.repr z))  
  | Pvar v => ok (get_var s.(evm) v)
  | Pget x e => 
      Let (n,t) := s.[x] in
      Let i := sem_pexpr s e >>= to_word in
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

Definition write_rval_aux (s0:estate) (l:rval) (v:value) (s:estate) : exec estate :=
  match l with 
  | Rnone _ => ok s
  | Rvar x => write_var x v s
  | Rmem x e =>  
    Let vx := to_word (get_var (evm s0) x) in
    Let ve := sem_pexpr s0 e >>= to_word in
    let p := wadd vx ve in (* should we add the size of value, i.e vx + sz * se *)
    Let w := to_word v in
    Let m :=  write_mem s.(emem) p w in
    ok {|emem := m;  evm := s.(evm) |}
  | Raset x i =>
    Let (n,t) := s0.[x] in
    Let i := sem_pexpr s0 i >>= to_word in
    Let v := to_word v in
    Let t := Array.set t i v in
    Let vm := set_var s.(evm) x (@to_val (sarr n) t) in 
    ok ({| emem := s.(emem); evm := vm |})
  end.
 
Definition write_rval l v s := write_rval_aux s l v s.

Definition write_rvals (s:estate) xs vs := 
   fold2 ErrType (write_rval_aux s) xs vs s.

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

| Ecall s1 m2 s2 ii xs f fd args vargs vs : 
    get_fundef P f = Some fd ->
    sem_pexprs s1 args = ok vargs ->
    sem_call s1.(emem) fd vargs m2 vs ->
    write_rvals {|emem:= m2; evm := s1.(evm) |} xs vs = ok s2 ->
    sem_i s1 (Ccall ii xs f args) s2

with sem_for : var -> seq Z -> estate -> cmd -> estate -> Prop :=
| EForDone s i c :
    sem_for i [::] s c s

| EForOne s1 s1' s2 s3 i w ws c :
    write_var i (Vint w) s1 = ok s1' ->
    sem s1' c s2 ->
    sem_for i ws s2 c s3 ->
    sem_for i (w :: ws) s1 c s3

with sem_call : mem -> fundef -> seq value -> mem -> seq value -> Prop := 
| EcallRun m1 m2 f vargs vres:
    (* semantics defined for all vm0 *)
    (forall vm0, all_empty_arr vm0 -> 
       exists s1 vm2, [/\ 
        write_vars f.(f_params) vargs (Estate m1 vm0) = ok s1, 
        sem s1 f.(f_body) (Estate m2 vm2) &
        map (fun (x:var_i) => get_var vm2 x) f.(f_res) = vres]) ->
    List.Forall is_full_array vres ->
    sem_call m1 f vargs m2 vres.

(* -------------------------------------------------------------------- *)

Section SEM_IND.
  Variables
    (Pc   : estate -> cmd -> estate -> Prop)
    (Pi_r : estate -> instr_r -> estate -> Prop)
    (Pi : estate -> instr -> estate -> Prop)
    (Pfor : var -> seq Z -> estate -> cmd -> estate -> Prop)
    (Pfun : mem -> fundef -> seq value -> mem -> seq value -> Prop).
 
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

  Hypothesis Hfor_nil : forall (s : estate) (i : var) (c : cmd), Pfor i [::] s c s.

  Hypothesis Hfor_cons : forall (s1 s1' s2 s3 : estate) (i : var_i) 
         (w : Z) (ws : seq Z) (c : cmd),
    write_var i w s1 = Ok error s1' ->
    sem s1' c s2 -> Pc s1' c s2 ->
    sem_for i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.

  Hypothesis Hcall : forall (s1 : estate) (m2 : mem) (s2 : estate) 
         (ii : inline_info) (xs : rvals) (fn : pos_eqType) 
         (fd : fundef) (args : pexprs) (vargs vs : seq value),
    get_fundef P fn = Some fd ->
    sem_pexprs s1 args = Ok error vargs ->
    sem_call (emem s1) fd vargs m2 vs -> Pfun (emem s1) fd vargs m2 vs ->
    write_rvals {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
    Pi_r s1 (Ccall ii xs fn args) s2.

  Hypothesis Hproc : forall (m1 m2 : mem) (fd : fundef) (vargs vres : seq value),
    (forall vm0 : vmap,
       all_empty_arr vm0 ->
       exists (s1 : estate) (vm2 : vmap),
         [/\ write_vars (f_params fd) vargs {| emem := m1; evm := vm0 |} =  Ok error s1, 
             sem s1 (f_body fd) {| emem := m2; evm := vm2 |},
             Pc s1 (f_body fd) {| emem := m2; evm := vm2 |}
          & map (fun (x:var_i) => get_var vm2 x) fd.(f_res) = vres]) ->
    List.Forall is_full_array vres -> Pfun m1 fd vargs m2 vres.

  Section CALL.

    Variable sem_Ind : forall s1 c s2, sem s1 c s2 -> Pc s1 c s2.

    Definition sem_call_Ind_aux m1 fd vargs m2 vres :
       sem_call m1 fd vargs m2 vres -> Pfun m1 fd vargs m2 vres.
    Proof.
      move=> [] {m1 m2 vargs vres fd} m1 m2 fd vargs vres H Hfull.
      apply Hproc=> //.
      move=> vm0 /H [] s1 [] vm2 [] Hargs Hsem Hres.
      exists s1, vm2;split => //.
      by apply sem_Ind.
    Defined.

  End CALL.
      
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
    | @Ecall s1 m2 s2 ii xs f13 fd args vargs vs e1 e2 s0 e3 =>
      @Hcall s1 m2 s2 ii xs f13 fd args vargs vs e1 e2 s0
        (@sem_call_Ind (emem s1) fd vargs m2 vs s0) e3
    end

  with sem_I_Ind (e : estate) (i : instr) (e0 : estate) (s : sem_I e i e0) {struct s} :
    Pi e i e0 :=
    match s in (sem_I e1 i0 e2) return (Pi e1 i0 e2) with
    | @EmkI ii i0 s1 s2 s0 => @HmkI ii i0 s1 s2 s0 (@sem_i_Ind s1 i0 s2 s0)
    end

  with sem_for_Ind (v : var) (l : seq Z) (e : estate) (l0 : cmd) (e0 : estate)
         (s : sem_for v l e l0 e0) {struct s} : Pfor v l e l0 e0 :=
    match s in (sem_for v0 l1 e1 l2 e2) return (Pfor v0 l1 e1 l2 e2) with
    | EForDone s0 i c => Hfor_nil s0 i c
    | @EForOne s1 s1' s2 s3 i w ws c e1 s0 s4 =>
      @Hfor_cons s1 s1' s2 s3 i w ws c e1 s0 (@sem_Ind s1' c s2 s0)
         s4 (@sem_for_Ind i ws s2 c s3 s4)
    end

  with sem_call_Ind (m : mem) (f13 : fundef) (l : seq value) (m0 : mem) 
         (l0 : seq value) (s : sem_call m f13 l m0 l0) {struct s} : Pfun m f13 l m0 l0 :=
    @sem_call_Ind_aux (@sem_Ind) m f13 l m0 l0 s.

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

Lemma vrvP_var (x:var_i) v s1 s2 :
  write_var x v s1 = ok s2 -> 
  s1.(evm) = s2.(evm) [\ Sv.add x Sv.empty].
Proof.
  rewrite /write_var /set_var; case: of_val => //= v' [<-] /=.
  by move=> z Hz;rewrite Fv.setP_neq //;apply /eqP; SvD.fsetdec.
Qed.

Lemma vrv_auxP s0 (x:rval) v s1 s2 : 
  write_rval_aux s0 x v s1 = ok s2 -> 
  s1.(evm) = s2.(evm) [\ vrv x].
Proof.
  case x => /= [ _ [<-] | ? /vrvP_var| y e| y e] //.
  + case: (to_word (get_var _ _)) => //= vy.             
    case: (Let _ := sem_pexpr _ _ in _) => //= ve.
    case: to_word => //= w.
    by case: write_mem => //= m [<-].
  apply: on_arr_varP2 => n t; case:y => -[] ty yn yi /= -> Hy.
  apply: rbindP => we;apply: rbindP => ve He Hve.
  apply: rbindP => v0 Hv0;apply rbindP => t' Ht'.
  rewrite /set_var /=.
  case: CEDecStype.pos_dec => //= H [<-] /=.
  by move=> z Hz;rewrite Fv.setP_neq //;apply /eqP; SvD.fsetdec.
Qed.
   
Lemma vrvP (x:rval) v s1 s2 : 
  write_rval x v s1 = ok s2 -> 
  s1.(evm) = s2.(evm) [\ vrv x].
Proof. by apply vrv_auxP. Qed.

Lemma vrvsP xs vs s1 s2 :
  write_rvals s1 xs vs = ok s2 -> 
  s1.(evm) = s2.(evm) [\ vrvs xs].
Proof.
  rewrite /write_rvals.
  move: {1}s1 => s0.
  elim: xs vs s1 s2 => [|x xs Hrec] [|v vs] s1 s2 //=.
  + by move=> [<-].
  case Hrv: write_rval_aux => [s | ] //= /Hrec Hrvs z.
  by rewrite vrvs_cons => Hnin;rewrite (vrv_auxP Hrv) ?Hrvs //;SvD.fsetdec.
Qed.

Lemma write_i_opn xs o es : write_i (Copn xs o es) = vrvs xs. 
Proof. done. Qed.

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
  + move=> s1 m2 s2 ii xs f fd args vargs vs _ _ _ _ Hw z.
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

Lemma read_e_eq_on s vm' vm m e:
  vm =[read_e_rec s e] vm'->
  sem_pexpr (Estate m vm) e = sem_pexpr (Estate m vm') e.
Proof.
  elim:e s => //= [e He | v | v e He |v e He | e He | o e1 He1 e2 He2] s.
  + by move=> /He ->. 
  + move=> /get_var_eq_on -> //;SvD.fsetdec. 
  + move=> Heq;rewrite (He _ Heq)=> {He}.
    case:v Heq => [[[]]] //= n vn _;rewrite /on_arr_var /= => H.
    by rewrite H // read_eE;SvD.fsetdec.
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
  exists (vm1'.[x <- v'])%vmap;split=>// z Hin.
  case: (x =P z) => [<- | /eqP Hxz];first by rewrite !Fv.setP_eq.
  rewrite !Fv.setP_neq ?Heq //;move/eqP:Hxz; SvD.fsetdec.
Qed.

Lemma write_rval_eq_on s x v m1 m2 vm1 vm2 vm1': 
  Sv.Subset (read_rv x) s ->
  write_rval x v {| emem := m1; evm := vm1 |} = ok {|emem := m2; evm := vm2 |} ->
  vm1 =[s] vm1' ->
  exists vm2' : vmap,
   vm2 =[Sv.union (vrv x) s]  vm2' /\
   write_rval x v {|emem:= m1; evm := vm1'|} = ok {|emem:= m2; evm := vm2'|}.
Proof.
  case:x => [vi | x | x e | x e ] /=.
  + by move=> _ [] <- <- Hvm;exists vm1';split=>//;apply: eq_onI Hvm.
  + move=> _;rewrite /write_var /=.
    case Heq: set_var => [vm1'' | ]//= []<- <- Hvm.
    by have [vm2' [Heq' ->]]:= set_var_eq_on Heq Hvm;exists vm2'.
  + rewrite read_eE => Hsub Hsem Hvm;move:Hsem. 
    rewrite -(get_var_eq_on _ Hvm);last by SvD.fsetdec.
    case: (to_word (get_var _ _)) => //= vx.
    rewrite (@read_e_eq_on (Sv.add x Sv.empty) vm1');first last.
    + by apply: eq_onI Hvm;rewrite read_eE;SvD.fsetdec.
    case:(Let _ := sem_pexpr _ _ in _) => //= ve.
    by case: to_word => //= w;case: write_mem => //= m [<- <-];exists vm1'.
  move=> Hsub Hsem Hvm;move:Hsem.      
  case:x Hsub => [[[]]] //= n vn _;rewrite /on_arr_var /=.
  rewrite read_eE;set x := {| vtype := sarr n; vname := vn |} => H.
  rewrite (@read_e_eq_on (Sv.add x Sv.empty) vm1');first last.
  + by apply: eq_onI Hvm;rewrite read_eE.
  case:(Let _ := sem_pexpr _ _ in _) => //= i.
  case: to_word => //= v0; rewrite (Hvm x);last by SvD.fsetdec.
  case: Array.set => //= a.
  case Heq: set_var => [vm1'' | ]//= []<- <-.
  by have [vm2' [Heq' ->]]:= set_var_eq_on Heq Hvm;exists vm2'.
Qed.

(*
Lemma write_rval_eq_on t s (x:rval t) v m1 m2 vm1 vm2 vm1': 
  write_rval {| emem := m1; evm := vm1 |} x v = ok {|emem := m2; evm := vm2 |} ->
  vm1 =[ read_rv_rec x (Sv.diff s (vrv x))] vm1' ->
  exists vm2' : vmap,
   vm2 =[s]  vm2' /\
   write_rval {|emem:= m1; evm := vm1'|} x v = ok {|emem:= m2; evm := vm2'|}.
Proof.
  rewrite /write_rval=> Hw Heq;move: Hw.
  have -> := @read_rv_eq_on _ x (Sv.diff s (vrv x)) m1 vm1 vm1' Heq.
  case Heq': rval2vval=> [rv|] //= Hw.
  apply: (write_vval_eq_on Heq' Hw);apply: eq_onI Heq;rewrite read_rvE;SvD.fsetdec.
Qed.
*)
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

Definition vm_uincl (vm1 vm2:vmap) :=
  forall x, val_uincl (vm1.[x])%vmap (vm2.[x])%vmap.

Lemma val_uincl_refl t v: @val_uincl t v v.
Proof. by elim: t v => //=. Qed.

Hint Resolve val_uincl_refl.    

Definition value_uincl (v1 v2:value) := 
  match v1, v2 with
  | Vbool b1, Vbool b2 => b1 = b2
  | Vint n1, Vint n2   => n1 = n2
  | Varr n1 t1, Varr n2 t2 => 
    n1 = n2 /\ (forall i v, Array.get t1 i = ok v -> Array.get t2 i = ok v)
  | Vword w1, Vword w2 => w1 = w2
  | _, _ => False
  end.

Lemma value_uincl_int ve ve' z :
  value_uincl ve ve' -> to_int ve = ok z -> ve = z /\ ve' = z.
Proof. by case:ve ve' => //= z0 [] //= z1 -> [] ->. Qed.

Lemma value_uincl_word ve ve' w :
  value_uincl ve ve' -> to_word ve = ok w -> ve = w /\ ve' = w.
Proof. by case:ve ve' => //= z0 [] //= z1 -> [] ->. Qed.

Lemma value_uincl_bool ve ve' b :
  value_uincl ve ve' -> to_bool ve = ok b -> ve = b /\ ve' = b.
Proof. by case:ve ve' => //= z0 [] //= z1 -> [] ->. Qed.

Lemma get_var_uincl vm1 vm2 x : 
  vm_uincl vm1 vm2 -> value_uincl (get_var vm1 x) (get_var vm2 x).
Proof. by move=> /(_ x);case x => -[]. Qed.

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

Lemma sem_pexpr_uincl s1 vm2 e v1:
  vm_uincl s1.(evm) vm2 ->
  sem_pexpr s1 e = ok v1 ->
  exists v2, sem_pexpr (Estate s1.(emem) vm2) e = ok v2 /\ value_uincl v1 v2.
Proof.
  move=> Hu; elim: e v1=>//= [z | b | e He | x | x p Hp | x p Hp | e Hp | o e1 He1 e2 He2] v1.
  + by move=> [] <-;exists z.
  + by move=> [] <-;exists b.
  + apply: rbindP => z;apply: rbindP => ve /He [] ve' [] -> Hvu Hto [] <-.
    by case: (value_uincl_int Hvu Hto) => ??;subst; exists (Vword (I64.repr z)).
  + by move=> [] <-;exists (get_var vm2 x);split=> //;apply get_var_uincl.
  + have := Hu x;case x => -[xt xn] xi /= H H';move: H' H.
    apply: on_arr_varP2 => /= n t -> /= H; have {H} <- := JMeq_eq H.
    apply: rbindP => z;apply: rbindP => vp /Hp [] vp' [] Hvp' Hvu Hto.
    case: (value_uincl_word Hvu Hto) => ??;subst.
    apply: rbindP=> w Hget [] <- /=.
    by rewrite /on_arr_var Hvp' /= => /(_ _ _ Hget) -> /=;exists w.
  + apply: rbindP => w;apply: rbindP => wp;apply: rbindP => vp /Hp [] vp' [] -> Hvu Hto.
    by case: (value_uincl_word Hvu Hto) => ??;subst => /= -> [] <-;exists w.
  + apply: rbindP => b;apply: rbindP => vx /Hp [] vp' [] -> Hvu Hto [] <-.
    by case: (value_uincl_bool Hvu Hto) => ??;subst => /=;exists (~~b).
  apply: rbindP => ve1 /He1 [] ve1' [] -> Hvu1.
  apply: rbindP => ve2 /He2 [] ve2' [] -> Hvu2 {He1 He2}.
  case:o => /=;eauto using vuincl_sem_op2_i, vuincl_sem_op2_b, vuincl_sem_op2_ib.
Qed.

(*
Lemma write_uincl s1 s2 vm1 t (r:rval t) v1 v2:
  vm_uincl s1.(evm) vm1 ->
  val_uincl v1 v2 ->
  write_rval s1 r v1 = ok s2 ->
  exists vm2, write_rval (Estate (emem s1) vm1) r v2 = ok (Estate (emem s2) vm2) /\ 
              vm_uincl s2.(evm) vm2.
Proof.
(*
  rewrite /write_rval;case Heq: rval2vval => [rv|] //=.
  move=> Hvm Hv;move=> /(rval2vval_uincl Hvm) in Heq;rewrite Heq /= => {Heq}.
  elim: rv s1 s2 vm1 v1 v2 Hvm Hv => [x | p | ?? x1 Hx1 x2 Hx2] s1 s2 vm1 v1 v2 /= Hvm.
  + move=> Hv [] <- /=;exists (vm1.[x <- v2])%vmap;split=>// z.
    case:(x =P z)=> [<-|/eqP ?];first by rewrite !Fv.setP_eq.
    by rewrite !Fv.setP_neq.
  + by move=> <-;case Heq: write_mem => [m|]//= [] <- /=;exists vm1.
  move=> []Hv1 Hv2;case Heq2:write_vval => [s1'|] //= Heq1.
  have [vm2 [Heq2' Hvm2]]:= Hx2 _ _ _ _ _ Hvm Hv2 Heq2. 
  have [vm3 [Heq1' Hvm3]] := Hx1 _ _ _ _ _ Hvm2 Hv1 Heq1. 
  by exists vm3;split=> //;rewrite Heq2'.
Qed.
*)
Admitted.

Section UNDEFINCL.
(*
Let Pi (i:instr) := 
  forall s1 vm1 s2, 
    vm_uincl (evm s1) vm1 ->
    sem_i s1 i s2 ->
    exists vm2, 
       sem_i {|emem := emem s1; evm := vm1|} i {|emem := emem s2; evm := vm2|} /\ 
       vm_uincl (evm s2) vm2.

Let Pc (c:cmd) := 
  forall s1 vm1 s2, 
    vm_uincl (evm s1) vm1 ->
    sem s1 c s2 ->
    exists vm2, 
       sem {|emem := emem s1; evm := vm1|} c {|emem := emem s2; evm := vm2|} /\ 
       vm_uincl (evm s2) vm2.

Let Pf ta tr (fd:fundef ta tr) := 
  forall m1 va va' m2 vr,
    val_uincl va va' ->
    sem_call m1 fd va m2 vr ->
    exists vr', sem_call m1 fd va' m2 vr' /\ val_uincl vr vr'.

Let Hskip : Pc [::].
Proof. 
  by move=> s1 vm1 s2 Hu H;sinversion H;exists vm1;split=>//;constructor.
Qed.

Let Hseq  : forall i c,  Pi i -> Pc c -> Pc (i::c).
Proof.
  move=> i c Hi Hc s1 vm1 s3 Hu H;sinversion H.
  move=> /Hi in H3;case (H3 _ Hu) => {H3} vm2 [Hi'] /Hc /(_ H5) [vm3] [Hc' Hvm3].
  by exists vm3;split=>//;econstructor;eauto.
Qed.

Let Hbcmd : forall t (x:rval t) e,  Pi (Cassgn x e).
Proof.
  move=> t x e s1 vm1 s2 Hu H;sinversion H.
  sinversion H3;sinversion H4;case Heq1:sem_pexpr H5 => [v1|] //=.
  case: (sem_expr_uincl Hu Heq1)=> v1' [He1 Hincl] /= Hw.  
  have [vm2 [Hw2 Hu2]]:= write_uincl Hu Hincl Hw.
  by exists vm2;split=>//;constructor;rewrite He1.
Qed.

Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
Proof.
  move=> e c1 c2 Hc1 Hc2 s1 vm1 s2 Hu H;sinversion H.
  case: (sem_expr_uincl Hu H5)=> cond' [He' /= H];subst.
  case: cond' He' {H5} H6 => He' Hs. 
  + have [vm2 [Hs' Hu2]]:= (Hc1 _ _ _ Hu Hs).
    exists vm2;split=> //;econstructor;eauto.
  have [vm2 [Hs' Hu2]]:= (Hc2 _ _ _ Hu Hs).
  exists vm2;split=> //;econstructor;eauto.
Qed.

Let Hfor  : forall i rn c, Pc c -> Pi (Cfor i rn c).
Proof.
  move=> i [[dir hi] low] c Hc s1 vm1 s2 Hu H;sinversion H.
  case: (sem_expr_uincl Hu H7)=> vlow' [Hlow' /= H] {H7};subst.
  case: (sem_expr_uincl Hu H8)=> vhi' [Hhi' /= H] {H8};subst.
  have : exists vm2,  
     sem_for i [seq n2w i | i <- wrange dir vlow' vhi']
     {| emem := emem s1; evm := vm1 |} c {| emem := emem s2; evm := vm2 |} /\
     vm_uincl (evm s2) vm2.
  + move=> {Hlow' Hhi'}.
    elim: wrange s1 vm1 Hu H9 => /= [|w ws Hrec] s1 vm1 Hu H;sinversion H.
    + by exists vm1;split=>//;constructor.
    have [vm2 /= [Hw Hu2]] := write_uincl Hu (@val_uincl_refl sword (n2w w)) H2.
    have [vm2' /= [H1 /Hrec [//|vm3 [??]]]]:= Hc _ _ _ Hu2 H4.
    by exists vm3;split=>//;econstructor;eauto.
  move=> [vm2 [Hfor Hu2]];exists vm2;split=>//.
  by econstructor;eauto.
Qed.

Let Hwhile  : forall e c, Pc c -> Pi (Cwhile e c).
Proof.
  move=> e c Hc s1 vm1 s2 Hu H;sinversion H.
  have : exists vm2, 
     sem_while {| emem := emem s1; evm := vm1 |} e c 
               {| emem := emem s2; evm := vm2 |} /\
     vm_uincl (evm s2) vm2.
  elim: H4 vm1 Hu Hc => {e c s1 s2}
    [s e c He| s1 s2 s3 e c He Hs _ Hrec] vm1 Hu Hc.
  + exists vm1;split=>//;constructor.
    by case: (sem_expr_uincl Hu He) => ? [-> <-].
    case: (sem_expr_uincl Hu He) => /= ? [] ??;subst.
    case: (Hc _ _ _ Hu Hs) => vm2 [Hc' Hu2].
    case: (Hrec _ Hu2 Hc) => vm3 [Hw Hu3].
    by exists vm3;split=>//;econstructor;eauto.
  by move=> [vm2 [Hw Hu2]];exists vm2;split=>//;constructor.
Qed.

Let Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
Proof.
  move=> ta tr x fd a Hf s1 vm1 s2 Hu H;sinversion H.
  sinversion H6;sinversion H5;sinversion H2;sinversion H0.
  case He : sem_pexpr @rarg H7 H8 => [va|]//= _.
  case: (sem_expr_uincl Hu He) => /= va' [] H1 H2 Hs.
  have [vr' [Hs' Hu']]:= Hf _ _ _ _ _ H2 Hs.
  have /(_ _ Hu) [vm2 [Hw2 Hu2]]:= write_uincl _ Hu' H9.
  by exists vm2;split=>//;econstructor;eauto;rewrite H1.
Qed.

Lemma empty_dflt t: is_empty_array (dflt_val t).
Proof. elim: t => //=. Qed.

Lemma empty_vmap0 : all_empty_arr vmap0.
Proof. by move=> x;rewrite Fv.get0; apply empty_dflt. Qed.

Lemma is_full_array_uincl t (v v':st2ty t): 
  is_full_array v -> val_uincl v v' -> v = v'.
Proof.
  elim: t v v' => // [t1 Ht1 t2 Ht2 | s] /=.
  + by move=> [v1 v2] [v1' v2'] /= [] ?? [] /Ht1 <- // /Ht2 <-.
  move=> v v' Hf Hu; apply Array.eq_ext=> w;have := Hu w; have := Hf w.
  rewrite /Array.get;case:ifP => // /andP [] /Z.leb_le ?  /Z.ltb_lt ?.
  by move=> [] // x Hx Hv; rewrite Hx -(Hv _ Hx). 
Qed.

Let Hfunc : forall ta tr (x:rval ta) c (re:pexpr tr), Pc c -> Pf (FunDef x c re).
Proof.
  move=> ta tr x c re Hc m1 va va' m2 vr Hu Hs;sinversion Hs.
  sinversion H.
  have [s2 /= [vm [Hw Hsc Hsr]]]:= H5 _ empty_vmap0.
  have Hu0 : vm_uincl vmap0 vmap0 by move=> z.
  have /(_ _ Hu0) [vm1/= [Hw1 Hu1]]:= write_uincl _ Hu Hw.
  have [vm2 /= [Hsc' Hu2]] := Hc _ _ _ Hu1 Hsc.
  have /(_ _ Hu2)[vr' [Hvr' Hu']]:= sem_expr_uincl _ Hsr.
  exists vr';split=>//;econstructor;last by have <- := is_full_array_uincl H7 Hu'.
  move=> {vm Hw Hsc Hsr vm1 Hw1 Hu1 vm2 Hsc' Hu2 Hvr'}.
  move=> vm0 Hall;case (H5 _ Hall) => s1 /= [vm [Hw Hsc Hsr]].
  have Huvm : vm_uincl vm0 vm0 by move=> z.
  have /(_ _ Huvm) [vm1/= [Hw1 Hu1]]:= write_uincl _ Hu Hw.
  have [vm2 /= [Hsc' Hu2]] := Hc _ _ _ Hu1 Hsc.
  have /(_ _ Hu2)[vr'' [Hvr' Hu'']]:= sem_expr_uincl _ Hsr.
  have ?:=  is_full_array_uincl H7 Hu';subst vr'.
  have ?:=  is_full_array_uincl H7 Hu'';subst vr''.
  by exists {| emem := emem s1; evm := vm1 |}, vm2;split.
Qed.

Lemma sem_i_uincl i : Pi i.
Proof.
  apply (@instr_rect2 Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall Hfunc).
Qed.

Lemma sem_uincl c : Pc c.
Proof.
  apply (@cmd_rect Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall Hfunc).
Qed.

Lemma sem_call_uincl ta tr (fd:fundef ta tr): Pf fd.
Proof.
  apply (@func_rect Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall Hfunc).
Qed.
*)
End UNDEFINCL.
*)