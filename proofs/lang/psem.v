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

(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import Psatz xseq.
Require Export expr low_memory sem.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

Local Open Scope leakage_scope.

(* ** Interpretation of types
 * -------------------------------------------------------------------- *)

Record pword s :=
  { pw_size: wsize;
    pw_word : word pw_size;
    pw_proof : (pw_size <= s)%CMP }.

Definition psem_t (t : stype) : Type :=
  match t with
  | sbool   => bool
  | sint    => Z
  | sarr n  => WArray.array n
  | sword s => pword s
  end.

(* ** Default values
 * -------------------------------------------------------------------- *)

Definition pword_of_word (s:wsize) (w:word s) : pword s :=
  {|pw_word := w; pw_proof := cmp_le_refl s|}.

Definition to_pword (s: wsize) (v: value) : exec (pword s) :=
   match v with
   | Vword s' w =>
    ok (
     if Sumbool.sumbool_of_bool (s' ≤ s)%CMP is left heq
     then {| pw_word := w ; pw_proof := heq |}
     else pword_of_word (zero_extend s w))
   | Vundef (sword _) => undef_error
   | _                => type_error
   end.

Definition to_parr (n : positive) v: exec (WArray.array n) :=
  match v with
  | Varr n' t => ok (WArray.inject n t)
  | Vundef (sarr n') => type_error
  | _                => type_error
  end.

Definition pof_val t : value -> exec (psem_t t) :=
  match t return value -> exec (psem_t t) with
  | sbool   => to_bool
  | sint    => to_int
  | sarr n  => to_parr n
  | sword s => to_pword s
  end.

Definition pto_val t : psem_t t -> value :=
  match t return psem_t t -> value with
  | sbool   => Vbool
  | sint    => Vint
  | sarr n  => fun a => Varr a
  | sword s => fun w => Vword (pw_word w)
  end.

Lemma to_pwordI s v w :
  to_pword s v = ok w →
  ∃ s' w',
    v = @Vword s' w' ∧
    w = if Sumbool.sumbool_of_bool (s' ≤ s)%CMP is left heq
        then {| pw_word := w' ; pw_proof := heq |}
        else pword_of_word (zero_extend s w').
Proof. by case: v => // [ | [] // ] s' w' /= [<-]; exists s', w'. Qed.

Lemma type_of_val_to_pword sz v w :
  type_of_val v = sword sz →
  to_pword sz v = ok w →
  ∃ w' : word sz, w = pword_of_word w' ∧ v = Vword w'.
Proof.
  case: v => //= [ s w' [?]| []//]; subst.
  by rewrite sumbool_of_boolET => - [<-]; exists w'.
Qed.

(* ** Variable map
 * -------------------------------------------------------------------- *)

Notation vmap     := (Fv.t (fun t => exec (psem_t t))).

Definition pundef_addr t :=
  match t return exec (psem_t t) with
  | sbool | sint | sword _ => undef_error
  | sarr n => ok (@WArray.empty n)
  end.

Definition vmap0 : vmap :=
  @Fv.empty (fun t => exec (psem_t t)) (fun x => pundef_addr x.(vtype)).

(* An access to a undefined value, leads to an error *)
Definition get_var (m:vmap) x :=
  on_vu (@pto_val (vtype x)) undef_error (m.[x]%vmap).

(* Assigning undefined value is allowed only for bool *)
Definition set_var (m:vmap) x v : exec vmap :=
  on_vu (fun v => m.[x<-ok v]%vmap)
        (if is_sbool x.(vtype) then ok m.[x<-pundef_addr x.(vtype)]%vmap
         else type_error)
        (pof_val (vtype x) v).

Lemma set_varP (m m':vmap) x v P :
   (forall t, pof_val (vtype x) v = ok t -> m.[x <- ok t]%vmap = m' -> P) ->
   ( is_sbool x.(vtype) -> pof_val (vtype x) v = undef_error ->
     m.[x<-pundef_addr x.(vtype)]%vmap = m' -> P) ->
   set_var m x v = ok m' -> P.
Proof.
  move=> H1 H2;apply on_vuP => //.
  by case:ifPn => // hb herr []; apply : H2.
Qed.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Record estate := Estate {
  emem : mem;
  evm  : vmap
}.

Definition on_arr_var A (s:estate) (x:var) (f:forall n, WArray.array n-> exec A) :=
  Let v := get_var s.(evm) x in
  match v with
  | Varr n t => f n t
  | _ => type_error
  end.

Notation "'Let' ( n , t ) ':=' s '.[' x ']' 'in' body" :=
  (@on_arr_var _ s x (fun n (t:WArray.array n) => body))
  (at level 25, s at level 0).

Section SEM_PEXPR.

Context (gd: glob_decls).

Fixpoint sem_pexpr (s:estate) (e : pexpr) : exec (value * leak_e)  :=
 match e with
  | Pconst z => ok (Vint z, LEmpty)
  | Pbool b  => ok (Vbool b, LEmpty)
  | Parr_init n => ok (Varr (WArray.empty n), LEmpty)
  | Pvar x => Let v := get_var s.(evm) x in 
              ok (v, LEmpty)
  | Pglobal g => Let v := get_global gd g in 
                 ok (v, LEmpty)
  | Pget ws x e =>
      Let (n, t) := s.[x] in
      Let vl := sem_pexpr s e in 
      Let i := to_int vl.1 in 
      Let w := WArray.get ws t i in
      ok ((Vword w), LSub [ :: vl.2 ; (LIdx i)])
  | Pload sz x e =>
    Let w1 := get_var s.(evm) x >>= to_pointer in
    Let vl2 := sem_pexpr s e in 
    Let w2 := to_pointer vl2.1 in
    let adr := (w1 + w2)%R in 
    Let w  := read_mem s.(emem) adr sz in
    ok (@to_val (sword sz) w, LSub [ :: vl2.2;  (LAdr adr)])
  | Papp1 o e1 =>
    Let vl := sem_pexpr s e1 in
    Let v := sem_sop1 o vl.1 in 
    ok (v, vl.2)
  | Papp2 o e1 e2 =>
    Let vl1 := sem_pexpr s e1 in
    Let vl2 := sem_pexpr s e2 in
    Let v := sem_sop2 o vl1.1 vl2.1 in
    ok (v, LSub [:: vl1.2; vl2.2])
  | PappN op es =>
    Let vs := mapM (sem_pexpr s) es in
    Let v := sem_opN op (unzip1 vs) in
    ok (v, LSub (unzip2 vs))
  | Pif t e e1 e2 =>
    Let vl := sem_pexpr s e in
    Let b := to_bool vl.1in
    Let vl1 := sem_pexpr s e1 in
    Let vl2 := sem_pexpr s e2 in
    Let v1 := truncate_val t vl1.1 in
    Let v2 := truncate_val t vl2.1 in
    ok (if b then v1 else v2, LSub [:: vl.2 ; vl1.2; vl2.2])
  end.

Definition sem_pexprs s es := mapM (sem_pexpr s) es. 

Definition write_var (x:var_i) (v:value) (s:estate) : exec estate :=
  Let vm := set_var s.(evm) x v in
  ok ({| emem := s.(emem); evm := vm |}).

Definition write_vars xs vs s :=
  fold2 ErrType write_var xs vs s.

Definition write_none (s:estate) ty v :=
  on_vu (fun v => s) (if is_sbool ty then ok s else type_error)
          (pof_val ty v).

Definition write_lval (l:lval) (v:value) (s:estate) : exec (estate * leak_e) :=
  match l with
  | Lnone _ ty => Let x := write_none s ty v in ok (x, LEmpty)
  | Lvar x => Let v' := write_var x v s in ok(v', LEmpty)
  | Lmem sz x e =>
    Let vx := get_var (evm s) x >>= to_pointer in
    Let vl := sem_pexpr s e in 
    Let ve := to_pointer vl.1 in
    let p := (vx + ve)%R in
    Let w := to_word sz v in
    Let m :=  write_mem s.(emem) p sz w in
    ok ({| emem := m;  evm := s.(evm) |}, LSub [:: vl.2; (LAdr p)])
  | Laset ws x i =>
    Let (n,t) := s.[x] in
    Let vl := sem_pexpr s i in 
    Let i := to_int vl.1 in
    Let v := to_word ws v in
    Let t := WArray.set t i v in
    Let vm := set_var s.(evm) x (@to_val (sarr n) t) in
    ok ({| emem := s.(emem); evm := vm |}, LSub [:: vl.2; (LIdx i)])
  end.

Fixpoint write_lvals (s:estate) xs vs : exec (estate * seq leak_e) :=
  match xs, vs with
  | [::], [::] => ok (s, [::])
  | x::xs, v::vs =>
    Let sl := write_lval x v s in
    Let sls := write_lvals sl.1 xs vs in
    ok (sls.1, sl.2::sls.2)
  | _, _ => Error ErrType                     
  end.


End SEM_PEXPR.

(* ** Instructions
 * -------------------------------------------------------------------- *)

Section SEM.

Variable P:prog.
Notation gd := (p_globs P).

Definition sem_range (s : estate) (r : range) :=
  let: (d,pe1,pe2) := r in
  Let vl1 := sem_pexpr gd s pe1 in 
  Let i1 := to_int vl1.1 in 
  Let vl2 := sem_pexpr gd s pe2 in 
  Let i2 := to_int vl2.1 in
  ok (wrange d i1 i2, LSub [:: vl1.2 ; vl2.2]).

Definition sem_sopn gd o m lvs args := 
  Let vas := sem_pexprs gd m args in
  Let vs := exec_sopn o (unzip1 vas) in 
  Let ml := write_lvals gd m lvs vs in
  ok (ml.1, LSub [:: LSub (unzip2 vas) ; LSub ml.2]).

Inductive sem : estate -> cmd -> leak_c -> estate -> Prop :=
| Eskip s :
    sem s [::] [::] s

| Eseq s1 s2 s3 i c li lc :
    sem_I s1 i li s2 -> sem s2 c lc s3 -> sem s1 (i::c) (li :: lc) s3

with sem_I : estate -> instr -> leak_i -> estate -> Prop :=
| EmkI ii i s1 s2 li:
    sem_i s1 i li s2 ->
    sem_I s1 (MkI ii i) li s2

with sem_i : estate -> instr_r -> leak_i -> estate -> Prop :=
| Eassgn s1 s2 (x:lval) tag ty e v v' l1 l2:
    sem_pexpr gd s1 e = ok (v,l1)  ->
    truncate_val ty v = ok v' →
    write_lval gd x v' s1 = ok (s2, l2) ->
    sem_i s1 (Cassgn x tag ty e) (Lassgn (LSub [:: l1 ; l2])) s2

| Eopn s1 s2 t o xs es lo:
    sem_sopn gd o s1 xs es = ok (s2, lo) ->
    sem_i s1 (Copn xs t o es) (Lopn lo) s2

| Eif_true s1 s2 e c1 c2 le lc:
    sem_pexpr gd s1 e = ok (Vbool true, le) ->
    sem s1 c1 lc s2 ->
    sem_i s1 (Cif e c1 c2) (Lcond le true lc) s2

| Eif_false s1 s2 e c1 c2 le lc:
    sem_pexpr gd s1 e = ok (Vbool false, le) ->
    sem s1 c2 lc s2 ->
    sem_i s1 (Cif e c1 c2) (Lcond le false lc) s2

| Ewhile_true s1 s2 s3 s4 a c e c' lc le lc' lw:
    sem s1 c lc s2 ->
    sem_pexpr gd s2 e = ok (Vbool true, le) ->
    sem s2 c' lc' s3 ->
    sem_i s3 (Cwhile a c e c') lw s4 ->
    sem_i s1 (Cwhile a c e c') (Lwhile_true lc le lc' lw) s4

| Ewhile_false s1 s2 a c e c' lc le:
    sem s1 c lc s2 ->
    sem_pexpr gd s2 e = ok (Vbool false, le) ->
    sem_i s1 (Cwhile a c e c') (Lwhile_false lc le) s2

| Efor s1 s2 (i:var_i) r c wr lr lf:
    sem_range s1 r = ok (wr, lr) ->
    sem_for i wr s1 c lf s2 ->
    sem_i s1 (Cfor i r c) (Lfor lr lf) s2

| Ecall s1 m2 s2 ii xs f args vargs vs lf l2:
    sem_pexprs gd s1 args = ok vargs ->
    sem_call s1.(emem) f (unzip1 vargs) lf m2 vs ->
    write_lvals gd {|emem:= m2; evm := s1.(evm) |} xs vs = ok (s2, l2) ->
    sem_i s1 (Ccall ii xs f args) (Lcall (LSub (unzip2 vargs)) lf (LSub l2)) s2

with sem_for : var_i -> seq Z -> estate -> cmd -> leak_for -> estate -> Prop :=
| EForDone s i c :
    sem_for i [::] s c [::] s

| EForOne s1 s1' s2 s3 i w ws c lc lw :
    write_var i (Vint w) s1 = ok s1' ->
    sem s1' c lc s2 ->
    sem_for i ws s2 c lw s3 ->
    sem_for i (w :: ws) s1 c (lc :: lw) s3

with sem_call : mem -> funname -> seq value -> leak_fun -> mem -> seq value -> Prop :=
| EcallRun m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc :
    get_fundef (p_funcs P) fn = Some f ->
    mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
    write_vars f.(f_params) vargs (Estate m1 vmap0) = ok s1 ->
    sem s1 f.(f_body) lc (Estate m2 vm2) ->
    mapM (fun (x:var_i) => get_var vm2 x) f.(f_res) = ok vres ->
    mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
    sem_call m1 fn vargs' (fn, lc) m2 vres'.

Lemma semE s c s' lc:
  sem s c lc s' ->
  match c with
  | [::] => s' = s /\ lc = [::]
  | i :: c' => exists si li lc', 
    [/\ sem_I s i li si, sem si c' lc' s' & lc = li :: lc']
  end.
Proof. case. move=> H1; split; auto.
move=> s1 s2 s3 i li lc0 lc' H1 H2.
exists s2. exists lc0. exists lc'. split; auto. 
Qed.

Lemma sem_IE s i s' li:
  sem_I s i li s' ->
  let 'MkI ii r := i in
  sem_i s r li s'.
Proof. by case. Qed.

Lemma sem_iE s i s' li:
  sem_i s i li s' ->
  match i with
  | Cassgn lv _ ty e =>
    ∃ v v' le lw,
    [/\ sem_pexpr gd s e = ok (v, le), truncate_val ty v = ok v' & write_lval gd lv v' s = ok (s', lw) ]
  | Copn lvs _ op es => ∃ lo, sem_sopn gd op s lvs es = ok (s', lo)
  | Cif e th el =>
    ∃ b le lc, sem_pexpr gd s e = ok (Vbool b, le) ∧ sem s (if b then th else el) lc s'
  | Cfor i r c =>
    ∃ wr lr lf,
    [/\ sem_range s r = ok (wr, lr) &
        sem_for i wr s c lf s' ]
  | Cwhile a c e c' =>
    ∃ si b lc le,
       [/\ sem s c lc si, sem_pexpr gd si e = ok (Vbool b, le) &
                       if b then ∃ sj lc' lw, sem si c' lc' sj ∧ sem_i sj (Cwhile a c e c') lw s' else si = s' ]
  | Ccall _ xs f es =>
    ∃ vs m2 rs lf l2,
    [/\ sem_pexprs gd s es = ok vs, sem_call s.(emem) f (unzip1 vs) lf m2 rs &
       write_lvals gd {|emem:= m2; evm := s.(evm) |} xs rs = ok (s', l2) ]
  end.
Proof.
  case => {s i li s'} //.
  - by move => s s' x _ ty e v v' le lw hv hv' hw; exists v, v', le, lw.
  - by move => s s' e th el le lc he; exists lc; auto.
  - by move => s s' e th el le lc he hel; exists true, le, lc; split; auto.
  - by move => s s' e th el le lc he hel; exists false, le, lc; split; auto.
  - by move =>  s si sj s' a c e c' lc le lc' lw hc he hc' hrec; exists si, true, lc, le; constructor => //; exists sj, lc', lw; constructor => //.
  - by move => s s' a c e c' lc le hc he; exists s', false, lc, le.
  - by move => s s' i r c wr lr lf hr hf; exists wr, lr, lf.
  by move => s m s' _ xs f es vs rs lf l2 hvs h hrs; exists vs, m, rs, lf, l2.
Qed.

Lemma sem_callE m1 fn vargs' m2 vres' lf:
  sem_call m1 fn vargs' lf m2 vres' ->
  ∃ f,
    get_fundef (p_funcs P) fn = Some f ∧
  ∃ vargs s1 vm2 vres lc,
  [/\
    mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs,
    write_vars f.(f_params) vargs (Estate m1 vmap0) = ok s1,
    sem s1 f.(f_body) lc (Estate m2 vm2),
    mapM (fun (x:var_i) => get_var vm2 x) f.(f_res) = ok vres &
    mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ].
Proof.
  case => { m1 fn vargs' lf m2 vres' } m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc.
  move => hf ha hw hc hr ht.
  exists f; split => //.
  by exists vargs, s1, vm2, vres, lc.
Qed.

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
    (Pc   : estate -> cmd -> leak_c -> estate -> Prop)
    (Pi_r : estate -> instr_r -> leak_i -> estate -> Prop)
    (Pi : estate -> instr -> leak_i -> estate -> Prop)
    (Pfor : var_i -> seq Z -> estate -> cmd -> leak_for -> estate -> Prop)
    (Pfun : mem -> funname -> seq value -> leak_fun -> mem -> seq value -> Prop).

  Definition sem_Ind_nil : Prop :=
    forall s : estate, Pc s [::] [::] s.

  Definition sem_Ind_cons : Prop :=
    forall (s1 s2 s3 : estate) (i : instr) (c : cmd) (li : leak_i) (lc : leak_c),
      sem_I s1 i li s2 -> Pi s1 i li s2 -> sem s2 c lc s3 -> Pc s2 c lc s3 -> Pc s1 (i :: c) (li :: lc) s3.

  Hypotheses
    (Hnil: sem_Ind_nil)
    (Hcons: sem_Ind_cons)
  .

  Definition sem_Ind_mkI : Prop :=
    forall (ii : instr_info) (i : instr_r) (s1 s2 : estate) (li : leak_i),
      sem_i s1 i li s2 -> Pi_r s1 i li s2 -> Pi s1 (MkI ii i) li s2.

  Hypothesis HmkI : sem_Ind_mkI.

  Definition sem_Ind_assgn : Prop :=
    forall (s1 s2 : estate) (x : lval) (tag : assgn_tag) ty (e : pexpr) v v' (le lw : leak_e),
      sem_pexpr gd s1 e = ok (v, le) ->
      truncate_val ty v = ok v' →
      write_lval gd x v' s1 = Ok error (s2, lw) ->
      Pi_r s1 (Cassgn x tag ty e) (Lassgn (LSub ([:: le ; lw]))) s2.

  Definition sem_Ind_opn : Prop :=
    forall (s1 s2 : estate) t (o : sopn) (xs : lvals) (es : pexprs) (lo : leak_e),
      sem_sopn gd o s1 xs es = Ok error (s2, lo) ->
      Pi_r s1 (Copn xs t o es) (Lopn lo) s2.

  Definition sem_Ind_if_true : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd) (le : leak_e) (lc : leak_c),
      sem_pexpr gd s1 e = ok (Vbool true, le) ->
      sem s1 c1 lc s2 -> Pc s1 c1 lc s2 -> Pi_r s1 (Cif e c1 c2) (Lcond le true lc) s2.

  Definition sem_Ind_if_false : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd) (le : leak_e) (lc : leak_c),
      sem_pexpr gd s1 e = ok (Vbool false, le) ->
      sem s1 c2 lc s2 -> Pc s1 c2 lc s2 -> Pi_r s1 (Cif e c1 c2) (Lcond le false lc) s2.

  Definition sem_Ind_while_true : Prop :=
    forall (s1 s2 s3 s4 : estate) a (c : cmd) (e : pexpr) (c' : cmd) (lc : leak_c) 
           (le : leak_e) (lc' : leak_c) (li : leak_i),
      sem s1 c lc s2 -> Pc s1 c lc s2 ->
      sem_pexpr gd s2 e = ok (Vbool true, le) ->
      sem s2 c' lc' s3 -> Pc s2 c' lc' s3 ->
      sem_i s3 (Cwhile a c e c') li s4 -> 
      Pi_r s3 (Cwhile a c e c') li s4 -> 
      Pi_r s1 (Cwhile a c e c') (Lwhile_true lc le lc' li) s4.

  Definition sem_Ind_while_false : Prop :=
    forall (s1 s2 : estate) a (c : cmd) (e : pexpr) (c' : cmd) (lc : leak_c) (le : leak_e),
      sem s1 c lc s2 -> Pc s1 c lc s2 ->
      sem_pexpr gd s2 e = ok (Vbool false, le) ->
      Pi_r s1 (Cwhile a c e c') (Lwhile_false lc le) s2.

  Hypotheses
    (Hasgn: sem_Ind_assgn)
    (Hopn: sem_Ind_opn)
    (Hif_true: sem_Ind_if_true)
    (Hif_false: sem_Ind_if_false)
    (Hwhile_true: sem_Ind_while_true)
    (Hwhile_false: sem_Ind_while_false)
  .

  Definition sem_Ind_for : Prop :=
    forall (s1 s2 : estate) (i : var_i) r wr (c : cmd) (lr : leak_e) (lf: leak_for),
      sem_range s1 r = ok (wr, lr) ->
      sem_for i wr s1 c lf s2 ->
      Pfor i wr s1 c lf s2 -> Pi_r s1 (Cfor i r c) (Lfor lr lf) s2.

  Definition sem_Ind_for_nil : Prop :=
    forall (s : estate) (i : var_i) (c : cmd),
      Pfor i [::] s c [::] s.

  Definition sem_Ind_for_cons : Prop :=
    forall (s1 s1' s2 s3 : estate) (i : var_i) (w : Z) (ws : seq Z) (c : cmd) (lc : leak_c) (lf : leak_for),
      write_var i w s1 = Ok error s1' ->
      sem s1' c lc s2 -> Pc s1' c lc s2 ->
      sem_for i ws s2 c lf s3 -> Pfor i ws s2 c lf s3 -> Pfor i (w :: ws) s1 c (lc :: lf) s3.

  Hypotheses
    (Hfor: sem_Ind_for)
    (Hfor_nil: sem_Ind_for_nil)
    (Hfor_cons: sem_Ind_for_cons)
  .

  Definition sem_Ind_call : Prop :=
    forall (s1 : estate) (m2 : mem) (s2 : estate)
           (ii : inline_info) (xs : lvals)
           (fn : funname) (args : pexprs) (vargs : seq (value * leak_e)) (vs : seq value) (lf : leak_fun) (lw : seq leak_e),
      sem_pexprs gd s1 args = Ok error vargs ->
      sem_call (emem s1) fn (unzip1 vargs) lf m2 vs -> Pfun (emem s1) fn (unzip1 vargs) lf m2 vs ->
      write_lvals gd {| emem := m2; evm := evm s1 |} xs vs = Ok error (s2, lw) ->
      Pi_r s1 (Ccall ii xs fn args) (Lcall (LSub (unzip2 vargs)) lf (LSub lw)) s2.

  Definition sem_Ind_proc : Prop :=
    forall (m1 m2 : mem) (fn:funname) (f : fundef) (vargs vargs': seq value)
           (s1 : estate) (vm2 : vmap) (vres vres': seq value) (lc : leak_c),
      get_fundef (p_funcs P) fn = Some f ->
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
      sem s1 (f_body f) lc {| emem := m2; evm := vm2 |} ->
      Pc s1 (f_body f) lc {| emem := m2; evm := vm2 |} ->
      mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
      mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
      Pfun m1 fn vargs' (fn, lc) m2 vres'.

  Hypotheses
    (Hcall: sem_Ind_call)
    (Hproc: sem_Ind_proc)
  .

  Fixpoint sem_Ind (e : estate) (l : cmd) (le : leak_c) (e0 : estate) (s : sem e l le e0) {struct s} :
    Pc e l le e0 :=
    match s in (sem e1 l0 l1 e2) return (Pc e1 l0 l1 e2) with
    | Eskip s0 => Hnil s0
    | @Eseq s1 s2 s3 i c li lc s0 s4 =>
        @Hcons s1 s2 s3 i c li lc s0 (@sem_I_Ind s1 i li s2 s0) s4 (@sem_Ind s2 c lc s3 s4) 
    end

  with sem_i_Ind (e : estate) (i : instr_r) (li : leak_i) (e0 : estate) (s : sem_i e i li e0) {struct s} :
    Pi_r e i li e0 :=
    match s in (sem_i e1 i0 le1 e2) return (Pi_r e1 i0 le1 e2) with
    | @Eassgn s1 s2 x tag ty e1 v v' l1 l2 h1 h2 h3 => @Hasgn s1 s2 x tag ty e1 v v' l1 l2 h1 h2 h3
    | @Eopn s1 s2 t o xs es lo e1 => @Hopn s1 s2 t o xs es lo e1
    | @Eif_true s1 s2 e1 c1 c2 le lc e2 s0 =>
      @Hif_true s1 s2 e1 c1 c2 le lc e2 s0 (@sem_Ind s1 c1 lc s2 s0)
    | @Eif_false s1 s2 e1 c1 c2 le lc e2 s0 =>
      @Hif_false s1 s2 e1 c1 c2 le lc e2 s0 (@sem_Ind s1 c2 lc s2 s0)
    | @Ewhile_true s1 s2 s3 s4 a c e1 c' lc le lc' lw h1 h2 h3 h4 =>
      @Hwhile_true s1 s2 s3 s4 a c e1 c' lc le lc' lw h1 (@sem_Ind s1 c lc s2 h1) h2 h3 (@sem_Ind s2 c' lc' s3 h3) 
          h4 (@sem_i_Ind s3 (Cwhile a c e1 c') lw s4 h4)
    | @Ewhile_false s1 s2 a c e1 c' lc le s0 e2 =>
      @Hwhile_false s1 s2 a c e1 c' lc le s0 (@sem_Ind s1 c lc s2 s0) e2
    | @Efor s1 s2 i0 r c wr lr lf s0 sf =>
      @Hfor s1 s2 i0 r wr c lr lf s0 sf
        (@sem_for_Ind i0 wr s1 c lf s2 sf)
    | @Ecall s1 m2 s2 ii xs f13 args vargs vs lf l2 e2 s0 e3 =>
      @Hcall s1 m2 s2 ii xs f13 args vargs vs lf l2 e2 s0
        (@sem_call_Ind (emem s1) f13 (unzip1 vargs) m2 vs lf s0) e3
    end

  with sem_I_Ind (e : estate) (i : instr) (li : leak_i) (e0 : estate) (s : sem_I e i li e0) {struct s} :
    Pi e i li e0 :=
    match s in (sem_I e1 i0 le e2) return (Pi e1 i0 le e2) with
    | @EmkI ii i0 s1 s2 li s0 => @HmkI ii i0 s1 s2 li s0 (@sem_i_Ind s1 i0 li s2 s0)
    end

  with sem_for_Ind (v : var_i) (l : seq Z) (e : estate) (l0 : cmd) (lf : leak_for) (e0 : estate)
         (s : sem_for v l e l0 lf e0) {struct s} : Pfor v l e l0 lf e0 :=
    match s in (sem_for v0 l1 e1 l2 le e2) return (Pfor v0 l1 e1 l2 le e2) with
    | EForDone s0 i c => Hfor_nil s0 i c
    | @EForOne s1 s1' s2 s3 i w ws c lc lw e1 s0 s4 =>
      @Hfor_cons s1 s1' s2 s3 i w ws c lc lw e1 s0 (@sem_Ind s1' c lc s2 s0)
         s4 (@sem_for_Ind i ws s2 c lw s3 s4)
    end

  with sem_call_Ind (m : mem) (f13 : funname) (l : seq value) (m0 : mem)
         (l0 : seq value) (lf : leak_fun) (s : sem_call m f13 l lf m0 l0) {struct s} : Pfun m f13 l lf m0 l0 :=
    match s with
    | @EcallRun m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hget Hctin Hw Hsem Hvres Hctout =>
       @Hproc m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hget Hctin Hw Hsem (sem_Ind Hsem) Hvres Hctout
    end.


End SEM_IND.

End SEM.

(* -------------------------------------------------------------------- *)
(* Proving some properties                                              *)
(* -------------------------------------------------------------------- *)

Lemma truncate_word_u s (a : word s): truncate_word s a = ok a.
Proof. by rewrite /truncate_word cmp_le_refl zero_extend_u. Qed.

Lemma truncate_wordP s1 s2 (w1:word s1) (w2:word s2) :
  truncate_word s1 w2 = ok w1 →
  (s1 <= s2)%CMP /\ w1 = zero_extend s1 w2.
Proof. by rewrite /truncate_word;case:ifP => // Hle []. Qed.

Lemma truncate_word_errP s1 s2 (w: word s2) e :
  truncate_word s1 w = Error e →
  e = ErrType ∧ (s2 < s1)%CMP.
Proof.
by rewrite /truncate_word; case: ifP => // /negbT; rewrite cmp_nle_lt => ? [].
Qed.

Lemma of_val_type_of_val (v: value) :
  (if v is Vundef _ then false else true) →
  exists2 x, of_val (type_of_val v) v = ok x & to_val x = v.
Proof.
case: v => //=; eauto.
+ move=> n a _;rewrite /WArray.cast.
  exists a => //; case: ifP => /ZleP; last by lia.
  by move=> _; f_equal;case: a.
by move => sz w; rewrite truncate_word_u; eauto.
Qed.

Lemma to_boolI x b :
  to_bool x = ok b →
  x = b.
Proof. case: x => //=; last by case. by move => ? /(@ok_inj _ _ _ _) ->. Qed.

Lemma of_val_int v z: of_val sint v = ok z -> v = Vint z.
Proof. by case v=> //= [? [->] | []]. Qed.

Lemma to_wordI sz v w:
  to_word sz v = ok w →
  ∃ sz' (w': word sz'), [/\ (sz <= sz')%CMP, v = Vword w' & w = zero_extend sz w'].
Proof.
 case: v => //=.
 + by move=> s w' /truncate_wordP [];exists s, w'.
 by case => // ?;case: ifP => //.
Qed.

Corollary of_val_word sz v w :
  of_val (sword sz) v = ok w →
  ∃ sz' (w': word sz'), [/\ (sz <= sz')%CMP, v = Vword w' & w = zero_extend sz w'].
Proof. exact: to_wordI. Qed.

Lemma to_intI v n: to_int v = ok n → v = n.
Proof. by case: v => //= [? [<-] | [] ]. Qed.

Lemma to_arrI n v t : to_arr n v = ok t -> exists n' (t':WArray.array n'), [/\ v = Varr t', (n <= n')%Z & t = {| WArray.arr_data := WArray.arr_data t'|}].
Proof.
  case: v => //= [n' t' | [] //].
  rewrite /WArray.cast;case:ZleP => // ? [<-].
  by exists n', t'.
Qed.

Lemma of_val_subtype t v sv : of_val t v = ok sv -> subtype t (type_of_val v).
Proof.
  case: t sv => /= [ | |p|ws] sv.
  + by move=> /to_boolI ->.
  + by move=> /to_intI ->.
  + by move=> /to_arrI [n' [t' [-> /ZleP hle ?]]] /=.
  by move=> /to_wordI [ws' [w [? -> ?]]] /=.
Qed.

Lemma sopn_tinP o vs vs' : exec_sopn o vs = ok vs' ->
  all2 subtype (sopn_tin o) (List.map type_of_val vs).
Proof.
  rewrite /exec_sopn /sopn_tin /sopn_sem.
  case (get_instr o) => /= _ tin _ tout _ semi _ _ _.
  t_xrbindP => p hp _.
  elim: tin vs semi hp => /= [ | t tin hrec] [ | v vs] // semi.
  by t_xrbindP => sv /= /of_val_subtype -> /hrec.
Qed.

Lemma on_arr_varP A (f : forall n, WArray.array n -> exec A) v s x P0:
  (forall n t, subtype (sarr n) (vtype x) ->
       get_var (evm s) x = ok (@Varr n t) ->
       f n t = ok v -> P0) ->
  on_arr_var s x f = ok v -> P0.
Proof.
  rewrite /on_arr_var /= => H;apply: rbindP => vx.
  case: x H => -[ | | n | sz ] /= nx;rewrite /get_var => H;
    case Heq : ((evm s).[_])%vmap => [v' | e] //=; rewrite /= in H.
  + by move=> [<-]. + by case: (e) => // -[<-].
  + by move=> [<-]. + by case: (e) => // -[<-].
  + move=> [<-]; apply: H => /=; first by apply Z.leb_refl.
    by rewrite Heq /=.
  + by case: (e) => // -[<-].
  + by move=> [<-]. + by case: (e) => // -[<-].
Qed.

Definition Varr_inj := Varr_inj.

Definition Varr_inj1 := Varr_inj1.

Definition Vword_inj sz sz' w w' (e: @Vword sz w = @Vword sz' w') :
  ∃ e : sz = sz', eq_rect sz (λ s, (word s)) w sz' e = w' :=
  let 'Logic.eq_refl := e in (ex_intro _ erefl erefl).

Lemma ok_word_inj E sz sz' w w' :
  ok (@Vword sz w) = Ok E (@Vword sz' w') →
  ∃ e : sz = sz', eq_rect sz word w sz' e = w'.
Proof. by move => h; have /Vword_inj := ok_inj h. Qed.

Lemma truncate_val_subtype ty v v' :
  truncate_val ty v = ok v' →
  subtype ty (type_of_val v).
Proof.
  case: ty v => [ | | n | sz ] [] //; try by case.
  - move => n' t; rewrite /truncate_val /=.
    by rewrite /WArray.cast; case: ifP.
  by move => sz' w; rewrite /truncate_val /=; t_xrbindP => w' /truncate_wordP [].
Qed.

Lemma truncate_val_has_type ty v v' :
  truncate_val ty v = ok v' →
  type_of_val v' = ty.
Proof.
  case: ty v => [ | | n | sz ] [] //; try by case.
  - by move => b [<-].
  - by move => z [<-].
  - move => n' t; rewrite /truncate_val /= /WArray.cast.
    by case: ifP => h //= [<-].
  by move => sz' w; rewrite /truncate_val /=; t_xrbindP => w' /truncate_wordP [] ? -> <-.
Qed.

Lemma truncate_val_wordI ty v sz w :
  truncate_val ty v = ok (@Vword sz w) →
  ∃ sz' (w': word sz'), ty = sword sz /\ v = Vword w' ∧ (sz ≤ sz')%CMP /\ w = zero_extend sz w'.
Proof.
case: ty v => [ | | n | s ] [] //; try by case.
- by move => n' t; rewrite /truncate_val /= /WArray.cast; case: ifP.
move => sz' w'; rewrite /truncate_val /=.
apply: rbindP => w'' /truncate_wordP [] => hle -> h.
have := ok_inj h => {h} /Vword_inj [] ?; subst => /= ?; subst.
by exists sz', w'.
Qed.

Lemma truncate_val_int ty (z: Z) v :
  truncate_val ty z = ok v →
  ty = sint ∧ v = z.
Proof. by case: ty => // - []. Qed.

Lemma truncate_val_word ty sz (w: word sz) v :
  truncate_val ty (Vword w) = ok v →
  ∃ sz',
    [/\
    ty = sword sz',
    (sz' ≤ sz)%CMP &
    v = Vword (zero_extend sz' w) ].
Proof.
by case: ty => // sz'; apply: rbindP => w' /truncate_wordP [] hle -> [<-]; exists sz'.
Qed.

Lemma truncate_val_bool t (b:bool) v : truncate_val t b = ok v -> t = sbool /\ v = b.
Proof. by case: t => //= -[] <-. Qed.

Lemma truncate_val_boolI t (b:bool) v : truncate_val t v = ok (Vbool b) -> t = sbool /\ v = b.
Proof.
  move=> h; have /= ? := truncate_val_has_type h;subst t.
  by case: v h => //= [ b' [->] | []].
Qed.

Lemma truncate_pto_val ty v v':
  truncate_val ty (@pto_val ty v) = ok v' →
  v' = pto_val v.
Proof.
case: ty v.
+ by move=> ? [<-]. + by move=> ? [<-].
+ move=> p t1; rewrite /truncate_val /= /WArray.cast Z.leb_refl /= => -[<-].
  by f_equal;case: t1.
move => w [] // s v /= hle; apply: rbindP => w' /truncate_wordP [hle'] -> [<-].
by rewrite -(cmp_le_antisym hle hle') zero_extend_u.
Qed.


Lemma is_wconstP gd s sz e w:
  is_wconst sz e = Some w →
  Let vl := sem_pexpr gd s e in
  (to_word sz vl.1) = ok w. 
Proof.
  case: e => // - [] // sz' e /=; case: ifP => // hle /oseq.obindI [z] [h] [<-].
  have := is_constP e; rewrite h => {h} /is_reflect_some_inv -> {e}.
  by rewrite /= /truncate_word hle.
Qed.

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

Lemma size_wrange d z1 z2 :
  size (wrange d z1 z2) = Z.to_nat (z2 - z1).
Proof. by case: d => /=; rewrite ?size_rev size_map size_iota. Qed.

Lemma nth_wrange z0 d z1 z2 n : (n < Z.to_nat (z2 - z1))%nat ->
  nth z0 (wrange d z1 z2) n =
    if   d is UpTo
    then z1 + Z.of_nat n
    else z2 - Z.of_nat n.
Proof.
case: d => ltn /=;
  by rewrite (nth_map 0%nat) ?size_iota ?nth_iota.
Qed.

Lemma last_wrange_up_ne z0 lo hi :
  lo < hi -> last z0 (wrange UpTo lo hi) = hi - 1.
Proof.
move=> lt; rewrite -nth_last nth_wrange; last rewrite size_wrange prednK //.
rewrite size_wrange -subn1 Nat2Z.inj_sub; first by rewrite Z2Nat.id; lia.
+ apply/leP/ltP; rewrite -Z2Nat.inj_0; apply Z2Nat.inj_lt; lia.
+ apply/ltP; rewrite -Z2Nat.inj_0; apply Z2Nat.inj_lt; lia.
Qed.

Lemma last_wrange_up lo hi : last (hi-1) (wrange UpTo lo hi) = hi - 1.
Proof.
case: (Z_lt_le_dec lo hi) => [lt|le]; first by apply: last_wrange_up_ne.
rewrite -nth_last nth_default // size_wrange.
by rewrite [Z.to_nat _](_ : _ = 0%nat) ?Z_to_nat_le0 //; lia.
Qed.

Lemma wrange_cons lo hi : lo < hi ->
  lo - 1 :: wrange UpTo lo hi = wrange UpTo (lo - 1) hi.
Proof.
set s1 := wrange _ _ _; set s2 := wrange _ _ _ => /=.
move=> lt; apply/(@eq_from_nth _ 0) => /=.
+ rewrite {}/s1 {}/s2 !size_wrange -Z2Nat.inj_succ; try lia.
  by apply: Nat2Z.inj; rewrite !Z2Nat.id; lia.
rewrite {1}/s1 size_wrange; case => [|i].
+ rewrite /s2 nth_wrange /=; try lia.
  by rewrite -Z2Nat.inj_0; apply/leP/Z2Nat.inj_lt; lia.
move=> lti; rewrite -[nth _ (_ :: _) _]/(nth 0 s1 i) {}/s1 {}/s2.
rewrite !nth_wrange; first lia; last first.
+ by apply/leP; move/leP: lti; lia.
apply/leP/Nat2Z.inj_lt; rewrite Z2Nat.id; try lia.
move/leP/Nat2Z.inj_lt: lti; try rewrite -Z2Nat.inj_succ; try lia.
by rewrite Z2Nat.id; lia.
Qed.

(* -------------------------------------------------------------------- *)

Lemma sem_app P l1 l2 s1 s2 s3 ls1 ls2:
  sem P s1 l1 ls1 s2 -> sem P s2 l2 ls2 s3 ->
  sem P s1 (l1 ++ l2) (ls1 ++ ls2) s3.
Proof.
  elim: l1 s1 ls1; first by move => s1 ls1 /semE H H1;
  case H => <- ->; auto.
  move=> a l Hrec s1 ls1 /semE [si] [li] [lc'] [h1 hi ->] h /=.
  move: (Hrec si lc' hi h) => H.
  apply Eseq with si; auto.
Qed.

Lemma sem_seq1 P i s1 s2 li:
  sem_I P s1 i li s2 -> sem P s1 [::i] [::li] s2.
Proof.
  move=> Hi. apply Eseq with s2. auto.
  constructor.
Qed.

Lemma sem_seq1_iff P (i : instr) (s1 s2 : estate) li:
  sem_I P s1 i li s2 <-> sem P s1 [::i] [:: li] s2.
Proof.
  split. by apply sem_seq1.
  case /semE=> s [] li' [] lc' [] H1 H2 H. case: H=> -> H'.
  rewrite -H' in H2. inversion H2. by rewrite H4 in H1.
Qed.

Lemma sem_seq1_lis (P : prog) (i : instr) (s1 s2 : estate) lis:
  sem P s1 [::i] lis s2 -> lis = [::head dummy_lit lis].
Proof. by move=> H;inversion_clear H; inversion_clear H1. Qed.

Lemma sem_seq_while P a s1 c lc s2 e le c' lc' s3 lw s4 ii:
  sem P s1 c lc s2 ->
  sem_pexpr (p_globs P) s2 e = ok (Vbool true, le) ->
  sem P s2 c' lc' s3 ->
  sem P s3 [:: (MkI ii (Cwhile a c e c'))] lw s4 ->
  sem_i P s1 (Cwhile a c e c') (Lwhile_true lc le lc' (head dummy_lit lw)) s4.
Proof.
  move=> hc he hc' hi. apply Ewhile_true with s2 s3; auto.
  have hi' : sem P s3 [:: MkI ii (Cwhile a c e c')] lw s4; auto.
  apply sem_seq1_lis in hi. rewrite hi in hi'. move: sem_seq1_iff.
  move=>H. move: (H P (MkI ii (Cwhile a c e c')) s3 s4 (head dummy_lit lw)).
  move=> {H} H. case: H=> H1 H2. apply H2 in hi'. by inversion hi'.
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
  rewrite /write_var;t_xrbindP => vm.
  by apply: set_varP => [t | _] => ? <- <- z Hz; rewrite Fv.setP_neq //;apply /eqP; SvD.fsetdec.
Qed.

Lemma write_noneP s s' ty v:
  write_none s ty v = ok s' ->
  s' = s /\
  ((exists u, pof_val ty v = ok u) \/ pof_val ty v = undef_error ∧ ty = sbool).
Proof.
  apply: on_vuP => [u ? -> | ?].
  + by split => //;left;exists u.
  by case:ifPn => // /eqP ? [->];split => //;right.
Qed.

Lemma vrvP gd (x:lval) v s1 s2 lw:
  write_lval gd x v s1 = ok (s2, lw) ->
  s1.(evm) = s2.(evm) [\ vrv x].
Proof.
  case x => /= [ _ ty | | sz y e|sz y e ] //.
  + by t_xrbindP => ? /write_noneP [->] ? ->.
  + by t_xrbindP => ? ? /vrvP_var -> ->.
  + by t_xrbindP => z z0 He Hve v0 Hv0 t' Ht' w Hw m Hm <-.
  apply: on_arr_varP => n t; case: y => -[] ty yn yi /subtypeEl [n' /= [-> hle]] hget.
  t_xrbindP => we ve He Hve v0 Hv0 t' Ht' vm'.
  rewrite /set_var /= => -[<-] <- _ /=.
  move=> z Hz; rewrite Fv.setP_neq //;apply /eqP;SvD.fsetdec.
Qed.

Lemma vrvsP gd xs vs s1 s2 lw:
  write_lvals gd s1 xs vs = ok (s2, lw) ->
  s1.(evm) = s2.(evm) [\ vrvs xs].
Proof.
  elim: xs vs s1 lw s2 => [|x xs Hrec] [|v vs] s1 lw s2 //=.
  + by move=> [<-].
  t_xrbindP => -[s lw1] /vrvP Hrv [s' lws] /Hrec Hrvs <- Hl /=.
  rewrite vrvs_cons;apply: (@vmap_eq_exceptT (evm s)).
  + by apply: vmap_eq_exceptI Hrv;SvD.fsetdec.
  by apply: vmap_eq_exceptI Hrvs;SvD.fsetdec.
Qed.

Lemma writeP P c s1 s2 lc:
   sem P s1 c lc s2 -> s1.(evm) = s2.(evm) [\ write_c c].
Proof.
  apply (@sem_Ind P (fun s1 c lc s2 => s1.(evm) = s2.(evm) [\ write_c c])
                  (fun s1 i li s2 => s1.(evm) = s2.(evm) [\ write_i i])
                  (fun s1 i li s2 => s1.(evm) = s2.(evm) [\ write_I i])
                  (fun x ws s1 c lc s2 =>
                     s1.(evm) = s2.(evm) [\ (Sv.union (Sv.singleton x) (write_c c))])
                  (fun _ _ _ _ _  _=> True)) => {c s1 s2} //.
  + move=> s1 s2 s3 i c _ _ _ Hi _ Hc z;rewrite write_c_cons => Hnin.
    by rewrite Hi ?Hc //;SvD.fsetdec.
  + move=> s1 s2 x tag ty e v v'? hty Hw z w.
    by rewrite write_i_assgn;apply (vrvP w).
  + move=> s1 s2 t o xs es lo. rewrite /sem_sopn.
    t_xrbindP => -vs /= Hes vs' Hvs' [s3 lw3] /vrvsP /= H1 <- _.
    by rewrite write_i_opn.
  + by move=> s1 s2 e c1 c2 l1 l2 _ _ Hrec z;rewrite write_i_if => Hnin;apply Hrec;SvD.fsetdec.
  + by move=> s1 s2 e c1 c2 l1 l2 _ _ Hrec z;rewrite write_i_if => Hnin;apply Hrec;SvD.fsetdec.
  + by move=> s1 s2 s3 s4 a c e c' l1 l2 l3 l4 _ Hc _ _ Hc' _ Hw z Hnin; rewrite Hc ?Hc' ?Hw //;
    move: Hnin; rewrite write_i_while; SvD.fsetdec.
  + move=> s1 s2 a c e c' l1 l2 _ Hc _ z Hnin; rewrite Hc //.
    by move: Hnin; rewrite write_i_while; SvD.fsetdec.
  + by move=> s1 s2 i r wr c lr lf _ _ Hrec z;rewrite write_i_for;apply Hrec.
  + move=> s1 s1' s2 s3 i w ws c l1 l2 Hw _ Hc _ Hf z Hnin.
    by rewrite (vrvP_var Hw) ?Hc ?Hf //;SvD.fsetdec.
  move=> s1 m2 s2 ii xs fn args vargs vs l2 l3 _ _ _ Hw z.
  by rewrite write_i_call;apply (vrvsP Hw).
Qed.

Lemma write_IP P i s1 s2 Pi:
   sem_I P s1 i Pi s2 -> s1.(evm) = s2.(evm) [\ write_I i].
Proof.
  move=> /sem_seq1 /writeP.
  have := write_c_cons i [::].
  move=> Heq H x Hx;apply H; SvD.fsetdec.
Qed.

Lemma write_iP P i s1 s2 Pi:
   sem_i P s1 i Pi s2 -> s1.(evm) = s2.(evm) [\ write_i i].
Proof. by move=> /EmkI -/(_ 1%positive) /write_IP. Qed.

Lemma disjoint_eq_on gd s r s1 s2 v lw:
  disjoint s (vrv r) ->
  write_lval gd r v s1 = ok (s2, lw) ->
  s1.(evm) =[s] s2.(evm).
Proof.
  move=> Hd /vrvP H z Hnin;apply H.
  move:Hd;rewrite /disjoint /is_true Sv.is_empty_spec;SvD.fsetdec.
Qed.

Lemma disjoint_eq_ons gd s r s1 s2 v lw:
  disjoint s (vrvs r) ->
  write_lvals gd s1 r v = ok (s2, lw) ->
  s1.(evm) =[s] s2.(evm).
Proof.
  move=> Hd /vrvsP H z Hnin;apply H.
  move:Hd;rewrite /disjoint /is_true Sv.is_empty_spec;SvD.fsetdec.
Qed.

Lemma get_var_eq_on s vm' vm v: Sv.In v s -> vm =[s]  vm' -> get_var vm v = get_var vm' v.
Proof. by move=> Hin Hvm;rewrite /get_var Hvm. Qed.

Lemma on_arr_var_eq_on s' X s A x (f: ∀ n, WArray.array n → exec A) :
   evm s =[X] evm s' -> Sv.In x X ->
   on_arr_var s x f = on_arr_var s' x f.
Proof.
  by move=> Heq Hin;rewrite /on_arr_var;rewrite (get_var_eq_on Hin Heq).
Qed.

Section READ_E_ES_EQ_ON.
  Context (gd: glob_decls) (m: mem) (vm vm': vmap).

  Let P e : Prop :=
    ∀ s : Sv.t, vm =[read_e_rec s e]  vm' →
    sem_pexpr gd {| emem := m; evm := vm |} e = sem_pexpr gd {| emem := m; evm := vm' |} e.

  Let Q es : Prop :=
    ∀ s, vm =[read_es_rec s es] vm' →
         mapM (sem_pexpr gd (Estate m vm)) es = mapM (sem_pexpr gd (Estate m vm')) es.

  Lemma read_e_es_eq_on : (∀ e, P e) * (∀ es, Q es).
  Proof.
    apply: pexprs_ind_pair ; split; subst P Q => //=.
    - move => e rec es ih s Heq /=.
      have Heq' : vm =[read_e_rec s e] vm'.
      + apply: (eq_onI _ Heq); rewrite /= read_esE; SvD.fsetdec.
      move: rec => /(_ _ Heq') ->.
      by move: ih => /(_ _ Heq) ->.
    - by move=> x s /get_var_eq_on -> //; SvD.fsetdec.
    - move=> sz x e He s Heq; rewrite (He _ Heq) => {He}.
      rewrite (@on_arr_var_eq_on
          {| emem := m; evm := vm' |} _ {| emem := m; evm := vm |} _ _ _ Heq) ?read_eE //.
        by SvD.fsetdec.
    - by move=> sz x e He s Hvm; rewrite (get_var_eq_on _ Hvm) ?(He _ Hvm) // read_eE;SvD.fsetdec.
    - by move=> op e He s /He ->.
    - move => op e1 He1 e2 He2 s Heq; rewrite (He1 _ Heq) (He2 s) //.
      by move=> z Hin; apply Heq; rewrite read_eE; SvD.fsetdec.
    - move=> op es Hes s heq. rewrite -!/(sem_pexprs gd {| emem := m |}).
      by move: (Hes s heq) => ->.
    move=> t e He e1 He1 e2 He2 s Heq. rewrite (He _ Heq) (He1 s) //. 
    rewrite (He2 s); auto.
    move=> z Hin; apply Heq; rewrite !read_eE.
    by move: Hin;rewrite read_eE;SvD.fsetdec.
    move=> z Hin;apply Heq;rewrite !read_eE.
    by move: Hin;rewrite read_eE;SvD.fsetdec.
  Qed.

End READ_E_ES_EQ_ON.

Definition read_e_eq_on gd s vm' vm m e :=
  (read_e_es_eq_on gd m vm vm').1 e s.

Lemma read_es_eq_on gd es s m vm vm' : vm =[read_es_rec s es] vm' →
         sem_pexprs gd (Estate m vm) es = sem_pexprs gd (Estate m vm') es.
Proof.
  rewrite /sem_pexprs => Hvm.
  by rewrite ((read_e_es_eq_on gd m vm vm').2 es s).
Qed.

Lemma set_var_eq_on s x v vm1 vm2 vm1':
  set_var vm1 x v = ok vm2 ->
  vm1 =[s]  vm1' ->
  exists vm2' : vmap,
     vm2 =[Sv.union (Sv.add x Sv.empty) s]  vm2' /\
     set_var vm1' x v = ok vm2'.
Proof.
  (apply: set_varP;rewrite /set_var) => [t | ->] -> <- hvm /=.
  + exists (vm1'.[x <- ok t])%vmap;split => // z hin.
    case: (x =P z) => [<- | /eqP Hxz];first by rewrite !Fv.setP_eq.
    by rewrite !Fv.setP_neq ?hvm //;move/eqP:Hxz; SvD.fsetdec.
  exists (vm1'.[x <- pundef_addr (vtype x)])%vmap;split => // z Hin.
  case: (x =P z) => [<- | /eqP Hxz];first by rewrite !Fv.setP_eq.
  by rewrite !Fv.setP_neq ?hvm //;move/eqP:Hxz; SvD.fsetdec.
Qed.

Lemma write_var_eq_on X x v s1 s2 vm1:
  write_var x v s1 = ok s2 ->
  evm s1 =[X] vm1 ->
  exists vm2 : vmap,
    evm s2 =[Sv.add x X]  vm2 /\
    write_var x v {| emem := emem s1; evm := vm1 |} = ok {| emem := emem s2; evm := vm2 |}.
Proof.
  rewrite /write_var /=;t_xrbindP => vm2 Hset <-.
  move=> /(set_var_eq_on Hset) [vm2' [Hvm2 ->]];exists vm2';split=>//=.
  by apply: eq_onI Hvm2;SvD.fsetdec.
Qed.

Lemma write_lval_eq_on gd X x v s1 s2 vm1 lw:
  Sv.Subset (read_rv x) X ->
  write_lval gd x v s1 = ok (s2, lw) ->
  evm s1 =[X] vm1 ->
  exists vm2 : vmap,
   evm s2 =[Sv.union (vrv x) X] vm2 /\
   write_lval gd x v {|emem:= emem s1; evm := vm1|} = ok ({|emem:= emem s2; evm := vm2|}, lw).
Proof.
  case:x => [vi ty | x | sz x e | sz' x e ] /=.
  + t_xrbindP => ? y /write_noneP [->]; rewrite /write_none=> H <- <-;exists vm1;split=>//.
    case:H => [[u ->] | [->] ->]; auto.
  + move=> Hsub.
    t_xrbindP => y Hw <- <- /(write_var_eq_on Hw) [vm2 [Hvm2 ->]];exists vm2;split=>//.
    apply: eq_onI Hvm2. SvD.fsetdec. 
  + rewrite read_eE => Hsub Hsem Hvm;move:Hsem.
    rewrite -(get_var_eq_on _ Hvm);last by SvD.fsetdec.
    rewrite (get_var_eq_on _ Hvm);last by SvD.fsetdec.
    case: s1 Hvm => sm1 svm1 Hvm1.
    rewrite (@read_e_eq_on gd Sv.empty vm1 svm1);first last. 
    rewrite /= in Hvm1.
    apply: eq_onI Hvm1;rewrite read_eE. SvD.fsetdec.
    t_xrbindP => y h -> /= -> /= h2 -> /= h4 -> /= h6 -> /= h8 -> /= <- ->.
    exists vm1; split=>//.
  rewrite read_eE => Hsub Hsem Hvm;move:Hsem.
  apply: on_arr_varP => n t Htx; rewrite /on_arr_var.
  rewrite -(get_var_eq_on _ Hvm);last by SvD.fsetdec.
  rewrite (get_var_eq_on _ Hvm);last by SvD.fsetdec.
  case: s1 Hvm => sm1 svm1 /= Hvm1.
  rewrite (@read_e_eq_on gd Sv.empty vm1 svm1);first last. 
  apply: eq_onI Hvm1;rewrite read_eE. SvD.fsetdec.
  move=> ->.
  t_xrbindP => v1 -> /= i -> /= v0 -> /= a -> /= vm /set_var_eq_on Hvm2.
  move: (Hvm2 X vm1 Hvm1). move=> [] x0 Hvm2' <- /= -> /=.
  exists x0; split. apply Hvm2'.
  by case: Hvm2' => _ -> /=.
Qed.

Lemma write_lvals_eq_on gd X xs vs s1 s2 vm1 lw:
  Sv.Subset (read_rvs xs) X ->
  write_lvals gd s1 xs vs = ok (s2, lw) ->
  evm s1 =[X] vm1 ->
  exists vm2 : vmap,
    evm s2 =[Sv.union (vrvs xs) X] vm2 /\
    write_lvals gd {| emem:= emem s1; evm := vm1|} xs vs = ok ({|emem:= emem s2; evm := vm2|}, lw).
Proof.
 rewrite /write_lvals.
 elim: xs vs X s1 s2 lw vm1 => [ | x xs Hrec] [ | v vs] //= X s1 lw s2 vm1.
 + move=> Hsub [<- <-] Hvm. exists vm1. by split.
 rewrite read_rvs_cons => Hsub.
 t_xrbindP.
 move=> [s1' l1'] Hw [s2' l2'] Hws <- <- /(write_lval_eq_on _ Hw) [ |vm1' [Hvm1' ->]].
 + by SvD.fsetdec.
  have [ |vm2 [Hvm2 /= ->]]:= Hrec _ _ _ _ _ _ _ Hws Hvm1';first by SvD.fsetdec.
  by exists vm2;split => //;rewrite vrvs_cons;apply: eq_onI Hvm2;SvD.fsetdec.
Qed.

Notation "vm1 = vm2 [\ s ]" := (vmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Notation "vm1 '=[' s ']' vm2" := (eq_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  =[ s ]  '/'  vm2 ']'").

Definition word_uincl sz1 sz2 (w1:word sz1) (w2:word sz2) :=
  (sz1 <= sz2)%CMP && (w1 == zero_extend sz1 w2).

Lemma word_uincl_refl s (w : word s): word_uincl w w.
Proof. by rewrite /word_uincl zero_extend_u cmp_le_refl eqxx. Qed.
Hint Resolve word_uincl_refl.

Lemma word_uincl_eq s (w w': word s):
  word_uincl w w' → w = w'.
Proof. by move=> /andP [] _ /eqP; rewrite zero_extend_u. Qed.

Lemma word_uincl_trans s2 w2 s1 s3 w1 w3 :
   @word_uincl s1 s2 w1 w2 -> @word_uincl s2 s3 w2 w3 -> word_uincl w1 w3.
Proof.
  rewrite /word_uincl => /andP [hle1 /eqP ->] /andP [hle2 /eqP ->].
  by rewrite (cmp_le_trans hle1 hle2) zero_extend_idem // eqxx.
Qed.

(* ------------------------------------------ *)

(*Definition type_uincl t1 t2 :=
  match t1 with
  | sbool => t2 == sbool
  | sint => t2 == sint
  | sarr n1 =>
    if t2 is sarr n2 then (n1 <=? n2)
    else false
  | sword _ => is_sword t2 is sword _ then true else false
  end. *)

Definition value_uincl (v1 v2:value) :=
  match v1, v2 with
  | Vbool b1, Vbool b2 => b1 = b2
  | Vint n1, Vint n2   => n1 = n2
  | Varr n1 t1, Varr n2 t2 => WArray.uincl t1 t2
  | Vword sz1 w1, Vword sz2 w2 => word_uincl w1 w2
  | Vundef t, _     => compat_type t (type_of_val v2)
  | _, _ => False
  end.

Lemma value_uinclE v1 v2 :
  value_uincl v1 v2 →
  match v1 with
  | Vbool _ | Vint _ => v2 = v1
  | Varr n1 t1 =>
    exists n2,
      exists2 t2, v2 = @Varr n2 t2 & WArray.uincl t1 t2
  | Vword sz1 w1 => ∃ sz2 w2, v2 = @Vword sz2 w2 ∧ word_uincl w1 w2
  | Vundef t => compat_type t (type_of_val v2)
  end.
Proof.
  case: v1 v2 => [ b1 | n1 | n1 t1 | sz1 w1 | t1 ] [] //=; eauto; try by move => ? <-.
Qed.

(*Lemma type_uincl_refl t : type_uincl t t.
Proof. case: t => //=; move=> *; apply Z.leb_refl. Qed.
Lemma type_uincl_trans t2 t1 t3:
  type_uincl t1 t2 -> type_uincl t2 t3 -> type_uincl t1 t3.
Proof.
  case: t1 t2 t3 => [||n1| ?] [] //= n2 [] // n3 /ZleP h1 /ZleP h2.
  apply /ZleP; apply: Z.le_trans h1 h2.
Qed.
Lemma type_uincl_compat t1 t2 : type_uincl t1 t2 -> compat_type t1 t2.
Proof. by case: t1 => //= ?;case: t2. Qed.
Lemma subtype_type_uincl t1 t2 : subtype t1 t2 -> type_uincl t1 t2.
Proof.
  by case: t1 => //= [/eqP ->| /eqP -> | ] //; case: t2.
Qed.
Lemma subtype_compat t1 t2 : subtype t1 t2 -> compat_type t1 t2.
Proof.
  by move=> /subtype_type_uincl -/type_uincl_compat.
Qed.
*)

Lemma subtype_compat t1 t2 : subtype t1 t2 -> compat_type t1 t2.
Proof.
  by case: t1 => [/eqP ->| /eqP -> | p | w] // ; case: t2.
Qed.

Lemma compat_type_undef t : compat_type t (vundef_type t).
Proof. by case t. Qed.

(*Lemma type_uincl_undeft t : type_uincl (vundef_type t) t.
Proof. case t => //= ?; apply Z.leb_refl. Qed.
(* use compat_subtype_undef *)
Lemma type_uincl_subtype_undef t1 t2 : type_uincl t1 t2 → subtype (vundef_type t1) t2.
Proof.
case: t1 => [/eqP ->|/eqP ->|?|?] //=; case: t2 => //= ??.
by apply wsize_le_U8.
Qed.
*)

Lemma compat_subtype_undef t1 t2 : compat_type t1 t2 → subtype (vundef_type t1) t2.
Proof.
  case: t1 => [/eqP ->|/eqP ->|?|?] //=; case: t2 => // *.
  + by apply /ZleP;lia.
  by apply wsize_le_U8.
Qed.

Lemma subtype_type_of_val t (v:psem_t t):
  subtype (type_of_val (pto_val v)) t.
Proof.
  case: t v => //= s w.
  + by apply Z.leb_refl.
  by apply pw_proof.
Qed.

(*
Lemma type_uincl_pto_val t (s : psem_t t) :
  type_uincl t (type_of_val (pto_val s)).
Proof. case: t s => //= ??; apply Z.leb_refl. Qed.
*)

Lemma subtype_vundef_type t : subtype (vundef_type t) t.
Proof. by apply compat_subtype_undef. Qed.

Lemma vundef_type_idem v : vundef_type v = vundef_type (vundef_type v).
Proof. by case: v. Qed.

(* -------------------------------------------- *)
Lemma value_uincl_refl v: @value_uincl v v.
Proof. by case: v => //=; apply compat_type_undef. Qed.

Hint Resolve value_uincl_refl.

Lemma value_uincl_trans v2 v1 v3 :
  value_uincl v1 v2 ->
  value_uincl v2 v3 ->
  value_uincl v1 v3.
Proof.
  case: v1; case: v2 => //=; last (by
   move=> ?? h; apply:compat_type_trans;
   apply : (compat_type_trans h); rewrite compat_typeC compat_type_undef);
  case:v3=> //=.
  + by move=> ??? ->.
  + by move=> ??? ->.
  + by move=> ?? ?? ??; apply: WArray.uincl_trans.
  by move=> //= ??????;apply word_uincl_trans.
Qed.

(* -------------------------------------------- *)

Lemma value_uincl_int1 z v : value_uincl (Vint z) v -> v = Vint z.
Proof. by case: v => //= ? ->. Qed.

Lemma value_uincl_int ve ve' z :
  value_uincl ve ve' -> to_int ve = ok z -> ve = z /\ ve' = z.
Proof. by case: ve => // [ b' /value_uincl_int1 -> [->]| []//]. Qed.

Lemma value_uincl_bool1 b v : value_uincl (Vbool b) v -> v = Vbool b.
Proof. by case: v => //= ? ->. Qed.

Lemma value_uincl_bool ve ve' b :
  value_uincl ve ve' -> to_bool ve = ok b -> ve = b /\ ve' = b.
Proof. by case: ve => // [ b' /value_uincl_bool1 -> [->]| []//]. Qed.

Lemma value_uincl_word ve ve' sz (w: word sz) :
  value_uincl ve ve' →
  to_word sz ve  = ok w →
  to_word sz ve' = ok w.
Proof.
case: ve ve' => //=.
+ move => sz' w' [] // sz1 w1 /andP [] hle /eqP -> /truncate_wordP [] hle'.
  by rewrite zero_extend_idem // => -> /=; rewrite /truncate_word (cmp_le_trans hle' hle).
by case => // sz' ve' _; case: ifP.
Qed.

Lemma value_uincl_subtype v1 v2 :
  value_uincl v1 v2 ->
  subtype (type_of_val v1) (type_of_val v2).
Proof.
case: v1 v2 => [ b | i | n t | s w | ty ]; try by case.
+ by case => //= n' t' [] /ZleP.
+ by case => //= s' w' /andP[].
by move => /= v2; apply compat_subtype_undef.
Qed.

Lemma value_uincl_is_defined x y :
  value_uincl x y →
  is_defined x →
  is_defined y.
Proof. by case: y => //=; case; case: x. Qed.

Lemma value_uincl_compat_type v1 v1' v2 v2':
  value_uincl v1 v1' -> value_uincl v2 v2' ->
  compat_type (type_of_val v1) (type_of_val v2) ->
  compat_type (type_of_val v1') (type_of_val v2').
Proof.
  move=> /value_uincl_subtype -/subtype_compat h1.
  move=> /value_uincl_subtype -/subtype_compat h2 hc.
  apply: compat_type_trans h2; apply: compat_type_trans hc.
  by rewrite compat_typeC.
Qed.

Lemma word_uincl_zero_ext sz sz' (w':word sz') : (sz ≤ sz')%CMP -> word_uincl (zero_extend sz w') w'.
Proof. by move=> ?;apply /andP. Qed.

Lemma word_uincl_zero_extR sz sz' (w: word sz) :
  (sz ≤ sz')%CMP →
  word_uincl w (zero_extend sz' w).
Proof.
  move => hle; apply /andP; split; first exact: hle.
  by rewrite zero_extend_idem // zero_extend_u.
Qed.

Lemma value_uincl_zero_ext sz sz' (w':word sz') : (sz ≤ sz')%CMP ->
  value_uincl (Vword (zero_extend sz w')) (Vword w').
Proof. apply word_uincl_zero_ext. Qed.

Lemma pof_val_undef_ok t t' v:
  pof_val t (Vundef t') <> ok v.
Proof. by case: t t' v => //= [||p|s][]. Qed.

Lemma of_val_Vword t s1 (w1:word s1) w2 : of_val t (Vword w1) = ok w2 ->
  exists s2 (e:t = sword s2),
    (s2 <= s1)%CMP /\  eq_rect t sem_t w2 _ e = zero_extend s2 w1.
Proof.
  case: t w2 => //= s2 w2 /truncate_wordP [] hle ->.
  by exists s2, erefl.
Qed.

Lemma truncate_value_uincl ty x y x' :
  value_uincl x y →
  truncate_val ty x = ok x' →
  exists2 y', truncate_val ty y = ok y' & value_uincl x' y'.
Proof.
case: ty x y => //.
- by case => // [ b | [] ] // [] //= ? <- [<-]; exists (Vbool b).
- by case => // [ z | [] ] // [] //= ? <- [<-]; exists (Vint z).
- move => n; case => // [ n' t' | [] // ] [] //=.
  move => n'' t [hle hget]; rewrite /truncate_val /= /WArray.cast.
  case: ifPn => /ZleP //= h1 [<-].
  case: ifPn => /ZleP //= h2;last by lia.
  eexists; split => //=; first by apply Z.le_refl.
  by move=> ??? /hget h3;apply h3;lia.
(move => sz; case => // [ sz' w | [] // sz' ];
case) => // sz'' w' /=.
case/andP => hsz' /eqP -> {w}; rewrite /truncate_val /= /truncate_word.
case: ifP => // hsz [<-].
rewrite (cmp_le_trans hsz hsz') /=; eexists; first reflexivity.
by rewrite/= zero_extend_idem.
Qed.

Lemma mapM2_truncate_val tys vs1' vs1 vs2' :
  mapM2 ErrType truncate_val tys vs1' = ok vs1 ->
  List.Forall2 value_uincl vs1' vs2' ->
  exists2 vs2, mapM2 ErrType truncate_val tys vs2' = ok vs2 &
    List.Forall2 value_uincl vs1 vs2.
Proof.
  elim: tys vs1' vs1 vs2' => [ | t tys hrec] [|v1' vs1'] //=.
  + by move => ? ? [<-] /List_Forall2_inv_l ->; eauto.
  move=> vs1 vs2';t_xrbindP => v1 htr vs2 htrs <- /List_Forall2_inv_l [v] [vs] [->] [hv hvs].
  have [v2 -> hv2 /=]:= truncate_value_uincl hv htr.
  by have [vs2'' -> hvs2 /=] := hrec _ _ _ htrs hvs;eauto.
Qed.

Lemma value_uincl_truncate_val t v1 v2 : truncate_val t v1 = ok v2 -> value_uincl v2 v1.
Proof.
  rewrite /truncate_val;case: t; t_xrbindP => /=.
  + by move=> b /to_boolI -> <-.
  + by move=> b /to_intI -> <-.
  + by move=> n t/ to_arrI [n' [t' [-> ? -> <-]]]; split.
  move=> sz w /to_wordI [sz' [w' [? -> -> <-]]] => /=.
  by apply word_uincl_zero_ext.
Qed.

Definition val_uincl (t1 t2:stype) (v1:sem_t t1) (v2:sem_t t2) :=
  value_uincl (to_val v1) (to_val v2).

Definition pval_uincl (t1 t2:stype) (v1:psem_t t1) (v2:psem_t t2) :=
  value_uincl (pto_val v1) (pto_val v2).

Definition eval_uincl (t1 t2:stype) (v1: exec (psem_t t1)) (v2: exec (psem_t t2)) :=
  match v1, v2 with
  | Ok  v1 , Ok   v2 => pval_uincl v1 v2
  | Error ErrAddrUndef, Ok    _ => True
  | Error x, Error y => x = y
  | _      , _       => False
  end.

Definition vm_uincl (vm1 vm2:vmap) :=
  forall x, eval_uincl (vm1.[x])%vmap (vm2.[x])%vmap.

Lemma val_uincl_refl t v: @val_uincl t t v v.
Proof. by rewrite /val_uincl. Qed.
Hint Resolve val_uincl_refl.

Lemma pval_uincl_refl t v: @pval_uincl t t v v.
Proof.  by rewrite /pval_uincl. Qed.
Hint Resolve pval_uincl_refl.

Lemma eval_uincl_refl t v: @eval_uincl t t v v.
Proof. by case: v=> //= -[]. Qed.
Hint Resolve eval_uincl_refl.

Lemma eval_uincl_trans t1 t2 t3
  (v2 : exec (psem_t t2)) (v1: exec (psem_t t1)) (v3: exec (psem_t t3)) :
   eval_uincl v1 v2 -> eval_uincl v2 v3 -> eval_uincl v1 v3.
Proof.
  case: v1 => /= [v1 | ].
  + by case: v2 => //= v2; case: v3 => // v3;apply: value_uincl_trans.
  case: v2 => [v2 [] // _| ];first by case: v3.
  by move=> e1 e2 he;have <- : e2 = e1 by case: e2 he.
Qed.

Lemma vm_uincl_refl vm: @vm_uincl vm vm.
Proof. by done. Qed.
Hint Resolve vm_uincl_refl.

Lemma val_uincl_array n (a a' : WArray.array n) :
  (∀ (i : Z) (v : u8),
    0 <= i ∧ i < n →
    Mz.get (WArray.arr_data a) i = Some v → Mz.get (WArray.arr_data a') i = Some v) ->
  @val_uincl (sarr n) (sarr n) a a'.
Proof.
  by move=> H;rewrite /val_uincl /=;split => //; apply Z.le_refl.
Qed.

Lemma of_val_uincl v v' t z:
  value_uincl v v' ->
  of_val t v = ok z ->
  exists z', of_val t v' = ok z' /\ val_uincl z z'.
Proof.
  case: v v'=> [b | n | n a | sz w | tv] [b' | n' | n' a' | sz' w' | tv'] //=;
    try by move=> _ /of_val_undef_ok.
  + by move=> <- ->;eauto.
  + by move=> <- ->;eauto.
  + move=> [h1 h2]; case: t z => //= p a1.
    rewrite /WArray.cast; case: ifPn => /ZleP h // [<-].
    case: ifPn => /ZleP ?;last by lia.
    eexists;split; first by reflexivity.
    split => //=; first by apply Z.le_refl.
    by move=> ???; apply h2; lia.
  move=> /andP []hsz /eqP -> /of_val_Vword [] s2 [] ?;subst => /= -[] hle ->.
  rewrite /truncate_word (cmp_le_trans hle hsz) zero_extend_idem //.
  by eexists;split;first reflexivity.
Qed.

Lemma pof_val_uincl v v' t z:
  value_uincl v v' ->
  pof_val t v = ok z ->
  exists z', pof_val t v' = ok z' /\ pval_uincl z z'.
Proof.
  case: v v'=> [b | n | n a | sz w | tv] [b' | n' | n' a' | sz' w' | tv'] //=;
    try by move=> _ /pof_val_undef_ok.
  + by move=> <- ?;exists z.
  + by move=> <- ?;exists z.
  + move=> [h1 h2]; case: t z => //= p a1 [<-].
    eexists;split;first by reflexivity.
    split; first by apply Z.le_refl.
    move=> i v [h0i hip]; rewrite !WArray.zget_inject //; case: ifP => //= /ZltP hn.
    by case: ifPn => /ZltP hn'; [apply h2 | lia].
  move=> /andP []hsz /eqP ->;rewrite /pof_val /pval_uincl /=.
  case: t z => //= s z.
  case: (Sumbool.sumbool_of_bool (sz ≤ s)%CMP).
  + move=> e [<-].
    case: (Sumbool.sumbool_of_bool (sz' ≤ s)%CMP).
    + move=> ?; eexists;split;first reflexivity => /=.
      by rewrite /word_uincl /= hsz eqxx.
    move => /negbT hle; eexists; split; first reflexivity.
    by rewrite /word_uincl /= e zero_extend_idem // eqxx.
  move => /negbT hlt1 [<-]; eexists; split; first reflexivity.
  have hnle: (sz' <= s)%CMP = false.
  + apply negbTE; rewrite cmp_nle_lt.
    by apply: cmp_lt_le_trans hsz; rewrite -cmp_nle_lt.
  have hle := cmp_nle_le hlt1.
  by rewrite /= zero_extend_idem // (sumbool_of_boolEF hnle).
Qed.

(*
Lemma subtype_eq_vundef_type t t': subtype t t' -> vundef_type t = vundef_type t'.
Proof.
  move=> hsub.
  apply subtype_vundef_type_eq.
  apply: subtype_trans hsub;apply subtype_vundef_type.
Qed.
*)

Lemma get_var_uincl x vm1 vm2 v1:
  vm_uincl vm1 vm2 ->
  get_var vm1 x = ok v1 ->
  exists2 v2, get_var vm2 x = ok v2 & value_uincl v1 v2.
Proof.
  move=> /(_ x);rewrite /get_var=> H; apply: on_vuP => //.
  move=> z1 Heq1 <-.
  move: H;rewrite Heq1=> {Heq1}.
  case: (vm2.[x])%vmap => //= z2 Hz2.
  by exists (pto_val z2) => //;apply pval_uinclP.
Qed.

Lemma  get_vars_uincl (xs:seq var_i) vm1 vm2 vs1:
  vm_uincl vm1 vm2 ->
  mapM (fun x => get_var vm1 (v_var x)) xs = ok vs1 ->
  exists2 vs2,
    mapM (fun x => get_var vm2 (v_var x)) xs = ok vs2 & List.Forall2 value_uincl vs1 vs2.
Proof.
  move=> Hvm;elim: xs vs1 => [ | x xs Hrec] /= ?.
  + move=> [<-]; exists [::] => //; constructor.
  apply: rbindP => v1 /(get_var_uincl Hvm) [v2 -> ?].
  apply: rbindP => vs1 /Hrec [vs2 -> ?] [] <- /=; exists (v2::vs2) => //.
  by constructor.
Qed.

Lemma val_uincl_eq t (x y: sem_t t) :
  val_uincl x y →
  ~~is_sarr t ->
  y = x.
Proof.
  case: t x y => //.
  by move => sz /= x y /andP [] _ /eqP ->; rewrite zero_extend_u.
Qed.

Lemma vuincl_sem_sop2 o ve1 ve1' ve2 ve2' v1 :
  value_uincl ve1 ve1' -> value_uincl ve2 ve2' ->
  sem_sop2 o ve1 ve2 = ok v1 ->
  sem_sop2 o ve1' ve2' = ok v1.
Proof.
  move => h1 h2; rewrite /sem_sop2 /=; t_xrbindP => w1 ok_w1 w2 ok_w2 w3 ok_w3 <-.
  have {ok_w1} [z1 [-> /= hz1]] := of_val_uincl h1 ok_w1.
  have {ok_w2} [z2 [-> /= hz2]] := of_val_uincl h2 ok_w2.
  case: o w1 w2 w3 ok_w3 z1 hz1 z2 hz2 => /=
   [||[|s]|[|s]|[|s]| [|u s]|[|u s]| s|s|s|s|s|s| [|s]|[|s]| [|u s]|[|u s]|[|u s]|[|u s]
    | ve s | ve s | ve s | ve s | ve s | ve s ] /=.
  10, 12: by rewrite /mk_sem_divmod => w1 w2 w3; case: ifP => // h [<-] z1 /val_uincl_eq -> // z2 /val_uincl_eq /(_ erefl) ->; rewrite h.
  all: by move => ??? [<-] ? /val_uincl_eq -> // ? /val_uincl_eq ->.
Qed.

Lemma val_uincl_sword s (z z':sem_t (sword s)) : val_uincl z z' -> z = z'.
Proof.
  by rewrite /val_uincl /= /word_uincl cmp_le_refl zero_extend_u => /eqP.
Qed.

Lemma vuincl_sem_sop1 o ve1 ve1' v1 :
  value_uincl ve1 ve1' ->
  sem_sop1 o ve1 = ok v1 ->
  sem_sop1 o ve1' = ok v1.
Proof.
  case: o => [ sz | sz | szo szi | szo szi | | sz | [| sz] ].
  - by move => h; apply: rbindP => /= z1 /(value_uincl_int h) [??][?]; subst.
  - move => h; apply: rbindP => /= z1 /(value_uincl_word h) {h}h [?]; subst.
    by rewrite /sem_sop1 /= h.
  1-2:
    case: ve1 => // [ | [] // ] sz1 w1 /value_uinclE [sz2] [w2] [-> {ve1'}] /andP [] hle /eqP -> {w1};
    rewrite /sem_sop1 /=; t_xrbindP => /= y /truncate_wordP [hle'] -> <-;
    by rewrite /truncate_word (cmp_le_trans hle' hle) /= (zero_extend_idem _ hle').
  all:
    move => Hu;
    apply: rbindP => z Hz;
    rewrite /sem_sop1 /= => [<-].
  2, 4: by have [z' [/= -> /val_uincl_sword ->]] := of_val_uincl Hu Hz.
  all: by have [z' [/= -> ->]] := of_val_uincl Hu Hz.
Qed.

Lemma vuincl_sopn T ts o vs vs' (v: T) :
  all is_not_sarr ts ->
  List.Forall2 value_uincl vs vs' ->
  app_sopn ts o vs = ok v ->
  app_sopn ts o vs' = ok v.
Proof.
  elim: ts o vs vs' => /= [ | t ts Hrec] o [] //.
  + by move => vs' _ /List_Forall2_inv_l -> ->; eauto using List_Forall2_refl.
  move => n vs vs'' /andP [] ht hts /List_Forall2_inv_l [v'] [vs'] [->] {vs''} [hv hvs].
  case: t o ht => //= [ | | sz ] o _; apply: rbindP.
  + by move=> b /(value_uincl_bool hv) [] _ -> /= /(Hrec _ _ _ hts hvs).
  + by move=> z /(value_uincl_int hv) [] _ -> /= /(Hrec _ _ _ hts hvs).
  by move=> w /(value_uincl_word hv) -> /= /(Hrec _ _ _ hts hvs).
Qed.

Lemma vuincl_sem_opN op vs v vs' :
  sem_opN op vs = ok v →
  List.Forall2 value_uincl vs vs' →
  exists2 v' : value, sem_opN op vs' = ok v' & value_uincl v v'.
Proof.
  rewrite /sem_opN.
  apply: rbindP => q ok_q [<-{v}] hvs.
  have -> /= := vuincl_sopn _ hvs ok_q.
  + by eauto.
  case: {q ok_q} op => //.
  by move => sz n; rewrite /= all_nseq orbT.
Qed.

(*
Lemma value_uincl_vundef_type_eq v1 v2 :
  value_uincl v1 v2 ->
  vundef_type (type_of_val v1) = vundef_type (type_of_val v2).
Proof. move /value_uincl_subtype; exact: subtype_eq_vundef_type. Qed.
*)

(* We dont need this now *)
(* Lemma sem_pexpr_map_rec_uincl gd s1 vm2 es vs1:
  vm_uincl s1.(evm) vm2 →
  mapM (sem_pexpr gd s1) es = ok vs1 ->
  (∀ e : pexpr, e \in es →
   ∀ v1 : value, ∀ le : leakages_e, sem_pexpr gd s1 e = ok (v1, le) →
   exists2 v2 : value, exists2 le' : leakages_e,
   sem_pexpr gd {| emem := emem s1; evm := vm2 |} e = ok (v2, le') &
   le = le' &
   value_uincl v1 v2) →
   exists2 vs2,
     mapM (sem_pexpr gd (Estate s1.(emem) vm2)) es = ok vs2
     & List.Forall2 value_uincl (unzip1 vs1) (unzip1 vs2) /\
       unzip2 vs1 = unzip2 vs2.
Proof.
 move=> hvm; elim: es vs1.
 + move=> vs1 Hm He. case: Hm => <-. exists [::]; auto. split. constructor. auto.
 move=> e es ih vs1 /=. t_xrbindP.
 move=> [v l] ok_v vs ok_vs <-{vs1} rec.
 move: ih => /(_ _ ok_vs) [].
 + by move => e' he'; apply: rec; rewrite in_cons he' orbT.
 move => vs' ok_vs' hs.
 move: rec => /(_ e _ _ _ ok_v) [].
 + by rewrite in_cons eqxx.
 move => v' ok_v' h.
 case: ok_v' => [] le' -> -> /=.
 rewrite ok_vs' /=.
 exists ((v', le') :: vs'). auto.
 split. simpl. constructor. case hs => hs1 hs2.
 auto. case hs => hs1 hs2. auto.
 case hs => hs1 -> /=; auto.
Qed.*)

Lemma sem_pexpr_rec_uincl gd s1 vm2 es vs1:
  vm_uincl s1.(evm) vm2 →
  sem_pexprs gd s1 es = ok vs1 →
  (∀ e : pexpr, e \in es →
   ∀ v1 : value, ∀ le : leak_e, sem_pexpr gd s1 e = ok (v1, le) →
   exists2 v2 : value,
   sem_pexpr gd {| emem := emem s1; evm := vm2 |} e = ok (v2, le) &
   value_uincl v1 v2) →
   exists2 vs2,
     sem_pexprs gd (Estate s1.(emem) vm2) es = ok vs2
     & List.Forall2 value_uincl (unzip1 vs1) (unzip1 vs2)
     /\ unzip2 vs1 = unzip2 vs2.
Proof.
 move=> hvm; elim: es vs1.
 + move=> vs1 Hm He. case: Hm => <-. exists [::]; auto. split. constructor. auto.
 move=> e es ih vs1 /=. t_xrbindP.
 move=> [v l] ok_v vs ok_vs <-{vs1} rec.
 move: ih => /(_ _ ok_vs) [].
 + by move => e' he'; apply: rec; rewrite in_cons he' orbT.
 move => vs' ok_vs' hs.
 move: rec => /(_ e _ _ _ ok_v) [].
 + by rewrite in_cons eqxx.
 move => v' ok_v' h. rewrite ok_v' /=.
 rewrite ok_vs' /=.
 exists ((v', l) :: vs'). auto.
 split. simpl. constructor. case hs => hs1 hs2.
 auto. case hs => hs1 hs2. auto.
 case hs => hs1 -> /=; auto.
Qed.


(* FIXME: no need for “le'”; just use “le” *) (** FIXED **)
Lemma sem_pexpr_uincl gd s1 vm2 e v1 le:
  vm_uincl s1.(evm) vm2 →
  sem_pexpr gd s1 e = ok (v1, le) →
  exists2 v2,
  sem_pexpr gd (Estate s1.(emem) vm2) e = ok (v2, le)
  & value_uincl v1 v2.
Proof.
move=> Hu; elim: e v1 le=>//=[z|b|n|x|g|ws x p Hp|sz x p Hp|o e He|o e1 He1 e2 He2 | op es Hes | t e He e1 He1 e2 He2 ] v1 le.
  + move=> Hok. case: Hok => <- <-. exists z; auto.
  + move=> Hok; case: Hok => <- <-; exists b; auto.
  + case => <- <-; eauto.
  + t_xrbindP => y Hget. apply get_var_uincl with x (evm s1) vm2 y in Hget.
    case: Hget => [] v2 -> /= Hl /= <- <-. by exists v2. auto.
  + by eauto.
  + apply on_arr_varP => n t Htx;rewrite /on_arr_var=> /(get_var_uincl Hu) [v2 ->].
    case: v2 => //= n' t' hu.
    t_xrbindP. move => [zv zl] Hsem h0 Hi H2 Ha Hew Hl.
    move: (Hp zv zl). move=> Hsem'. move: (Hsem' Hsem).
    move=> H. case: H => [] v2 -> /= Hv.
    case: (value_uincl_int Hv Hi) => ??;subst.
    move: (WArray.uincl_get hu Ha). rewrite Hi /=. move=> -> /=.
    exists (Vword H2);auto.
  + apply: rbindP => w1;apply: rbindP => vx /(get_var_uincl Hu) [vx' ->].
    move=> /value_uincl_word H/H{H} /= -> /=.
    t_xrbindP. move=> [zv zl] Hsem h0 Hi h2 Hr Hw Hl.
    move: (Hp zv zl). move=> Hsem'. move: (Hsem' Hsem).
    move=> H. case: H => [] v2 -> /= Hv.
    move: (value_uincl_word Hv Hi). move=> -> /=. rewrite Hr /=.
    exists (Vword h2); auto.
    by rewrite -Hl. by rewrite -Hw.
  + t_xrbindP. move=> [zv zl] Hsem h0 Ho <- <-.
    move: (He zv zl). move=> Hsem'. move: (Hsem' Hsem).
    move=> H. case: H => [] v2 -> /= Hv.
    move: (vuincl_sem_sop1 Hv Ho). move=> -> /=.
    exists h0; auto. auto.
  + t_xrbindP. move=> [zv zl] Ho1 [zv' zl'] Ho2 h2 H2 <- <-.
    move: (He1 zv zl). move=> Hsem1'. move: (Hsem1' Ho1).
    move: (He2 zv' zl'). move=> Hsem2'. move: (Hsem2' Ho2).
    move=> H. case: H => [] v2 -> /= Hv.
    move=> H'. case: H' => [] v3 -> /= Hv'.
    move: (vuincl_sem_sop2 Hv' Hv H2). move=> -> /=.
    exists h2; auto. auto.
  + t_xrbindP => vs ok_vs ok_v1 Ho <- <-; rewrite -/(sem_pexprs gd _).
    move: (sem_pexpr_rec_uincl). move=> Hes'. rewrite /sem_pexprs in Hes'.
    move: (Hes' gd s1 vm2 es vs Hu ok_vs Hes). move=> [] x -> [] Hv ->.
    move: (vuincl_sem_opN Ho Hv) => /= Ho'. case: Ho' => [] v' -> Hv' /=.
    by exists v'.
  t_xrbindP. move=> [zv zl] H h0 Hb [zv1 zl1] He1' [zv2 zl2] He2' h6 Hv1 h8 Hv2 Hif <-.
  move: (He zv zl). move=> Hsem1'. move: (Hsem1' H).
  move=> Hbo. case: Hbo => [] v2 -> /= Hv.
  move: (value_uincl_bool Hv Hb) => Hb'.
  case: Hb' => <- -> /=.
  move: (He1 zv1 zl1). move=> Hsem2'. move: (Hsem2' He1').
  move=> Het. case: Het => [] v3 -> /= H3.
  move: (He2 zv2 zl2). move=> Hsem3'. move: (Hsem3' He2').
  move=> Hef. case: Hef => [] v4 -> /= H4.
  move: (truncate_value_uincl H3 Hv1).
  move=> Ht. case: Ht => [] v' -> H5.
  move: (truncate_value_uincl H4 Hv2).
  move=> Ht'. case: Ht' => [] v'' -> H6.
  rewrite Hb /=. rewrite <- Hif. case h0.
  by exists v'. by exists v''.
Qed.

(* FIXME: no need for “les'” *) (** FIXED **)
Lemma sem_pexprs_uincl gd s1 vm2 es vs1:
  vm_uincl s1.(evm) vm2 →
  sem_pexprs gd s1 es = ok vs1 →
  exists2 vs2,
  sem_pexprs gd (Estate s1.(emem) vm2) es = ok vs2
  & List.Forall2 value_uincl (unzip1 vs1) (unzip1 vs2)
  /\ unzip2 vs1 = unzip2 vs2.
Proof.
 move=> heq ok_vs.
 apply: (sem_pexpr_rec_uincl heq ok_vs) => e he.
 move=> v1 l1.
 apply: (sem_pexpr_uincl heq).
Qed.

Lemma value_uincl_is_word v v' sz u :
  value_uincl v v' →
  is_word sz v = ok u →
  is_word sz v' = ok tt.
Proof.
move => /value_uinclE; case: v => // [ sz' w | [] // sz' ].
+ by case => ? [] ? [] ->.
by case: v' => // - [].
Qed.

Lemma vuincl_exec_opn_eq o vs vs' v :
  List.Forall2 value_uincl vs vs' -> exec_sopn o vs = ok v ->
  exec_sopn o vs' = ok v.
Proof.
rewrite /exec_sopn /sopn_sem => h1; t_xrbindP => vs1 h2 h3.
by have -> /= := vuincl_sopn (tin_narr _) h1 h2;rewrite h3.
Qed.

Lemma vuincl_exec_opn o vs vs' v :
  List.Forall2 value_uincl vs vs' -> exec_sopn o vs = ok v ->
  exists v', exec_sopn o vs' = ok v' /\ List.Forall2  value_uincl v v'.
Proof. move => /vuincl_exec_opn_eq h /h {h}; eauto using List_Forall2_refl. Qed.

Lemma set_vm_uincl vm vm' x z z' :
  vm_uincl vm vm' ->
  eval_uincl z z' ->
  vm_uincl (vm.[x <- z])%vmap (vm'.[x <- z'])%vmap.
Proof.
  move=> Hvm Hz y; case( x =P y) => [<- | /eqP Hneq];by rewrite ?Fv.setP_eq ?Fv.setP_neq.
Qed.

Lemma of_val_error t v:
  of_val t v = undef_error -> exists2 t', v = Vundef t' & subtype t t'.
Proof.
case: t v => [||p|sz] [] //=.
+ by case => //; eauto.
+ by case => //; eauto.
+ by move => n a; rewrite /WArray.cast; case: ifPn.
+ by case => // ?;case:ifP => // ? _; eexists; first by reflexivity.
+ by move=> ??;rewrite /truncate_word;case:ifP.
by case => // sz'; case: ifP => // hle _; eauto.
Qed.

Lemma pof_val_error t v:
  pof_val t v = undef_error -> exists t', subtype (vundef_type t) t' /\ v = Vundef t'.
Proof.
case: t v => [||p|sz] [] //=.
+ by case => //;eauto.
+ by case => //;eauto.
+ by move => [].
case => // s _;eexists;split;last reflexivity.
by apply wsize_le_U8.
Qed.

(*
Lemma pof_val_type_of t v :
  vundef_type t = vundef_type (type_of_val v) ->
  (exists v', pof_val t v = ok v') \/ pof_val t v = undef_error.
Proof.
  case: t v => [||p1| s1] /= [b | z | s2 p2 t2 | s2 w | tv] //=;try by left;eauto.
  + by case: tv => //=;eauto.
  + by case: tv => //=;eauto.
  + by move=> [] ??;subst s2 p2;rewrite eq_dec_refl pos_dec_n_n /=;eauto.
  + by case: tv => //= s2 p2 [] ??;subst;rewrite !eqxx /=;eauto.
  by case: tv => //= s2 _;eauto.
Qed.
*)

Lemma subtype_pof_val_ok t1 t2 v v1 :
  subtype t1 t2 ->
  pof_val t1 v = ok v1 ->
  exists2 v2, pof_val t2 v = ok v2 & value_uincl (pto_val v1) (pto_val v2).
Proof.
  case: t1 v1 => /= [v1 /eqP<-|v1 /eqP<-|n v1 |s1 v1];
   try by move=> h; eexists; [apply h | done].
  + case: t2 => // p' /ZleP hle /=.
    case: v => //=; last by case.
    move=> len a [<-]; eexists;first by reflexivity.
    by split => // i v hi; rewrite !WArray.zget_inject //; lia.
  case: t2 => //= s2 hle;case: v => //=;last by case.
  move=> s' w [<-]; eexists; first reflexivity.
  case: Sumbool.sumbool_of_bool => e /=.
  + by rewrite (sumbool_of_boolET (cmp_le_trans e hle)).
  case: Sumbool.sumbool_of_bool => e' /=.
  + move: e => /negbT e.
    apply/andP; split => //; exact: cmp_nle_le.
  rewrite -(zero_extend_idem _ hle).
  exact: word_uincl_zero_ext.
Qed.

Lemma pof_val_pto_val t (v:psem_t t): pof_val t (pto_val v) = ok v.
Proof.
  case: t v => [b | z | n a | s w] //=.
  + by f_equal; rewrite /WArray.inject Z.ltb_irrefl; case: a.
  case: Sumbool.sumbool_of_bool => e.
  + f_equal;case: w e => /= ????;f_equal; apply eq_irrelevance.
  by have := pw_proof w;rewrite e.
Qed.

Lemma value_uincl_pof_val t v1 (v1' v2 : psem_t t):
  pof_val t v1 = ok v1' ->
  value_uincl v1 (pto_val v2) ->
  value_uincl (pto_val v1') (pto_val v2).
Proof.
  case: t v1' v2 => /= [||n|s] v1' v2.
  + by move=> /to_boolI ->.
  + by move=> h1 h2;have [? [<-]]:= value_uincl_int h2 h1.
  + case: v1 => //= [ len a| []//] [<-] [hlen hget].
    apply: val_uincl_array => i v hi.
    by rewrite WArray.zget_inject //; case:ZltP => // ?; apply hget; lia.
  case: v1 => //= [ s' w| [] //] [<-].
  case: Sumbool.sumbool_of_bool => //= /negbT hnle.
  have hle := cmp_nle_le hnle; apply: word_uincl_trans.
  exact: word_uincl_zero_ext.
Qed.

(*
Lemma apply_undef_pundef_addr t : apply_undef (pundef_addr t) = pundef_addr t.
Proof. by case: t. Qed.
Lemma eval_uincl_undef t (v:psem_t t) : eval_uincl (pundef_addr t) (ok v).
Proof.
  case: t v => //= p v. rewrite /pval_uincl /=; split.
  + by apply Z.le_refl.
  by move=> ??? /=; rewrite FArray.get0.
Qed.
Lemma eval_uincl_apply_undef t (v1 v2 : exec (psem_t t)):
  eval_uincl v1 v2 ->
  eval_uincl (apply_undef v1) (apply_undef v2).
Proof.
  case:v1 v2=> [v1 | []] [v2 | e2] //=; try by move=> <-.
  by move=> _; apply eval_uincl_undef.
Qed.
*)
(*
Lemma subtype_eval_uincl t t' (v:exec (psem_t t)):
  subtype (vundef_type t') t ->
  eval_uincl (pundef_addr t) v -> eval_uincl (pundef_addr t') v.
Proof.
  case: t' => /= [/eqP?|/eqP?|n|s];subst => //=; case: t v => //=.
  move=> p [] //= a /ZleP hle ?; split.
 => // ???.
  by rewrite FArray.get0.
Qed.
*)

Lemma subtype_eval_uincl_pundef t1 t2 :
  subtype t1 t2 ->
  eval_uincl (pundef_addr t1) (pundef_addr t2).
Proof.
  case: t1 => /= [/eqP?|/eqP?|n| s];subst => //=; case: t2 => //=.
  by move=> ? /ZleP ?.
Qed.

Lemma to_bool_undef v :
  to_bool v = undef_error -> v = Vundef sbool.
Proof. by case: v => //= -[]. Qed.

Lemma type_of_val_bool v : type_of_val v = sbool ->
  v = Vundef sbool \/ exists b, v = Vbool b.
Proof.
  case: v => //=; first by eauto.
  by move=> [] //=;auto.
Qed.

Lemma to_int_undef v :
  to_int v = undef_error -> v = Vundef sint.
Proof. by case: v => //= -[]. Qed.

Lemma type_of_val_int v : type_of_val v = sint ->
  v = Vundef sint \/ exists n, v = Vint n.
Proof.
  case: v => //=;first eauto.
  by move=> [] //=;auto.
Qed.

Lemma to_arr_undef p v : to_arr p v = undef_error ->
  exists p', v = Vundef (sarr p') /\ (p <= p').
Proof.
  case:v => //=.
  + by move=> ??; rewrite /WArray.cast; case: ifP.
  case => //= p'; case: ifPn => //= /ZleP hle _;eauto.
Qed.

Lemma to_parr_undef p v : to_parr p v <> undef_error.
Proof. by case:v => //= -[]. Qed.

Lemma type_of_val_arr n v : type_of_val v = sarr n ->
  (exists p, v = Vundef (sarr p)) \/ exists (a:WArray.array n), v = Varr a.
Proof.
  case: v => //=.
  + by move=> ? a [<-]; eauto.
   move=> [] //= ??;eauto.
Qed.

(*
Lemma type_uincl_arr n t :
  type_uincl (sarr n) t ->
  exists n', t = sarr n' /\ n <= n'.
Proof. by case: t=> //= n' /ZleP;eauto. Qed.
*)
Lemma to_pword_undef w v :
  to_pword w v = undef_error -> exists w', v = Vundef (sword w').
Proof. case: v => //= -[] // w' _;eauto. Qed.

Lemma compat_type_word w t : compat_type (sword w) t -> exists w', t = sword w'.
Proof. case: t => //; eauto. Qed.

Lemma type_of_val_word v wz :
  type_of_val v = sword wz ->
  exists wz',
   v = Vundef (sword wz') \/ exists (w:word wz'), v = Vword w.
Proof.
  case: v => //=;first by eauto.
  by case => //; eauto.
Qed.

Lemma pof_val_bool_undef v : pof_val sbool v = undef_error -> v = Vundef sbool.
Proof. by case: v => //= -[]. Qed.

Lemma pof_val_undef v v':
  value_uincl v v' ->
  pof_val sbool v = undef_error ->
  v' = Vundef sbool \/ exists b, v' = Vbool b.
Proof.
  by move=> hv hp;move: hp hv => /pof_val_bool_undef -> /= /eqP /type_of_val_bool.
Qed.

Lemma set_var_uincl vm1 vm1' vm2 x v v' :
  vm_uincl vm1 vm1' ->
  value_uincl v v' ->
  set_var vm1 x v = ok vm2 ->
  exists2 vm2', set_var vm1' x v' = ok vm2' & vm_uincl vm2 vm2'.
Proof.
  (move=> Hvm Hv;apply set_varP;rewrite /set_var) => [t | hb].
  + move=> /(pof_val_uincl Hv) [z' [-> ?]] <- /=.
    by exists (vm1'.[x <- ok z'])%vmap => //; apply set_vm_uincl.
  by rewrite hb;case: x hb => /= xt xn /eqP -> /(pof_val_undef Hv) [->| [b ->]] /= <-;
    (eexists;first reflexivity); apply set_vm_uincl.
Qed.

Lemma Array_set_uincl n1 n2
   (a1 a1': WArray.array n1) (a2 : WArray.array n2) wz i (v:word wz):
  @val_uincl (sarr n1) (sarr n2) a1 a2 ->
  WArray.set a1 i v = ok a1' ->
  exists2 a2', WArray.set a2 i v = ok a2' &
      @val_uincl (sarr n1) (sarr n2) a1' a2'.
Proof.
  rewrite /val_uincl /= => hu hs.
  by have [?[]]:= WArray.uincl_set hu hs; eauto.
Qed.

Lemma write_var_uincl s1 s2 vm1 v1 v2 x :
  vm_uincl (evm s1) vm1 ->
  value_uincl v1 v2 ->
  write_var x v1 s1 = ok s2 ->
  exists2 vm2 : vmap,
    write_var x v2 {| emem := emem s1; evm := vm1 |} =
    ok {| emem := emem s2; evm := vm2 |} & vm_uincl (evm s2) vm2.
Proof.
  move=> Hvm1 Hv;rewrite /write_var;t_xrbindP => vm1' Hmv1' <- /=.
  have [vm2' -> ? /=] := set_var_uincl Hvm1 Hv Hmv1';eauto.
Qed.

Lemma write_vars_uincl s1 s2 vm1 vs1 vs2 xs :
  vm_uincl (evm s1) vm1 ->
  List.Forall2 value_uincl vs1 vs2 ->
  write_vars xs vs1 s1 = ok s2 ->
  exists2 vm2 : vmap,
    write_vars xs vs2 {| emem := emem s1; evm := vm1 |} =
    ok {| emem := emem s2; evm := vm2 |} & vm_uincl (evm s2) vm2.
Proof.
  elim: xs s1 vm1 vs1 vs2 => /= [ | x xs Hrec] s1 vm1 vs1 vs2 Hvm [] //=.
  + by move=> [] <-;eauto.
  move=> {vs1 vs2} v1 v2 vs1 vs2 Hv Hvs;apply: rbindP => s1'.
  by move=> /(write_var_uincl Hvm Hv) [] vm2 -> Hvm2 /(Hrec _ _ _ _ Hvm2 Hvs).
Qed.

(*
Lemma vundef_type_nis_sword t:
  ~~ is_sword t -> vundef_type t = t.
Proof. by case: t => //. Qed.
Lemma vundef_type_is_sword t1 t2:
  vundef_type t1 = vundef_type t2 -> is_sword t1 = is_sword t2.
Proof. by case: t1;case: t2. Qed.
Lemma pof_val_type_of_val v:
  ~~ is_sword (type_of_val v) ->
  (∃ w : psem_t (type_of_val v), pof_val (type_of_val v) v = ok w) ∨
  pof_val (type_of_val v) v = undef_error.
Proof.
  case: v => [b|z|s n a|s w|s] //=;eauto.
  case: s => //=;eauto.
  by move=> ??;rewrite Z.leb_refl /=;auto.
Qed.
*)
(* Use: pof_val_undef
Lemma pof_val_uincl_error v1 v2 t:
  ~~ is_sword t ->
  pof_val t v1 = undef_error ->
  value_uincl v1 v2 ->
  (exists w:psem_t t, pof_val t v2 = ok w) \/ pof_val t v2 = undef_error.
Proof.
  move=> hw hof hu.
  by have := pof_val_undef hof hu.
*)

(*
Lemma pof_val_error_subtype t1 t2 v:
  subtype t1 t2 ->
  pof_val t1 v = undef_error ->
  pof_val t2 v = undef_error.
Proof.
  case: t1 => /=.
  + by move=> /eqP ?;subst.
  + by move=> /eqP ?;subst.
  + move=> p1;case: t2 => // p2 /ZleP hp /to_parr_undef [p3 [-> hp3]] /=.
  + by move=> ?? /eqP ?;subst.
  move=> w;case: t2 => //= w' hle.
  by rewrite /to_pword; case: v => // -[].
Qed.
*)

Lemma is_sword_subtype t1 t2 : subtype t1 t2 -> is_sword t1 = is_sword t2.
Proof.
  by case: t1 => //= [/eqP <-|/eqP <-|?|?] //;case:t2.
Qed.

(*
Lemma uincl_write_none_subtype s2 v1 v2 s s' t1 t2 :
  value_uincl v1 v2 ->
  write_none s t1 v1 = ok s' ->
  write_none s2 t2 v2 = ok s2.
Proof.
  move=> Hs Hv /write_noneP [_] H;rewrite /write_none.
  case:H.
  + move=> [u] /(subtype_pof_val_ok Hs) [v3 h1 h2].
    by have [v4 [-> _]] := pof_val_uincl Hv h1.
  move=> [] /(pof_val_error_subtype Hs) hof.
  rewrite (is_sword_subtype Hs) => hw.
  have [ [w] -> // | -> ] /=:= pof_val_uincl_error hw hof Hv.
  by rewrite (negbTE hw).
Qed.
*)

Lemma uincl_write_none s2 v1 v2 s s' t:
  value_uincl v1 v2 ->
  write_none s t v1 = ok s' ->
  write_none s2 t v2 = ok s2.
Proof.
  move=> Hv /write_noneP [_] H;rewrite /write_none.
  case: H.
  + by move=> [w1] /(pof_val_uincl Hv) [w2 [->]].
  by move=> [] H1 ?;subst t;move /(pof_val_undef Hv): H1 => [ | [b]] ->.
Qed.

Lemma write_uincl gd s1 s2 vm1 r v1 v2 lw:
  vm_uincl s1.(evm) vm1 ->
  value_uincl v1 v2 ->
  write_lval gd r v1 s1 = ok (s2, lw) ->
  exists2 vm2,
    write_lval gd r v2 (Estate (emem s1) vm1) = ok (Estate (emem s2) vm2, lw) &
    vm_uincl s2.(evm) vm2.
Proof.
 move=> Hvm1 Hv;case:r => [xi ty | x | sz x p | sz1 x p] /=.
  + t_xrbindP. move=> y H Hes Hel.
    rewrite -> Hes in H. have [-> _]:= write_noneP H.
    rewrite (uincl_write_none _ Hv H). exists vm1.
    by rewrite <- Hel => /=. auto.
  + t_xrbindP. move=> y Hw Hs Hl. rewrite -> Hs in Hw.
    move: (write_var_uincl Hvm1 Hv Hw)=> Hw'. 
    case: Hw' => x0 Hv' H'. exists x0. rewrite <- Hl.
    by rewrite -> Hv' => /=. auto.
  + t_xrbindP. move => y v Hv' Hp [zv zl] Hs1 h4 Hp' h6 Hw h8 Hm Hs Hl /=.
    case: (get_var_uincl Hvm1 Hv') => x0 -> Hvm2 /=.
    move: (value_uincl_word Hvm2 Hp) => -> /=.
    case: (sem_pexpr_uincl Hvm1 Hs1). move=> x1 Hsem' Hzv.
    rewrite Hsem' /=. rewrite /= in Hp'.
    move: (value_uincl_word Hzv Hp') => -> /=.
    move: (value_uincl_word Hv Hw) => -> /=. rewrite -> Hm => /=.
    rewrite <- Hs => /=.
    exists vm1. rewrite <- Hl => /=. done. auto.
  apply: on_arr_varP => n a Htx /(get_var_uincl Hvm1).
  rewrite /on_arr_var => -[] vx /= -> /=.
  case: vx => //= n0 t0 hu.
  t_xrbindP. move => [yv yl] Hsem h0 Hi /= h2 Hw h4 Ha h6 Hv' <- /= <- /=.
  case: (sem_pexpr_uincl Hvm1 Hsem). move=> x0 Hsem' Hl'.
  rewrite Hsem' /=.
  move: (value_uincl_int Hl' Hi) => Hii. case: Hii => <- ->.
  rewrite Hi => /=. move: (value_uincl_word Hv Hw) => -> /=.
  move: (WArray.uincl_set hu Ha) => Ha'.
  case: Ha'=> x1 H2. case H2 => -> H3 /=.
  have ht: (value_uincl (Varr h4) (Varr x1)). apply H3.
  move: (set_var_uincl Hvm1 ht Hv') => Htt.
  case: Htt => vm2 -> /= H6.
  by exists vm2.
Qed.

Lemma writes_uincl gd s1 s2 vm1 r v1 v2 lw:
  vm_uincl s1.(evm) vm1 ->
  List.Forall2 value_uincl v1 v2 ->
  write_lvals gd s1 r v1 = ok (s2, lw) ->
  exists2 vm2,
    write_lvals gd (Estate (emem s1) vm1) r v2 = ok (Estate (emem s2) vm2, lw) &
    vm_uincl s2.(evm) vm2.
Proof.
  rewrite /write_lvals.
  elim: r v1 v2 lw s1 s2 vm1 => [ | r rs Hrec] ?? lw s1 s2 vm1 Hvm1 /= [] //=.
  + move=> [] <-. move=> ->. by exists vm1.
  move=> v1 v2 vs1 vs2 Hv Hforall.
  t_xrbindP. move=> [v l] /(write_uincl Hvm1 Hv) [] vm2 -> Hvm2 [vs ls] /= Hs <- <- /=.
  move:(Hrec _ _ _ _ _ _ Hvm2 Hforall Hs). move=> Hx.
  case: Hx => vm3 Hw Hvm3. exists vm3. by rewrite Hw /=. auto.
Qed.

Lemma write_vars_lvals gd xs vs s1 v l:
  write_lvals gd s1 [seq Lvar i | i <- xs] vs = ok (v, l) ->
  write_vars xs vs s1 = ok v.
Proof.
  rewrite /write_vars /write_lvals.
  elim: xs vs s1 l => [ | x xs Hrec] [ | v' vs] //= s1.
  + move=> l He. by case: He => -> _.
  t_xrbindP. move=> ls [sy ly] s' Hw <- [s'' l'] /= He Hvs Hls /=.
  rewrite Hw /=. rewrite Hvs in He. by move: (Hrec _ _ _ He) => Hr.
Qed.

Lemma sem_pexprs_map_get_var gd s xs vs:
 mapM (sem_pexpr gd s) [seq Pvar i | i <- xs] = ok vs ->
 mapM (fun x : var_i => get_var (evm s) x) xs = ok (map fst vs).
Proof.
elim: xs vs.
 + move=> vs. move=> Hm. case: Hm => <- /=. auto.
 + move=> a l Hm /=. t_xrbindP.
   move=> h y h0 Hg <- /= h3 Hms <- /=.
   rewrite Hms in Hm. move: (Hm h3 erefl).
   rewrite Hg /=.
   by move=> -> /=.
Qed.

Fixpoint map_v_el (s : seq value) : seq (value * leak_e) := 
  match s with 
   | [::] => [::]
   | [:: x & xs] => [:: (x, LEmpty) & map_v_el xs]
end.

Lemma sem_pexprs_get_var_map gd s xs vs:
 mapM (fun x : var_i => get_var (evm s) x) xs = ok vs ->
 mapM (sem_pexpr gd s) [seq Pvar i | i <- xs] = ok (map_v_el vs).
Proof.
elim: xs vs.
 + move=> vs. move=> Hm. case: Hm => <- /=. auto.
 + move=> a l Hm /=. t_xrbindP.
   move=> h y -> /= h1 Hm' <-. rewrite Hm' in Hm.
   by move: (Hm h1 erefl) => -> /=.
Qed.

Lemma sem_pexprs_get_var gd s xs vs:
  sem_pexprs gd s [seq Pvar i | i <- xs] = ok vs ->
  mapM (fun x : var_i => get_var (evm s) x) xs = ok (unzip1 vs).
Proof.
  rewrite /sem_pexprs. t_xrbindP.
  move=> Hm. by move: (sem_pexprs_map_get_var Hm) => -> /=.
Qed.

Lemma write_lvals_vars gd xs vs s1 v:  
  write_vars xs vs s1 = ok v ->
  exists l, write_lvals gd s1 (map Lvar xs) vs = ok (v, l).
Proof.
  rewrite /write_lvals. rewrite /write_vars.
  elim: xs vs s1 => [ | x xs Hrec] [ | v' vs] //= s1.
  + move=> [] <-. by exists [::].
  t_xrbindP. move=> s1' -> /= Hw. move: (Hrec vs s1' Hw).
  move=> [] l' Hw'. exists (LEmpty :: l'). by rewrite Hw' /=.
Qed.

Lemma write_lvals_vars' gd xs vs s1 v:  
  write_vars xs vs s1 = ok v ->
  write_lvals gd s1 (map Lvar xs) vs = ok (v, (map (fun x => LEmpty) xs)).
Proof.
  rewrite /write_lvals. rewrite /write_vars.
  elim: xs vs s1 => [ | x xs Hrec] [ | v' vs] //= s1.
  + by move=> [] <-.
  t_xrbindP. move=> s1' -> /= Hw. move: (Hrec vs s1' Hw).
  move=> Hw'. by rewrite Hw' /=.
Qed.

Lemma get_var_sem_pexprs gd s xs vs:
  mapM (λ x : var_i, get_var (evm s) x) xs = ok vs ->
  exists vs', sem_pexprs gd s [seq Pvar i | i <- xs] = ok vs'.
Proof.
 rewrite /sem_pexprs. elim: xs vs.
 + move=> vs Hm /=. by exists [::].
 move=> a l Hm /=. t_xrbindP.
 move=> vs v Hg vs' Hm' Hv. rewrite Hg /=. move: (Hm vs' Hm').
 move=> [] vsl -> /=. by exists ((v, LEmpty) :: vsl).
Qed.

Lemma get_var_sem_pexprs_empty gd s xs vs:
  mapM (λ x : var_i, get_var (evm s) x) xs = ok vs ->
  sem_pexprs gd s [seq Pvar i | i <- xs] = ok (zip vs (map (fun x => LEmpty) vs)).
Proof.
 rewrite /sem_pexprs. elim: xs vs.
 + move=> vs /= Hm /=. by case: Hm=> <-.
 move=> a l /= Hm /=. t_xrbindP.
 move=> vs v Hg vs' Hm' Hv. rewrite Hg /=. move: (Hm vs' Hm').
 move=> -> /=. by rewrite -Hv /=.
Qed.

Section UNDEFINCL.

Variable (p:prog).
Notation gd:= (p_globs p).

Let Pc s1 c lc s2 :=
  forall vm1,
    vm_uincl (evm s1) vm1 ->
    exists vm2, 
      sem p {|emem := emem s1; evm := vm1|} c lc {|emem := emem s2; evm := vm2|} /\
      vm_uincl (evm s2) vm2.

Let Pi_r s1 i li s2 :=
  forall vm1,
    vm_uincl (evm s1) vm1 ->
    exists vm2,
      sem_i p {|emem := emem s1; evm := vm1|} i li {|emem := emem s2; evm := vm2|} /\
      vm_uincl (evm s2) vm2.

Let Pi s1 i li s2 :=
  forall vm1 ,
    vm_uincl (evm s1) vm1 ->
    exists vm2, 
      sem_I p {|emem := emem s1; evm := vm1|} i li {|emem := emem s2; evm := vm2|} /\
      vm_uincl (evm s2) vm2.

Let Pfor (i:var_i) zs s1 c lc s2 :=
  forall vm1,
    vm_uincl (evm s1) vm1 ->
    exists vm2, 
      sem_for p i zs {|emem := emem s1; evm := vm1|} c lc {|emem := emem s2; evm := vm2|} /\
      vm_uincl (evm s2) vm2.

Let Pfun m1 fd vargs lf m2 vres :=
  forall vargs',
    List.Forall2 value_uincl vargs vargs' ->
    exists vres', 
      sem_call p m1 fd vargs' lf m2 vres' /\
      List.Forall2 value_uincl vres vres'.

Local Lemma Hnil : sem_Ind_nil Pc.
Proof. move=> s vm1 Hvm1. exists vm1. split. constructor. auto. Qed. 

Local Lemma Hcons : sem_Ind_cons p Pc Pi.
Proof.
  move=> s1 s2 s3 i c li lc _ Hi _ Hc vm1 /Hi [vm2 []] Hsi /Hc [vm3 []] Hsc ?.
  by exists vm3;split=>//;econstructor;eauto.
Qed.

Local Lemma HmkI : sem_Ind_mkI p Pi_r Pi.
Proof. by move=> ii i s1 s2 li _ Hi vm1 /Hi [vm2 []] Hsi ?;exists vm2. Qed.

Local Lemma Hasgn : sem_Ind_assgn p Pi_r.
Proof.
  move=> s1 s2 x tag ty e v v' le lw hsem hty hwr vm1 Hvm1.
  have [w hsem' hle]:= sem_pexpr_uincl Hvm1 hsem.
  have [w'' hty' hle'] := truncate_value_uincl hle hty.
  have  [vm2 Hw ?]:= write_uincl Hvm1 hle' hwr; exists vm2 ;split=> //.
  by econstructor;first exact hsem'; eauto.
Qed.

Local Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
  move=> s1 s2 t o xs es lo H vm1 Hvm1; apply: rbindP H.
  move => vs Hsem.
  move: (sem_pexprs_uincl Hvm1 Hsem) => [] vs' H1 [] H2 H3.
  t_xrbindP => y Hon [v' l'] Hw /= He <-.
  move: (vuincl_exec_opn H2 Hon) => [] x Hop. case: Hop=> Hop H3'.
  move: (writes_uincl Hvm1 H3' Hw) => [] vm2 Hws Hvms.
  exists vm2. split => //. constructor.
  rewrite /sem_sopn. rewrite H1 /= Hop /= Hws /=.
  rewrite /= in He.
  by rewrite -He -H3. rewrite -He. auto.
Qed.

Local Lemma Hif_true : sem_Ind_if_true p Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 le lc H _ Hc vm1 Hvm1.
  have [v' H1 /value_uincl_bool1 ?]:= sem_pexpr_uincl Hvm1 H;subst v'.
  have [vm2 [??]]:= Hc _ Hvm1;exists vm2;split=>//.
  apply Eif_true. rewrite // Hsem. auto.
Qed.

Local Lemma Hif_false : sem_Ind_if_false p Pc Pi_r.
Proof.
  move=> s1 s2 e c1 c2 le lc H _ Hc vm1 Hvm1.
  have [v' H1 /value_uincl_bool1 ?]:= sem_pexpr_uincl Hvm1 H;subst v'.
  have [vm2 [??]]:= Hc _ Hvm1;exists vm2;split=>//.
  apply Eif_false. rewrite // Hsem. auto.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true p Pc Pi_r.
Proof.
  move=> s1 s2 s3 s4 a c e c' lc le lc' li _ Hc H _ Hc' _ Hw vm1 Hvm1.
  have [vm2 [Hs2 Hvm2]] := Hc _ Hvm1.
  have [v' H1 /value_uincl_bool1 ?]:= sem_pexpr_uincl Hvm2 H;subst.
  have [vm3 [H4 /Hw [vm4] [??]]]:= Hc' _ Hvm2;exists vm4;split => //.
  eapply Ewhile_true; eauto.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false p Pc Pi_r.
Proof.
  move=> s1 s2 a c e c' lc le _ Hc H vm1 Hvm1.
  have [vm2 [Hs2 Hvm2]] := Hc _ Hvm1.
  have [v' H1 /value_uincl_bool1 ?]:= sem_pexpr_uincl Hvm2 H;subst.
  exists vm2; split => //; apply Ewhile_false => //.
Qed.

Lemma sem_range_uincl s1 vm2 r v1 le:
  vm_uincl s1.(evm) vm2 →
  sem_range p s1 r = ok (v1, le) →
  sem_range p (Estate s1.(emem) vm2) r = ok (v1, le).
Proof.
 move=> Hvm; elim: r v1 le.
 move=> [d p1] p2 v1 le /=.
 t_xrbindP. 
 move=> [v l] Hp h0 Hi [v' l'] Hp' h4 Hi' Hw Hle.
 move: (sem_pexpr_uincl Hvm Hp) => [] v3 Hpsem Hv2.
 move: (sem_pexpr_uincl Hvm Hp') => [] v4 Hpsem' Hv3.
 rewrite Hpsem Hpsem' /=.
 move: (value_uincl_int Hv2 Hi) => Hvi.
 case: Hvi => Hv ->. rewrite Hv in Hi. rewrite Hi /=.
 move: (value_uincl_int Hv3 Hi') => Hvi'.
 case: Hvi' => Hv' ->. rewrite Hv' in Hi'. rewrite Hi' /=.
 by rewrite Hw -Hle /=.
Qed.

Local Lemma Hfor : sem_Ind_for p Pi_r Pfor.
Proof.
  move=> s1 s2 i r wr c lr lf H' _ Hfor vm1 Hvm1.
  have [vm2 []??]:= Hfor _ Hvm1; exists vm2;split=>//.
  econstructor; eauto.
  by move: (sem_range_uincl Hvm1 H') => H.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof. by move=> s i c vm1 Hvm1;exists vm1;split=> //;constructor. Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons p Pc Pfor.
Proof.
  move=> s1 s1' s2 s3 i w ws c lc lf Hi _ Hc _ Hf vm1 Hvm1.
  have [vm1' Hi' /Hc] := write_var_uincl Hvm1 (value_uincl_refl _) Hi.
  move=> [vm2 [Hsc /Hf]] [vm3 [Hsf Hvm3]];exists vm3;split => //.
  by econstructor;eauto.
Qed.

Local Lemma Hcall : sem_Ind_call p Pi_r Pfun.
Proof.
  move=> s1 m2 s2 ii xs fn args vargs vs lf lw Hargs Hcall Hfd Hxs vm1 Hvm1.
  move: (sem_pexprs_uincl). move=>  Hargs'.
  move: (Hargs' gd s1 vm1 args vargs Hvm1 Hargs).
  move=> [] vargs' Hes [] Hv Hl {Hargs'}.
  have Hvm1' : vm_uincl (evm {| emem := m2; evm := evm s1 |}) vm1 by done.
  rewrite /Pfun in Hfd. move: (Hfd (unzip1 vargs') Hv).
  move=> [] vs' [] Hfd' Hv' {Hfd}.
  move: (writes_uincl). move=> Hxs'.
  move: (Hxs' gd {| emem := m2; evm := evm s1 |} s2 vm1 xs vs vs' lw Hvm1 Hv' Hxs).
  move=> [] vm2 {Hxs'} /= Hxs' Hvm2'.
  exists vm2;split=>//. rewrite Hl /=.
  econstructor; eauto.
Qed.

Lemma check_ty_val_uincl v1 x v2 :
  check_ty_val x v1 → value_uincl v1 v2 → check_ty_val x v2.
Proof.
  rewrite /check_ty_val => h /value_uincl_subtype.
  by apply: subtype_trans.
Qed.

Lemma all2_check_ty_val v1 x v2 :
  all2 check_ty_val x v1 → List.Forall2 value_uincl v1 v2 → all2 check_ty_val x v2.
Proof.
  move=> /all2P H1 H2;apply /all2P;apply: Forall2_trans H1 H2;apply check_ty_val_uincl.
Qed.

Local Lemma Hproc : sem_Ind_proc p Pc Pfun.
Proof.
  move=> m1 m2 fn fd vargs vargs' s1 vm2 vres vres' lc Hget Hca Hargs Hsem Hrec Hmap Hcr vargs1' Uargs.
  have [vargs2' hm2 Uargs']:= mapM2_truncate_val Hca Uargs.
  have [vm1 Hargs' Hvm1] := write_vars_uincl (vm_uincl_refl _) Uargs' Hargs.
  have [vm2' /= [] Hsem' Uvm2]:= Hrec _ Hvm1.
  have [vs2 Hvs2 Hsub] := get_vars_uincl Uvm2 Hmap.
  have [vres2' hmr2 Ures']:= mapM2_truncate_val Hcr Hsub.
  by exists vres2';split=>//;econstructor;eauto.
Qed.

Lemma sem_call_uincl vargs m1 f lf m2 vres vargs':
  List.Forall2 value_uincl vargs vargs' ->
  sem_call p m1 f vargs lf m2 vres ->
  exists vres', sem_call p m1 f vargs' lf m2 vres' /\ List.Forall2 value_uincl vres vres'.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_i_uincl s1 i li s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem_i p s1 i li s2 ->
  exists vm2,
    sem_i p {|emem := emem s1; evm := vm1|} i li {|emem := emem s2; evm := vm2|} /\
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_i_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_I_uincl s1 i li s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem_I p s1 i li s2 ->
  exists vm2,
    sem_I p {|emem := emem s1; evm := vm1|} i li {|emem := emem s2; evm := vm2|} /\
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_I_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

Lemma sem_uincl s1 c lc s2 vm1 :
  vm_uincl (evm s1) vm1 ->
  sem p s1 c lc s2 ->
  exists vm2,
    sem p {|emem := emem s1; evm := vm1|} c lc {|emem := emem s2; evm := vm2|} /\
    vm_uincl (evm s2) vm2.
Proof.
  move=> H1 H2.
  by apply:
    (@sem_Ind p Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn
        Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc) H1.
Qed.

End UNDEFINCL.

Lemma eq_expr_map_recP gd s (es es': pexprs) :
  (∀ e : pexpr, e \in es →
   ∀ e' : pexpr, eq_expr e e' → sem_pexpr gd s e = sem_pexpr gd s e') →
  all2 eq_expr es es' →
  mapM (sem_pexpr gd s) es = mapM (sem_pexpr gd s) es'.
Proof.
  elim: es es'; first by case.
  move => e es ih [] //= e' es' rec /andP [] he hes.
  rewrite (rec e _ e' he); last by rewrite in_cons eqxx.
  case: (sem_pexpr _ _ e') => //= v.
  rewrite (ih es') // => q hq q' hq'.
  by apply: rec => //; rewrite in_cons hq orbT.
Qed.

Lemma eq_expr_recP gd s (es es': pexprs) :
  (∀ e : pexpr, e \in es →
   ∀ e' : pexpr, eq_expr e e' → sem_pexpr gd s e = sem_pexpr gd s e') →
  all2 eq_expr es es' →
  sem_pexprs gd s es = sem_pexprs gd s es'.
Proof.
  rewrite /sem_pexprs /=.
  move=> ih hf.
  by rewrite (eq_expr_map_recP ih hf).
Qed.

Lemma eq_exprP gd s e1 e2 : eq_expr e1 e2 -> sem_pexpr gd s e1 = sem_pexpr gd s e2.
Proof.
  elim: e1 e2=> [z  | b | n | x | g | sz x e He | sz x e He | o e  He | o e1 He1 e2 He2 | o es Hes | t e He e1 He1 e2 He2]
                [z' | b' | n' | x' | g' | sz' x' e'  | sz' x' e'  | o' e' | o' e1' e2' | o' es' | t' e' e1' e2'] //=.
  + by move=> /eqP ->.   + by move=> /eqP ->.
  + by move=> /eqP ->.   + by move=> /eqP ->.  + by move=> /eqP ->.
  + by move=> /andP []/andP [] /eqP -> /eqP -> /He ->.
  + by case/andP => /andP [] /eqP -> /eqP -> /He ->.
  + by move=> /andP[]/eqP -> /He ->.
  + by move=> /andP[]/andP[] /eqP -> /He1 -> /He2 ->.
  + case/andP => /eqP <-. move=> Hf.
    by rewrite (eq_expr_map_recP Hes Hf).
  by move=> /andP[]/andP[]/andP[] /eqP -> /He -> /He1 -> /He2 ->.
Qed.

Lemma eq_exprsP gd m es1 es2:
  all2 eq_expr es1 es2 → sem_pexprs gd m es1 = sem_pexprs gd m es2.
Proof.
  apply: eq_expr_recP => e _ e'; exact: eq_exprP.
Qed.

Lemma eq_lvalP gd m lv lv' v :
  eq_lval lv lv' ->
  write_lval gd lv v m = write_lval gd lv' v m.
Proof.
  case: lv lv'=> [ ?? | [??] | sz [??] e | sz [??] e] [ ?? | [??] | sz' [??] e' | sz' [??] e'] //=.
  + by move=> /eqP ->.
  + by move=> /eqP ->.
  + by case/andP => /andP [] /eqP -> /eqP -> /eq_exprP ->.
  by move=> /andP [] /andP [] /eqP -> /eqP -> /eq_exprP ->.
Qed.

Lemma eq_lvalsP gd m ls1 ls2 vs:
  all2 eq_lval ls1 ls2 → write_lvals gd m ls1 vs =  write_lvals gd m ls2 vs.
Proof.
 elim: ls1 ls2 vs m => [ | l1 ls1 Hrec] [ | l2 ls2] //= [] // v vs m.
 move=> /andP [] /eq_lvalP -> /Hrec; case: write_lval => /=.
 move=> a Ha. move: (Ha vs a.1). move=>H. by rewrite H.
 move=> e. by move=> H.
Qed.

Lemma to_val_inj t (v1 v2:sem_t t) : to_val v1 = to_val v2 -> v1 = v2.
Proof.
  by case: t v1 v2 => //= [ | | p | sz ] v1 v2 => [ []|[] |/Varr_inj1 |[] ] ->.
Qed.

Lemma pto_val_inj t (v1 v2:psem_t t) : pto_val v1 = pto_val v2 -> v1 = v2.
Proof.
  case: t v1 v2 => //= [ | | p | sz ] v1 v2 => [ []|[] | /Varr_inj1 | ] //.
  case: v1 v2 => sz1 w1 p1 [sz2 w2 p2] /=.
  move=> /Vword_inj [e];subst => /= <-.
  by rewrite (@eq_irrelevance _ _ _ p1 p2).
Qed.

Lemma to_val_undef  t (v:sem_t t) : to_val v <> Vundef t.
Proof. by case: t v. Qed.

Lemma pto_val_undef  t (v:psem_t t) : pto_val v <> Vundef t.
Proof. by case: t v. Qed.

(* TODO: move *)
Lemma to_word_to_pword s v w: to_word s v = ok w -> to_pword s v = ok (pword_of_word w).
Proof.
  case: v => //= [ s' w' | [] // ].
  move=> /truncate_wordP [hle] ?; subst w; f_equal.
  case: Sumbool.sumbool_of_bool => //=.
  move=> e;move: (e);rewrite cmp_le_eq_lt in e => e'.
  case /orP: e => [hlt | /eqP ?];first by rewrite -cmp_nlt_le hlt in hle.
  by subst; rewrite /pword_of_word zero_extend_u;do 2 f_equal;apply eq_irrelevance.
Qed.

(* ------------------------------------------------------------------------------ *)
Definition apply_undef t (v : exec (psem_t t)) :=
  match v with
  | Error ErrAddrUndef => pundef_addr t
  | _                  => v
  end.

Lemma eval_uincl_undef t1 t2 (v:psem_t t2) :
  subtype t1 t2 ->
  eval_uincl (pundef_addr t1) (ok v).
Proof. by case: t1 => //= p; case: t2 v => //= p2 a /ZleP. Qed.

Lemma apply_undef_pundef_addr t : apply_undef (pundef_addr t) = pundef_addr t.
Proof. by case: t. Qed.

Lemma eval_uincl_apply_undef t (v1 v2 : exec (psem_t t)):
  eval_uincl v1 v2 ->
  eval_uincl (apply_undef v1) (apply_undef v2).
Proof.
  case:v1 v2=> [v1 | []] [v2 | e2] //=; try by move=> <-.
  by move=> _; apply eval_uincl_undef.
Qed.

(* ------------------------------------------------------------------------------ *)

Section WF.

Local Open Scope vmap.

  Definition wf_vm (vm:vmap) :=
    forall x,
      match vm.[x], vtype x with
      | Ok _   , _      => True
      | Error ErrAddrUndef, sarr _ => False
      | Error ErrAddrUndef, _ => True
      | _, _ => false
      end.

  Lemma wf_set_var x ve vm1 vm2 :
    wf_vm vm1 -> set_var vm1 x ve = ok vm2 -> wf_vm vm2.
  Proof.
    move=> Hwf;apply: set_varP => [v | _ ] ? <- /= z.
    + case: (x =P z) => [ <- | /eqP Hne];first by rewrite Fv.setP_eq.
      by rewrite Fv.setP_neq //;apply (Hwf z).
    case: (x =P z) => [ <- | /eqP Hne].
    + by rewrite Fv.setP_eq; case (vtype x).
    by rewrite Fv.setP_neq //;apply (Hwf z).
  Qed.

  Lemma wf_write_var x ve s1 s2 :
    wf_vm (evm s1) -> write_var x ve s1 = ok s2 -> wf_vm (evm s2).
  Proof.
    by move=> HWf; apply: rbindP => vm Hset [<-] /=;apply: wf_set_var Hset.
  Qed.

  Lemma wf_write_vars x ve s1 s2 :
    wf_vm (evm s1) -> write_vars x ve s1 = ok s2 -> wf_vm (evm s2).
  Proof.
    elim: x ve s1 s2=> [ | x xs Hrec] [ | e es] //= s1 s2.
    + by move=> ? [<-].
    by move=> Hwf; apply: rbindP => vm /(wf_write_var Hwf) -/Hrec H/H.
  Qed.

  Lemma wf_write_lval gd x ve s1 s2 l :
    wf_vm (evm s1) -> write_lval gd x ve s1 = ok (s2, l) -> wf_vm (evm s2).
  Proof.
    case: x => [vi t|v|sz v e|sz v e] /= Hwf.
    + t_xrbindP => y /write_noneP H <- Hl. by case: H => -> _.
    + t_xrbindP => y /wf_write_var H1 <- Hl. by apply H1.
    + by t_rbindP => -[<-].
    apply: on_arr_varP => n t ? ?.
    t_xrbindP => y H h0 Hi h2 Hw h4 Ha h6 /wf_set_var Hs <- /= Hl.
    by apply Hs.
  Qed.

  Lemma wf_write_lvals gd xs vs s1 s2 l:
    wf_vm (evm s1) -> write_lvals gd s1 xs vs = ok (s2, l) -> wf_vm (evm s2).
  Proof.
    rewrite /write_lvals.
    elim: xs vs s1 l => [ | x xs Hrec] [ | v vs] s1 l //= Hwf => [[<-]//| ].
    t_xrbindP => -[y h] Hw. move: (wf_write_lval Hwf Hw) => Hy /= [vs' ls'] Hp /= Hs /= Hf /=. rewrite Hs in Hp.
    move: (Hrec vs y ls' Hy) => Hf'. move: (Hf' Hp) => H. auto.
  Qed.

  Lemma wf_sem p s1 c lc s2 :
    sem p s1 c lc s2 -> wf_vm (evm s1) -> wf_vm (evm s2).
  Proof.
    apply (@cmd_rect
             (fun i => forall s1 li s2, sem_i p s1 i li s2 -> wf_vm (evm s1) -> wf_vm (evm s2))
             (fun i => forall s1 li s2, sem_I p s1 i li s2 -> wf_vm (evm s1) -> wf_vm (evm s2))
             (fun c => forall s1 lc s2, sem   p s1 c lc s2 -> wf_vm (evm s1) -> wf_vm (evm s2)))=>
      {s1 s2 c}.
    + by move=> i ii Hrec s1 li s2 /sem_IE; apply: Hrec.
    + by move => s1 lc0 s2 /semE [-> Hl] Hw.
    + move=> i c Hi Hc s1 lc0 s2 /semE [si] [li] [lc0'] [] /Hi {Hi} Hi Hs Hl /Hi.
      by move: (Hc si lc0' s2 Hs) => H3.
    + move=> x t ty e s1 li s2 /sem_iE [v] [v'] [le] [lw] [hv hv' ok_s2] hw.
      by apply: wf_write_lval ok_s2.
    + move=> xs t o es s1 li s2 /sem_iE.
      t_xrbindP => Ho. case Ho. rewrite /sem_sopn. t_xrbindP.
      by move=> h yvs Hes h1 Hs [hv hl] /wf_write_lvals hvm <- Hl' /=.
    + move=> e c1 c2 Hc1 Hc2 s1 lc0 s2 /sem_iE [b] [le] [lc1]. case: b => Hp. case Hp => Hp1 Hp2.
      by move: (Hc1 s1 lc1 s2 Hp2) => H. case Hp => Hp1 Hp2.
      by move: (Hc2 s1 lc1 s2 Hp2) => H.
    + move=> i dir lo hi c Hc s1 lc0 s2 /sem_iE [wr] [lr] [lf] [hr hfor].
      elim: hfor Hc => // s0 s1' s3 s4 io w ws c0 lc1 lw Hw Hsc Hsf Hrec Hc.
      by move=> /wf_write_var -/(_ _ _ _ Hw) -/(Hc _ _ _ Hsc) ;apply: Hrec Hc.
    + move=> a c e c' Hc Hc' s1 lc0 s2 H.
      move: {1 2}(Cwhile a c e c') H (refl_equal (Cwhile a c e c'))=> i;elim=> //=.
      move=> ???????????? Hsc ? Hsc' Hsw Hrec [????];subst.
      move=> /(Hc _ _ _ Hsc).
      by move=> /(Hc' _ _ _ Hsc'); apply Hrec.
    + move=> ???????? Hsc ? [????];subst.
      exact: (Hc _ _ _ Hsc).
    move=> i xs f es s1 li s2 /sem_iE [vs] [m2] [rs] [lf] [l2] [_ _ ok_s2] hw.
    by apply: wf_write_lvals ok_s2.
  Qed.

  Lemma wf_vm_uincl vm : wf_vm vm -> vm_uincl vmap0 vm.
  Proof.
    move=> Hwf x;have := Hwf x;rewrite /vmap0 Fv.get0.
    case: vm.[x] => [a _ | ];first by apply eval_uincl_undef.
    move=> [] //=;case:(vtype x) => //=.

  Qed.

  Lemma wf_vmap0 : wf_vm vmap0.
  Proof. by move=> x;rewrite /vmap0 Fv.get0;case:vtype. Qed.

End WF.
