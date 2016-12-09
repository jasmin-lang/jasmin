(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import strings word dmasm_utils dmasm_type dmasm_var.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Operators
 * -------------------------------------------------------------------- *)
(* *** Summary
   Operators represent several constructs in the Ocaml compiler:
   - const-op: compile-time expressions (constexpr in C++)
   - list-op: argument and result lists
   - arr-op: reading and writing arrays
   - cpu-op: CPU instructions such as addition with carry
*)

Inductive sop2 : Set :=
| Oand  : sop2                      (* const : sbool -> sbool -> sbool *)
| Oor   : sop2                      (* const : sbool -> sbool -> sbool *)

| Oadd  : sop2                      (* const : sint -> sint -> sint *)
| Omul  : sop2                      (* const : sint -> sint -> sint *)
| Osub  : sop2                      (* const : sint -> sint -> sint *)

| Oeq   : sop2                      (* const : sint -> sint -> sbool *)
| Oneq  : sop2                      (* const : sint -> sint -> sbool *)
| Olt   : sop2                      (* const : sint -> sint -> sbool *)
| Ole   : sop2                      (* const : sint -> sint -> sbool *)
| Ogt   : sop2                      (* const : sint -> sint -> sbool *)
| Oge   : sop2.                     (* const : sint -> sint -> sbool *)

Inductive sopn : Set :=
| Olnot : sopn                      (* cpu : sword -> sword *) 

| Oxor  : sopn                      (* cpu   : sword -> sword -> sword *)
| Oland : sopn                      (* cpu   : sword -> sword -> sword *)
| Olor  : sopn                      (* cpu   : sword -> sword -> sword *)
| Olsr  : sopn                      (* cpu   : sword -> sword -> sword *)
| Olsl  : sopn                      (* cpu   : sword -> sword -> sword *)

| Oif   : sopn                      (* cpu  : sbool -> sword -> sword -> sword *)

| Omulu     : sopn                  (* cpu   : [sword; sword]        -> [sword;sword] *)
| Omuli     : sopn                  (* cpu   : [sword; sword]        -> [sword]       *)
| Oaddcarry : sopn                  (* cpu   : [sword; sword; sbool] -> [sbool;sword] *)
| Osubcarry : sopn.                 (* cpu   : [sword; sword; sbool] -> [sbool;sword] *) 

Scheme Equality for sop2.
(* Definition sop2_beq : sop2 -> sop2 -> bool *)

Lemma sop2_eq_axiom : Equality.axiom sop2_beq. 
Proof. 
  move=> x y;apply:(iffP idP).
  + by apply: internal_sop2_dec_bl.
  by apply: internal_sop2_dec_lb.
Qed.

Definition sop2_eqMixin     := Equality.Mixin sop2_eq_axiom.
Canonical  sop2_eqType      := Eval hnf in EqType sop2 sop2_eqMixin.

Scheme Equality for sopn.
(* Definition sopn_beq : sopn -> sopn -> bool *)
Lemma sopn_eq_axiom : Equality.axiom sopn_beq. 
Proof. 
  move=> x y;apply:(iffP idP).
  + by apply: internal_sopn_dec_bl.
  by apply: internal_sopn_dec_lb.
Qed.

Definition sopn_eqMixin     := Equality.Mixin sopn_eq_axiom.
Canonical  sopn_eqType      := Eval hnf in EqType sopn sopn_eqMixin.

(* ** Expressions
 * -------------------------------------------------------------------- *)
(* Used only by the ocaml compiler *)
Definition var_info := positive.

Record var_i := VarI {
  v_var :> var;
  v_info : var_info 
}.

Inductive pexpr : Type :=
| Pconst :> Z -> pexpr
| Pbool  :> bool -> pexpr
| Pcast  : pexpr -> pexpr              (* int -> word *)
| Pvar   : var_i -> pexpr
| Pget   : var_i -> pexpr -> pexpr 
| Pload  : var_i -> pexpr -> pexpr 
| Pnot   : pexpr -> pexpr 
| Papp2  : sop2 -> pexpr -> pexpr -> pexpr.

Notation pexprs := (seq pexpr).

Definition var_i_beq x1 x2 := 
  match x1, x2 with
  | VarI x1 i1, VarI x2 i2 => (x1 == x2) && (i1 == i2)
  end.

Lemma var_i_eq_axiom : Equality.axiom var_i_beq. 
Proof. 
Admitted.

Definition var_i_eqMixin     := Equality.Mixin var_i_eq_axiom.
Canonical  var_i_eqType      := Eval hnf in EqType var_i var_i_eqMixin.

Module Eq_pexpr.
Fixpoint eqb (e1 e2:pexpr) : bool :=
  match e1, e2 with
  | Pconst n1   , Pconst n2    => n1 == n2 
  | Pbool  b1   , Pbool  b2    => b1 == b2
  | Pcast  e1   , Pcast  e2    => eqb e1 e2
  | Pvar   x1   , Pvar   x2    => (x1 == x2)
  | Pget   x1 e1, Pget   x2 e2 => (x1 == x2) && eqb e1 e2
  | Pload  x1 e1, Pload  x2 e2 => (x1 == x2) && eqb e1 e2 
  | Pnot   e1   , Pnot   e2    => eqb e1 e2 
  | Papp2 o1 e11 e12, Papp2 o2 e21 e22  =>  
     (o1 == o2) && eqb e11 e21 && eqb e12 e22
  | _, _ => false
  end.


  Lemma eq_axiom : Equality.axiom eqb. 
  Proof. 
  Admitted.     

  Definition eqMixin := Equality.Mixin eq_axiom.
  Module Exports.
  Canonical eqType  := Eval hnf in EqType pexpr eqMixin.
  End Exports.
End Eq_pexpr.
Import Eq_pexpr.Exports.

(* ** Right values
 * -------------------------------------------------------------------- *)

Inductive rval : Type :=
| Rnone : var_info -> rval
| Rvar  : var_i -> rval
| Rmem  : var_i -> pexpr -> rval
| Raset : var_i -> pexpr -> rval.

Notation rvals := (seq rval).

Definition rval_beq (x1:rval) (x2:rval) :=
  match x1, x2 with
  | Rnone i1   , Rnone i2    => i1 == i2
  | Rvar  x1   , Rvar  x2    => x1 == x2
  | Rmem  x1 e1, Rmem  x2 e2 => (x1 == x2) && (e1 == e2)
  | Raset x1 e1, Raset x2 e2 => (x1 == x2) && (e1 == e2)
  | _          , _           => false   
  end.

Lemma rval_eq_axiom : Equality.axiom rval_beq. 
Proof. 
Admitted.

Definition rval_eqMixin     := Equality.Mixin rval_eq_axiom.
Canonical  rval_eqType      := Eval hnf in EqType rval rval_eqMixin.

(* ** Instructions 
 * -------------------------------------------------------------------- *)

Inductive dir := UpTo | DownTo.

Scheme Equality for dir.

Lemma dir_eq_axiom : Equality.axiom dir_beq. 
Proof. 
  move=> x y;apply:(iffP idP).
  + by apply: internal_dir_dec_bl.
  by apply: internal_dir_dec_lb.
Qed.

Definition dir_eqMixin     := Equality.Mixin dir_eq_axiom.
Canonical  dir_eqType      := Eval hnf in EqType dir dir_eqMixin.

Definition range := (dir * pexpr * pexpr)%type.

Definition instr_info := positive.
Definition dummy_iinfo := xH.

Inductive assgn_tag := 
  | AT_keep    (* normal assignment *)
  | AT_rename  (* equality constraint introduced by inline ... *)
  | AT_inline. (* assignment to be removed later : introduce by unrolling ... *) 

Scheme Equality for assgn_tag.

Lemma assgn_tag_eq_axiom : Equality.axiom assgn_tag_beq. 
Proof. 
  move=> x y;apply:(iffP idP).
  + by apply: internal_assgn_tag_dec_bl.
  by apply: internal_assgn_tag_dec_lb.
Qed.

Definition assgn_tag_eqMixin     := Equality.Mixin assgn_tag_eq_axiom.
Canonical  assgn_tag_eqType      := Eval hnf in EqType assgn_tag assgn_tag_eqMixin.

(* -------------------------------------------------------------------- *)

Definition funname := positive.

Inductive inline_info := 
  | InlineFun
  | DoNotInline.

Scheme Equality for inline_info.

Lemma inline_info_eq_axiom : Equality.axiom inline_info_beq. 
Proof. 
  move=> x y;apply:(iffP idP).
  + by apply: internal_inline_info_dec_bl.
  by apply: internal_inline_info_dec_lb.
Qed.

Definition inline_info_eqMixin     := Equality.Mixin inline_info_eq_axiom.
Canonical  inline_info_eqType      := Eval hnf in EqType inline_info inline_info_eqMixin.

(* -------------------------------------------------------------------- *)


Inductive instr_r := 
| Cassgn : rval -> assgn_tag -> pexpr -> instr_r
| Copn   : rvals -> sopn -> pexprs -> instr_r 
 
| Cif    : pexpr -> seq instr -> seq instr  -> instr_r
| Cfor   : var_i -> range -> seq instr -> instr_r
| Cwhile : pexpr -> seq instr -> instr_r
| Ccall  : inline_info -> rvals -> funname -> pexprs -> instr_r 

with instr := MkI : instr_info -> instr_r ->  instr.

Notation cmd := (seq instr).

Record fundef := MkFun {
  f_iinfo  : instr_info;
  f_params : seq var_i;
  f_body   : cmd;
  f_res    : seq var_i;
}.

Definition prog := seq (funname * fundef).

Definition dummy_fundef := 
 {|f_iinfo := dummy_iinfo; f_params := [::]; f_body := [::]; f_res := [::] |}. 

Definition instr_d (i:instr) := 
  match i with
  | MkI i _ => i
  end.

Fixpoint instr_r_beq i1 i2 := 
  match i1, i2 with
  | Cassgn x1 tag1 e1, Cassgn x2 tag2 e2 => 
     (tag1 == tag2) && (x1 == x2) && (e1 == e2)
  | Copn x1 o1 e1, Copn x2 o2 e2 =>
     (x1 == x2) && (o1 == o2) && (e1 == e2)
  | Cif e1 c11 c12, Cif e2 c21 c22 =>
    (e1 == e2) && all2 instr_beq c11 c21 && all2 instr_beq c12 c22
  | Cfor i1 (dir1,lo1,hi1) c1, Cfor i2 (dir2,lo2,hi2) c2 =>
    (i1 == i2) && (dir1 == dir2) && (lo1 == lo2) && (hi1 == hi2) && all2 instr_beq c1 c2
  | Cwhile e1 c1 , Cwhile e2 c2 =>
    (e1 == e2) && all2 instr_beq c1 c2
  | Ccall ii1 x1 f1 arg1, Ccall ii2 x2 f2 arg2 => 
    (ii1 == ii2) && (x1==x2) && (f1 == f2) && (arg1 == arg2)
  | _, _ => false 
  end
with instr_beq i1 i2 := 
  match i1, i2 with
  | MkI if1 i1, MkI if2 i2 => (if1 == if2) && (instr_r_beq i1 i2) 
  end.

Lemma instr_r_eq_axiom : Equality.axiom instr_r_beq. 
Proof. 
Admitted.

Definition instr_r_eqMixin     := Equality.Mixin instr_r_eq_axiom.
Canonical  instr_r_eqType      := Eval hnf in EqType instr_r instr_r_eqMixin.

Lemma instr_eq_axiom : Equality.axiom instr_beq. 
Proof. 
Admitted.

Definition instr_eqMixin     := Equality.Mixin instr_eq_axiom.
Canonical  instr_eqType      := Eval hnf in EqType instr instr_eqMixin.

Definition fundef_beq fd1 fd2 := 
  match fd1, fd2 with
  | MkFun ii1 x1 c1 r1, MkFun ii2 x2 c2 r2 =>
    (ii1 == ii2) && (x1 == x2) && (c1 == c2) && (r1 == r2)
  end.

Lemma fundef_eq_axiom : Equality.axiom fundef_beq. 
Proof. 
Admitted.

Definition fundef_eqMixin     := Equality.Mixin fundef_eq_axiom.
Canonical  fundef_eqType      := Eval hnf in EqType fundef fundef_eqMixin.

(* ** Compute written variables
 * -------------------------------------------------------------------- *)

Definition vrv_rec (s:Sv.t) (rv:rval) :=
  match rv with
  | Rnone _    => s
  | Rvar  x    => Sv.add x s
  | Rmem  _ _  => s
  | Raset x _  => Sv.add x s
  end.

Definition vrvs_rec s (rv:rvals) := foldl vrv_rec s rv.

Definition vrv := (vrv_rec Sv.empty).
Definition vrvs := (vrvs_rec Sv.empty).

Fixpoint write_i_rec s i := 
  match i with
  | Cassgn x _ _    => vrv_rec s x
  | Copn xs _ _     => vrvs_rec s xs
  | Cif   _ c1 c2   => foldl write_I_rec (foldl write_I_rec s c2) c1
  | Cfor  x _ c     => foldl write_I_rec (Sv.add x s) c
  | Cwhile  _ c     => foldl write_I_rec s c
  | Ccall _ x _ _   => vrvs_rec s x
  end
with write_I_rec s i := 
  match i with
  | MkI _ i => write_i_rec s i
  end.

Definition write_i i := write_i_rec Sv.empty i.

Definition write_I i := write_I_rec Sv.empty i.

Definition write_c_rec s c := foldl write_I_rec s c.

Definition write_c c := write_c_rec Sv.empty c.

(*
Instance vrv_rec_m {t} : Proper (Sv.Equal ==> (@eq (rval t)) ==> Sv.Equal) vrv_rec.
Proof.
  move=> s1 s2 Hs x r ->.
  elim:r => //=.
(*  elim:r s1 s2 Hs => //= {t x} [x ?? -> //| ?? r1 Hr1 r2 Hr2 ???];auto. 
Qed. *)
Admitted.

Lemma vrv_var (x:var) info: Sv.Equal (vrv (Rvar info x)) (Sv.singleton x). 
Proof. rewrite /vrv /=;SvD.fsetdec. Qed.

Lemma vrv_mem e : Sv.Equal (vrv (Rmem e)) Sv.empty. 
Proof. rewrite /vrv /=;SvD.fsetdec. Qed.

Lemma vrv_recE t (r:rval t) s : Sv.Equal (vrv_rec s r) (Sv.union s (vrv r)).
Proof.
(*
  elim: r s => //= [x | e | ?? r1 Hr1 r2 Hr2] s.
  + by rewrite vrv_var;SvD.fsetdec.
  + by rewrite /vrv /=;SvD.fsetdec.
  rewrite /vrv /= !(Hr1,Hr2);SvD.fsetdec.
Qed. *)
Admitted.

Lemma vrv_pair t1 t2 (r1:rval t1) (r2:rval t2):
  Sv.Equal (vrv (Rpair r1 r2)) (Sv.union (vrv r1) (vrv r2)).
Proof. rewrite {1}/vrv /= !vrv_recE;SvD.fsetdec. Qed.

Lemma write_c_recE s c : Sv.Equal (write_c_rec s c) (Sv.union s (write_c c)).
Proof.
(*
  apply (@cmd_rect
           (fun i => forall s, Sv.Equal (write_i_rec s i) (Sv.union s (write_i i)))
           (fun i => forall s, Sv.Equal (write_I_rec s i) (Sv.union s (write_I i)))
           (fun c => forall s, Sv.Equal (write_c_rec s c) (Sv.union s (write_c c)))
           (fun _ _ _ => True)) => /= {c s}
    [ |i c1 Hi Hc1|t x e|e c1 c2 Hc1 Hc2|x rn c Hc| e c Hc | ?? x f a _|//] s;
    rewrite /write_i /write_c /=.
  + by SvD.fsetdec. 
  + by rewrite !Hc1 !Hi; SvD.fsetdec.  
  + by rewrite !vrv_recE;SvD.fsetdec.
  + by rewrite -!/(write_c_rec _ c1) -!/(write_c_rec _ c2) !Hc1 !Hc2; SvD.fsetdec.
  + by rewrite -!/(write_c_rec _ c) !Hc vrv_recE; SvD.fsetdec.
  + by rewrite -!/(write_c_rec _ c) !Hc ; SvD.fsetdec.
  by rewrite !vrv_recE; SvD.fsetdec.
Qed. *) Admitted.

Lemma write_i_recE s i : Sv.Equal (write_i_rec s i) (Sv.union s (write_i i)).
Proof. (* by apply (write_c_recE s [:: i]). Qed. *) Admitted.

Lemma write_c_nil : write_c [::] = Sv.empty.
Proof. done. Qed.

Lemma write_c_cons i c: Sv.Equal (write_c (i::c)) (Sv.union (write_I i) (write_c c)).
Proof. (* by rewrite {1}/write_c /= write_c_recE write_i_recE;SvD.fsetdec. Qed. *) Admitted.

Lemma write_i_assgn t (x:rval t) tag e : write_i (Cassgn x tag e) = vrv x. 
Proof. done. Qed.

Lemma write_i_if e c1 c2 :
   Sv.Equal (write_i (Cif e c1 c2)) (Sv.union (write_c c1) (write_c c2)).
Proof.
  rewrite /write_i /= -/(write_c_rec _ c1) -/(write_c_rec _ c2) !write_c_recE;SvD.fsetdec.
Qed.

Lemma write_i_for x rn c :
   Sv.Equal (write_i (Cfor x rn c)) (Sv.union (vrv x) (write_c c)).
Proof.
  rewrite /write_i /= -/(write_c_rec _ c) write_c_recE vrv_recE;SvD.fsetdec.
Qed.

Lemma write_i_while e c :
   Sv.Equal (write_i (Cwhile e c)) (write_c c).
Proof.
  rewrite /write_i /= -/(write_c_rec _ c) write_c_recE;SvD.fsetdec.
Qed.

Lemma write_i_call t1 t2 (f:fundef t1 t2) x a :
  write_i (Ccall x f a) = vrv x.
Proof. done. Qed.
*)

(* ** Compute read variables
 * -------------------------------------------------------------------- *)

Fixpoint read_e_rec (s:Sv.t) (e:pexpr) : Sv.t := 
  match e with
  | Pconst _        => s
  | Pbool  _        => s
  | Pcast  e        => read_e_rec s e 
  | Pvar   x        => Sv.add x s 
  | Pget   x e      => read_e_rec (Sv.add x s) e
  | Pload  x e      => read_e_rec (Sv.add x s) e
  | Pnot   e        => read_e_rec s e 
  | Papp2  op e1 e2 => read_e_rec (read_e_rec s e2) e1
  end.

Definition read_e := read_e_rec Sv.empty.
Definition read_es_rec := foldl read_e_rec.
Definition read_es := read_es_rec Sv.empty.
         
Definition read_rv_rec  (s:Sv.t) (r:rval) := 
  match r with
  | Rnone _   => s 
  | Rvar  _   => s
  | Rmem  x e => read_e_rec (Sv.add x s) e
  | Raset x e => read_e_rec (Sv.add x s) e 
  end.

Definition read_rv := read_rv_rec Sv.empty.
Definition read_rvs_rec := foldl read_rv_rec.
Definition read_rvs := read_rvs_rec Sv.empty.

Fixpoint read_i_rec (s:Sv.t) (i:instr_r) : Sv.t :=
  match i with
  | Cassgn x _ e => read_rv_rec (read_e_rec s e) x
  | Copn xs _ es => read_es_rec (read_rvs_rec s xs) es
  | Cif b c1 c2 => 
    let s := foldl read_I_rec s c1 in
    let s := foldl read_I_rec s c2 in
    read_e_rec s b 
  | Cfor x (dir, e1, e2) c =>
    let s := foldl read_I_rec s c in
    read_e_rec (read_e_rec s e2) e1
  | Cwhile e c =>
    let s := foldl read_I_rec s c in
    read_e_rec s e
  | Ccall _ xs _ es => read_es_rec (read_rvs_rec s xs) es
  end
with read_I_rec (s:Sv.t) (i:instr) : Sv.t :=
  match i with 
  | MkI _ i => read_i_rec s i
  end.
              
Definition read_c_rec := foldl read_I_rec.

Definition read_i := read_i_rec Sv.empty.

Definition read_I := read_I_rec Sv.empty.

Definition read_c := read_c_rec Sv.empty.

(*
Lemma read_eE t (e:pexpr t) s : Sv.Equal (read_e_rec e s) (Sv.union (read_e e) s).
Proof.
  rewrite /read_e; elim: e s => /=.
  + by move=> x s;SvD.fsetdec.
  + by [].
  + by move=> _ s;SvD.fsetdec.
  + by move=> _ s;SvD.fsetdec.
  + by move=> ??? e1 He1 s;apply He1.
  + move=> ???? e1 He1 e2 He2 s. 
    by rewrite He1 He2 (He1 (read_e_rec _ _));SvD.fsetdec.
  move=> ????? e1 He1 e2 He2 e3 He3 s.
  rewrite He1 (He1 (read_e_rec _ _)) He2 (He2 (read_e_rec _ _)) He3;SvD.fsetdec.
Qed.

Lemma read_rvE t s (x:rval t): Sv.Equal (read_rv_rec x s) (Sv.union s (read_rv x)).
Proof.
  (*
  elim : x s => //= [x | e | ?? x1 Hx1 x2 Hx2] s.
  + by rewrite /read_rv /=;SvD.fsetdec.
  + by rewrite /read_rv /= !read_eE;SvD.fsetdec.
  by rewrite /read_rv /= !Hx1 !Hx2;SvD.fsetdec.
Qed. *)
Admitted.

Lemma read_rv_pair t1 t2 (x1:rval t1) (x2:rval t2): 
  Sv.Equal (read_rv (Rpair x1 x2)) (Sv.union (read_rv x1) (read_rv x2)).
Proof. by rewrite /read_rv /= !read_rvE;SvD.fsetdec. Qed.

Lemma read_cE s c : Sv.Equal (read_c_rec s c) (Sv.union s (read_c c)).
Proof.
(*
  apply (@cmd_rect
           (fun i => forall s, Sv.Equal (read_i_rec s i) (Sv.union s (read_i i)))
           (fun c => forall s, Sv.Equal (read_c_rec s c) (Sv.union s (read_c c)))
           (fun _ _ _ => True)) => /= {c s}
    [ |i c1 Hi Hc1|t x e|e c1 c2 Hc1 Hc2|x [[dir lo] hi] c Hc|e c Hc | ?? x f a _|//] s;
    rewrite /read_i /read_c /=.
  + by SvD.fsetdec. 
  + by rewrite -/read_i -/read_c_rec !Hc1 Hi; SvD.fsetdec.  
  + by rewrite !read_rvE !read_eE; SvD.fsetdec.
  + by rewrite -/read_c_rec !read_eE !Hc2 !Hc1;SvD.fsetdec.
  + by rewrite -/read_c_rec !read_eE !Hc; SvD.fsetdec.
  + by rewrite -/read_c_rec !read_eE !Hc; SvD.fsetdec.
  by rewrite !read_eE; SvD.fsetdec.
Qed. *)
Admitted.

Lemma read_iE s i : Sv.Equal (read_i_rec s i) (Sv.union s (read_i i)).
Proof. (* by apply (read_cE s [:: i]). Qed. *) 
Admitted.

Lemma read_c_nil : read_c [::] = Sv.empty.
Proof. done. Qed.

Lemma read_c_cons i c: Sv.Equal (read_c (i::c)) (Sv.union (read_I i) (read_c c)).
Proof. (* rewrite {1}/read_c /= -/read_c_rec read_cE read_iE;SvD.fsetdec. Qed. *) 
Admitted.

Lemma read_i_assgn t (x:rval t) tag e :
  Sv.Equal (read_i (Cassgn x tag e)) (Sv.union (read_rv x) (read_e e)).
Proof. rewrite /read_i /= read_rvE read_eE;SvD.fsetdec. Qed.

Lemma read_i_if e c1 c2 :
   Sv.Equal (read_i (Cif e c1 c2)) (Sv.union (read_e e) (Sv.union (read_c c1) (read_c c2))).
Proof.
  rewrite /read_i /= -/read_c_rec read_eE !read_cE;SvD.fsetdec.
Qed.

Lemma read_i_for x dir lo hi c :
   Sv.Equal (read_i (Cfor x (dir, lo, hi) c)) 
            (Sv.union (read_e lo) (Sv.union (read_e hi) (read_c c))).
Proof.
  rewrite /read_i /= -/read_c_rec !read_eE read_cE;SvD.fsetdec.
Qed.

Lemma read_i_while e c :
   Sv.Equal (read_i (Cwhile e c)) 
            (Sv.union (read_e e) (read_c c)).
Proof.
  rewrite /read_i /= -/read_c_rec !read_eE read_cE;SvD.fsetdec.
Qed.

Lemma read_i_call t1 t2 (f:fundef t1 t2) x a :
  read_i (Ccall x f a) = read_e a.
Proof. done. Qed.
*)

(* ** Some smart constructors
 * -------------------------------------------------------------------------- *)

Fixpoint is_const (e:pexpr) := 
  match e with
  | Pconst n => Some n
  | _        => None
  end.

(*
(*
Ltac jm_destr e1 := 
  let t := 
      match type of e1 with 
      | pexpr ?t => t 
      | _ => fail 1 "jm_destr: an spexpr is expected" 
      end in
  let e' := fresh "e'" in
  let t' := fresh "t'" in
  let H  := fresh "H" in
  let jmeq := fresh "jmeq" in
  move: (erefl t) (JMeq_refl e1);
  set e' := (e in _ -> @JMeq _ e _ _ -> _);move: e';
  set t' := (X in forall (e':pexpr X), X = _ -> @JMeq (pexpr X) _ _ _ -> _)=> e';
  (case: t' / e'=> [[??]H | ?? | ?? | ?? | ?????| ???????| ?????????] jmeq;
     [simpl in H | | | | | | ]);
  subst;try rewrite -(JMeq_eq jmeq).
*)
Lemma is_constP e n : is_const e = Some n -> e = n.
Proof. (*by jm_destr e=> //= -[] ->. Qed. *) Admitted.
*)

Definition is_bool (e:pexpr) :=
  match e with 
  | Pbool b => Some b 
  | _ => None 
  end.

Lemma is_boolP e b : is_bool e = Some b -> e = Pbool b.
Proof. (* by jm_destr e=> //= -[] ->. Qed. *) Admitted.