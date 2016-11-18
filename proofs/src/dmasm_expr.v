(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import JMeq ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import strings word dmasm_utils dmasm_type dmasm_var.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope string_scope.



(* ** Operators
 * -------------------------------------------------------------------- *)

Inductive sop1 : stype -> stype -> Set := 
(* bools *)
| Onot  : sop1 sbool sbool
(* words *)
(*| Olnot : sop1 sword sword *)
(* pairs *)
| Ofst  : forall st1 st2, sop1 (st1 ** st2) st1
| Osnd  : forall st1 st2, sop1 (st1 ** st2) st2.

Inductive sop2 : stype -> stype -> stype -> Set :=
(* bools *)
| Oand  : sop2 sbool sbool sbool
| Oor   : sop2 sbool sbool sbool
(* words *)
| Oadd   : sop2 sword sword sword
| Omul   : sop2 sword sword sword
| Oaddc  : sop2 sword sword (sbool ** sword)

| Osub  : sop2 sword sword sword
| Osubc  : sop2 sword sword (sbool ** sword)

(*| Oxor  : sop2 sword sword sword
| Oland : sop2 sword sword sword
| Olor  : sop2 sword sword sword *)
| Oeq   : sop2 sword sword sbool
| Olt   : sop2 sword sword sbool
| Ole   : sop2 sword sword sbool
(* arrays *)
| Oget  : forall n, sop2 (sarr n) sword sword
(* pairs *)
| Opair : forall st1 st2, sop2 st1 st2 (st1 ** st2).

Inductive sop3 : stype -> stype -> stype -> stype -> Set :=
(* words *)
| Oaddcarry : sop3 sword sword sbool (sbool ** sword)
| Osubcarry : sop3 sword sword sbool (sbool ** sword)
(* arrays *)
| Oset  : forall n, sop3 (sarr n) sword sword (sarr n).

Definition eqb_sop1 {t1 tr t1' tr'} (o:sop1 t1 tr) (o':sop1 t1' tr') := 
  match o, o' with
  | Onot    , Onot     => true
  | Ofst _ _, Ofst _ _ => true
  | Osnd _ _, Osnd _ _ => true
  | _       , _        => false
  end.

Definition eqb_sop2 {t1 t2 tr t1' t2' tr'} (o:sop2 t1 t2 tr) (o':sop2 t1' t2' tr') := 
  match o, o' with
| Oand     , Oand      => true
| Oor      , Oor       => true
| Oadd     , Oadd      => true
| Oaddc    , Oaddc     => true
| Omul     , Omul     => true
| Osub     , Osub      => true
| Osubc    , Osubc     => true
| Oeq      , Oeq       => true
| Olt      , Olt       => true
| Ole      , Ole       => true
| Oget _   , Oget _    => true
| Opair _ _, Opair _ _ => true
| _        , _         => false
end.

Definition eqb_sop3 {t1 t2 t3 tr t1' t2' t3' tr'} 
           (o:sop3 t1 t2 t3 tr) (o':sop3 t1' t2' t3' tr') := 
  match o, o' with
 | Oaddcarry , Oaddcarry  => true
 | Osubcarry , Osubcarry  => true
 | Oset _    , Oset _     => true
 | _         , _          => false
 end.

Lemma eqb_sop1P t1 t1' tr tr' (o:sop1 t1 tr) (o':sop1 t1' tr'):
  t1 = t1' -> eqb_sop1 o o' ->  tr = tr' /\ JMeq o o'.
Proof. by move: o o' => [|??|??] [|??|??] //= [] ->->. Qed. 

Lemma eqb_sop2P t1 t1' t2 t2' tr tr' (o:sop2 t1 t2 tr) (o':sop2 t1' t2' tr'):
  t1 = t1' -> t2 = t2' -> eqb_sop2 o o' -> tr = tr' /\ JMeq o o'.
Proof. by move: o o'=> [||||||||||?|??] [||||||||||?|??] //= => [ []->| ->->]. Qed.

Lemma eqb_sop3P t1 t1' t2 t2' t3 t3' tr tr' (o:sop3 t1 t2 t3 tr) (o':sop3 t1' t2' t3' tr'):
  t1 = t1' -> t2 = t2' -> t3 = t3' -> eqb_sop3 o o' ->  tr = tr' /\ JMeq o o'.
Proof. by move: o o'=> [||?] [||?] // [] ->. Qed.


(* ** Expressions
 * -------------------------------------------------------------------- *)

Inductive pexpr : stype -> Type :=
| Pvar   :> forall (x:var), pexpr (vtype x)
| Pload  :> pexpr sword -> pexpr sword
| Pconst :> Z -> pexpr sword
| Pbool  :> bool -> pexpr sbool
| Papp1  : forall st1 stres: stype, 
  sop1 st1 stres -> pexpr st1 -> pexpr stres
| Papp2  : forall st1 st2 stres: stype, 
  sop2 st1 st2 stres -> pexpr st1 -> pexpr st2 -> pexpr stres
| Papp3  : forall st1 st2 st3 stres: stype, 
  sop3 st1 st2 st3 stres -> pexpr st1 -> pexpr st2 -> pexpr st3 -> pexpr stres.


(* ** Right values
 * -------------------------------------------------------------------- *)

Inductive rval : stype -> Type :=
| Rvar  :> forall (x:var), rval (vtype x)
| Rmem  :> pexpr sword -> rval sword 
| Raset :  forall (s:positive), Ident.ident -> pexpr sword -> rval sword
| Rpair :  forall st1 st2, rval st1 -> rval st2 -> rval (st1 ** st2).

(* ** Instructions 
 * -------------------------------------------------------------------- *)

Inductive dir := UpTo | DownTo.

Definition range := (dir * pexpr sword * pexpr sword)%type.

Inductive instr := 
| Cassgn : forall st, rval st -> pexpr st -> instr
| Cif    : pexpr sbool -> seq instr -> seq instr -> instr
| Cfor   : rval sword -> range -> seq instr -> instr
| Cwhile : pexpr sbool -> seq instr -> instr
| Ccall  : forall starg stres, 
             rval  stres ->
             fundef starg stres ->
             pexpr starg ->
             instr

with fundef : stype -> stype -> Type := 
| FunDef : forall starg stres, rval starg -> seq instr -> pexpr stres -> fundef starg stres.

Notation cmd := (seq instr).

Definition fd_arg sta str (fd : fundef sta str) : rval sta :=
  match fd with FunDef _ _ fa _ _ => fa end.

Definition fd_body sta str (fd : fundef sta str) : cmd :=
  match fd with FunDef _ _ _ fb _ => fb end.

Definition fd_res sta str (fd : fundef sta str) : pexpr str :=
  match fd with FunDef _ _ _ _ fr => fr end.

Section IND.
  Variable Pi : instr -> Type.
  Variable Pc : cmd -> Type.
  Variable Pf : forall ta tr, fundef ta tr -> Type.

  Hypothesis Hskip  : Pc [::].
  Hypothesis Hseq   : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Hypothesis Hassgn : forall t x e,  Pi (@Cassgn t x e).
  Hypothesis Hif    : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
  Hypothesis Hfor   : forall i rn c, Pc c -> Pi (Cfor i rn c).
  Hypothesis Hwhile : forall e c, Pc c -> Pi (Cwhile e c).
  Hypothesis Hcall1 : forall ta tr x (f:fundef ta tr) a, Pc (fd_body f) -> Pi (Ccall x f a).

  Fixpoint instr_rect1 (i:instr) : Pi i := 
    match i return Pi i with
    | Cassgn t x e => Hassgn x e
    | Cif b c1 c2 =>
      Hif b
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect1 i) Hc) c1)
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect1 i) Hc) c2)
    | Cfor i rn c =>
      Hfor i rn 
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect1 i) Hc) c)
    | Cwhile e c =>
      Hwhile e 
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect1 i) Hc) c)
    | Ccall ta tr x f a =>
      @Hcall1 ta tr x f a 
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect1 i) Hc) (fd_body f))
    end.

  Definition cmd_rect1 c := 
    list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect1 i) Hc) c.

  Hypothesis Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
  Hypothesis Hfunc : forall ta tr (x:rval ta) c (re:pexpr tr), Pc c -> Pf (FunDef x c re).

  Fixpoint instr_rect2 (i:instr) : Pi i := 
    match i return Pi i with
    | Cassgn t x e => Hassgn x e
    | Cif b c1 c2 =>
      Hif b
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect2 i) Hc) c1)
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect2 i) Hc) c2)
    | Cfor i rn c =>
      Hfor i rn 
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect2 i) Hc) c)
    | Cwhile e c =>
      Hwhile e 
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect2 i) Hc) c)
    | Ccall ta tr x f a =>
      Hcall x a (func_rect f)
    end
  with func_rect {ta tr} (f:fundef ta tr) : Pf f := 
    match f with
    | FunDef ta tr x c re => 
      Hfunc x re
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect2 i) Hc) c)
    end.

  Definition cmd_rect c := 
    list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect2 i) Hc) c.

End IND.

Definition cmd_ind (P:cmd -> Prop) (Pf:forall ta tr, fundef ta tr -> Prop) := 
  @cmd_rect (fun i => P [::i]) P Pf.

Definition func_ind (P:cmd -> Prop) (Pf:forall ta tr, fundef ta tr -> Prop) := 
  @func_rect (fun i => P [::i]) P Pf.

Definition assgn st (rv : rval st) pe := Cassgn rv pe.
Definition load (rv:rval sword) pe := Cassgn rv (Pload pe).
Definition store pe1 pe2 := Cassgn (Rmem pe1) pe2.

Definition cmd_Ind (P : cmd -> Prop) := 
  @cmd_ind P (fun _ _ _ => True).

(* -------------------------------------------------------------------------- *)
(* Compute the set of writen variables of a program                           *)
(* -------------------------------------------------------------------------- *)

Fixpoint vrv_rec {t} (s:Sv.t) (rv : rval t)  :=
  match rv with
  | Rvar  x               => Sv.add x s
  | Rmem  _               => s
  | Raset sz id _         => Sv.add {|vname := id; vtype := sarr sz |} s
  | Rpair st1 st2 rv1 rv2 => vrv_rec (vrv_rec s rv1) rv2 
  end.

Definition vrv {t} (rv : rval t) := vrv_rec Sv.empty rv.

Fixpoint write_i_rec s i := 
  match i with
  | Cassgn t x _    => vrv_rec s x
  | Cif   _ c1 c2   => foldl write_i_rec (foldl write_i_rec s c2) c1
  | Cfor  x _ c     => foldl write_i_rec (vrv_rec s x) c
  | Cwhile  _ c     => foldl write_i_rec s c
  | Ccall _ _ x _ _ => vrv_rec s x
  end.

Definition write_i i := write_i_rec Sv.empty i.

Definition write_c_rec s c := foldl write_i_rec s c.

Definition write_c c := write_c_rec Sv.empty c.

Instance vrv_rec_m {t} : Proper (Sv.Equal ==> (@eq (rval t)) ==> Sv.Equal) vrv_rec.
Proof.
  move=> s1 s2 Hs x r ->.
(*  elim:r s1 s2 Hs => //= {t x} [x ?? -> //| ?? r1 Hr1 r2 Hr2 ???];auto. 
Qed. *)
Admitted.


Lemma vrv_var (x:var) : Sv.Equal (vrv x) (Sv.singleton x). 
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
  apply (@cmd_rect
           (fun i => forall s, Sv.Equal (write_i_rec s i) (Sv.union s (write_i i)))
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
Qed.

Lemma write_i_recE s i : Sv.Equal (write_i_rec s i) (Sv.union s (write_i i)).
Proof. by apply (write_c_recE s [:: i]). Qed.

Lemma write_c_nil : write_c [::] = Sv.empty.
Proof. done. Qed.

Lemma write_c_cons i c: Sv.Equal (write_c (i::c)) (Sv.union (write_i i) (write_c c)).
Proof. by rewrite {1}/write_c /= write_c_recE write_i_recE;SvD.fsetdec. Qed.

Lemma write_i_assgn t (x:rval t) e : write_i (Cassgn x e) = vrv x. 
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

Fixpoint read_e_rec t (e:pexpr t) (s:Sv.t) : Sv.t := 
  match e with
  | Pvar x                    => Sv.add x s 
  | Pload e                   => read_e_rec e s
  | Pconst _                  => s
  | Pbool  _                  => s
  | Papp1 _ _     op e1       => read_e_rec e1 s
  | Papp2 _ _ _   op e1 e2    => read_e_rec e1 (read_e_rec e2 s)
  | Papp3 _ _ _ _ op e1 e2 e3 => read_e_rec e1 (read_e_rec e2 (read_e_rec e3 s))
  end.

Definition read_e t (e:pexpr t) := read_e_rec e Sv.empty.
         
Fixpoint read_rv_rec t (r:rval t) (s:Sv.t) := 
  match r with
  | Rvar _ => s
  | Rmem e => read_e_rec e s
  | Raset sz id e => read_e_rec e (Sv.add {|vname := id; vtype := sarr sz|} s)
  | Rpair _ _ e1 e2 => read_rv_rec e1 (read_rv_rec e2 s)
  end.

Definition read_rv t (r:rval t) := read_rv_rec r Sv.empty.

Fixpoint read_i_rec (s:Sv.t) (i:instr) : Sv.t :=
  match i with
  | Cassgn _ x e => read_rv_rec x (read_e_rec e s)
  | Cif b c1 c2 => 
    let s := foldl read_i_rec s c1 in
    let s := foldl read_i_rec s c2 in
    read_e_rec b s 
  | Cfor x (dir, e1, e2) c =>
    let s := foldl read_i_rec s c in
    read_e_rec e1 (read_e_rec e2 s)
  | Cwhile e c =>
    let s := foldl read_i_rec s c in
    read_e_rec e s
  | Ccall ta tr x fd arg => read_e_rec arg s
  end.
              
Definition read_c_rec : Sv.t -> cmd -> Sv.t := foldl read_i_rec.

Definition read_i := read_i_rec Sv.empty.

Definition read_c := foldl read_i_rec Sv.empty.

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
Qed.

Lemma read_iE s i : Sv.Equal (read_i_rec s i) (Sv.union s (read_i i)).
Proof. by apply (read_cE s [:: i]). Qed.

Lemma read_c_nil : read_c [::] = Sv.empty.
Proof. done. Qed.

Lemma read_c_cons i c: Sv.Equal (read_c (i::c)) (Sv.union (read_i i) (read_c c)).
Proof. rewrite {1}/read_c /= -/read_c_rec read_cE read_iE;SvD.fsetdec. Qed.

Lemma read_i_assgn t (x:rval t) e : Sv.Equal (read_i (Cassgn x e)) (Sv.union (read_rv x) (read_e e)).
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

(* -------------------------------------------------------------------------- *)
(* Some smart constructors                                                    *)
(* -------------------------------------------------------------------------- *)

Definition destr_pair t1 t2 (p:pexpr (t1 ** t2)) : option (pexpr t1 * pexpr t2).
case H: _ / p => [ ? | ? | ? | ? | ???? | ??? o e1 e2| ???????? ].
+ exact None. + exact None. + exact None. + exact None. + exact None. 
+ (case:o H e1 e2 => [|||||||||||??[]<-<- e1 e2];last by exact (Some (e1,e2)))=> *; 
  exact None.
exact None. 
Defined.

Lemma destr_pairP t1 t2 (p:pexpr (t1 ** t2)) p1 p2:
   destr_pair p = Some (p1, p2) -> p = Papp2 (Opair _ _) p1 p2.
Proof.
  move=>Heq;apply JMeq_eq.
  have {Heq}: JMeq (destr_pair p) (Some (p1, p2)) by rewrite Heq.
  rewrite /destr_pair; move:p (erefl (t1 ** t2)). 
  set t12 := (X in forall (p:pexpr X) (e : _ = X), _ -> @JMeq (pexpr X) _ _ _) => p.
  case : t12 / p => //.
  + by move=> []/= ??<- Heq;have := JMeq_eq Heq.
  + by move=> ???? _ Heq;have := JMeq_eq Heq.
  + move=> t1' t2' tr' [] st1 st2 => //= => [ []?? e| []?? e | e1 e2 e].
    + by have := JMeq_eq e.  + by have := JMeq_eq e.
    case: (e)=> ??. subst st1 st2.
    rewrite (eq_irrelevance e (erefl (t1 ** t2))) /= /eq_rect_r /=.
    move=> Heq;have [-> ->] // := JMeq_eq Heq.
  by move=> ???? ???? ? Heq;have := JMeq_eq Heq.
Qed.

Definition is_const t (e:pexpr t) := 
  match e with
  | Pconst n => Some n 
  | _        => None
  end.

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

Lemma is_constP e n : is_const e = Some n -> e = n.
Proof. by jm_destr e=> //= -[] ->. Qed.

Definition is_bool (e:pexpr sbool) :=
  match e with Pbool b => Some b | _ => None end.

Lemma is_boolP e b : is_bool e = Some b -> e = Pbool b.
Proof. by jm_destr e=> //= -[] ->. Qed.

Definition efst t1 t2 (p:pexpr (t1 ** t2)) : pexpr t1 :=
  match destr_pair p with
  | Some (p1,p2) => p1
  | _            => Papp1 (Ofst _ _) p
  end.

Definition esnd t1 t2 (p:pexpr (t1 ** t2)) : pexpr t2 :=
  match destr_pair p with
  | Some (p1,p2) => p2
  | _            => Papp1 (Osnd _ _) p
  end.

(*Fixpoint rval2pe t (rv:rval t) := 
  match rv in rval t_ return pexpr t_ with
  | Rvar x              => x
  | Rmem e              => Pload e
  | Rpair t1 t2 rv1 rv2 => Papp2 (Opair t1 t2) (rval2pe rv1) (rval2pe rv2)
  end.  *)

Lemma read_e_efst t1 t2 (e:pexpr (t1 ** t2)): Sv.Subset (read_e (efst e)) (read_e e).
Proof.
  rewrite /efst.
  case: destr_pair (@destr_pairP _ _ e) => [[e1 e2] /(_ _ _ (erefl _)) ->| _].
  + by rewrite /read_e /= !read_eE;SvD.fsetdec.
  by rewrite /read_e /=;SvD.fsetdec.
Qed.

Lemma read_e_esnd t1 t2 (e:pexpr (t1 ** t2)): Sv.Subset (read_e (esnd e)) (read_e e).
Proof.
  rewrite /esnd.
  case: destr_pair (@destr_pairP _ _ e) => [[e1 e2] /(_ _ _ (erefl _)) ->| _].
  + by rewrite /read_e /= (read_eE e1) !read_eE;SvD.fsetdec.
  by rewrite /read_e /=;SvD.fsetdec.
Qed.

(*
Lemma read_rval2pe t (x:rval t): Sv.Equal (read_e (rval2pe x)) (vrv x).
Proof.
  rewrite /read_e;elim: x => /= [x | e | ?? x1 Hx1 x2 Hx2].
  + by rewrite vrv_var;SvD.fsetdec.
  + rewrite read_eE vrv_mem.
vrv_var;SvD.fsetdec.
  rewrite !read_eE vrv_pair -Hx1 -Hx2;SvD.fsetdec.
Qed.
*)
(* ----------------------------------------------------------------------------------- *)

Fixpoint eqb_pexpr t1 t2 (e1:pexpr t1) (e2:pexpr t2) : bool :=
  match e1, e2 with
  | Pvar x1  , Pvar x2    => x1 == x2
  | Pload e1 , Pload e2   => eqb_pexpr e1 e2 
  | Pconst n1, Pconst n2  => n1 == n2 
  | Pbool b1 , Pbool b2   => b1 == b2
  | Papp1 _ _ o1 e1         , Papp1 _ _ o2 e2          => 
    eqb_sop1 o1 o2 && eqb_pexpr e1 e2
  | Papp2 _ _ _ o1 e11 e12   , Papp2 _ _ _ o2 e21 e22     =>  
    eqb_sop2 o1 o2 && eqb_pexpr e11 e21 && eqb_pexpr e12 e22
  | Papp3 _ _ _ _ o1 e11 e12 e13, Papp3 _ _ _ _ o2 e21 e22 e23 => 
    eqb_sop3 o1 o2 && eqb_pexpr e11 e21 && eqb_pexpr e12 e22 && eqb_pexpr e13 e23
  | _, _ => false
  end.

Definition eqb_dir d1 d2 :=
  match d1, d2 with
  | UpTo  , UpTo   => true
  | DownTo, DownTo => true
  | _     , _     => false
  end.

Fixpoint eqb_rval t1 (x1:rval t1) t2 (x2:rval t2) :=
  match x1, x2 with
  | Rvar x1          , Rvar x2           => x1 == x2
  | Rmem e1          , Rmem e2           => eqb_pexpr e1 e2
  | Raset s1 i1 e1   , Raset s2 i2 e2    => (s1 == s2) && (i1 == i2) && eqb_pexpr e1 e2
  | Rpair _ _ x11 x12, Rpair _ _ x21 x22 => eqb_rval x11 x21 && eqb_rval x12 x22
  | _                , _                 => false
  end.
 
Fixpoint eqb_instr i1 i2 := 
  match i1, i2 with
  | Cassgn _ x1 e1, Cassgn _ x2 e2 => eqb_rval x1 x2 && eqb_pexpr e1 e2
  | Cif e1 c11 c12, Cif e2 c21 c22 =>
    eqb_pexpr e1 e2 && all2 eqb_instr c11 c21 && all2 eqb_instr c12 c22
  | Cfor i1 (dir1,lo1,hi1) c1, Cfor i2 (dir2,lo2,hi2) c2 =>
    eqb_dir dir1 dir2 && eqb_pexpr lo1 lo2 && eqb_pexpr hi1 hi2 &&
    all2 eqb_instr c1 c2
  | Cwhile e1 c1 , Cwhile e2 c2 =>
    eqb_pexpr e1 e2 && all2 eqb_instr c1 c2
  | Ccall _ _ x1 fd1 arg1, Ccall _ _ x2 fd2 arg2 => 
    eqb_rval x1 x2 &&
    eqb_fundef fd1 fd2 &&
    eqb_pexpr arg1 arg2
  | _, _ => false 
  end
with eqb_fundef ta1 tr1 (fd1:fundef ta1 tr1) ta2 tr2 (fd2:fundef ta2 tr2) :=
  match fd1, fd2 with
  | FunDef _ _ p1 c1 r1, FunDef _ _ p2 c2 r2 =>
    eqb_rval p1 p2 && eqb_pexpr r1 r2 && all2 eqb_instr c1 c2
  end.

Lemma eqb_dirP d1 d2 : reflect (d1 = d2) (eqb_dir d1 d2).
Proof. by case: d1 d2 => -[] /=;constructor. Qed.

Lemma eqb_pexprP t1 (e1:pexpr t1) t2 (e2:pexpr t2):
    eqb_pexpr e1 e2 -> t1 = t2 /\ JMeq e1 e2.
Proof.
  elim:e1 t2 e2=>
    [x1|e1 H1|z1|b1|?? o1 e1 H1|??? o1 e11 H1 e12 H2|???? o1 e11 H1 e12 H2 e13 H3] t2
    [x2|e2|z2|b2|?? o2 e2   |??? o2 e21    e22   |???? o2 e21    e22    e23] //=.
  + by move=> /eqP ->. + by move=> /H1[] ? ->.
  + by move=> /eqP ->. + by move=> /eqP ->.
  + by move=> /andP[] /eqb_sop1P H /H1[] ?;subst;case:H=> // ?;subst=> -> ->.
  + move=> /andP[]/andP[] /eqb_sop2P H /H1 [] ? Heq1;subst.
    by move=> /H2[] ? Heq2;subst;case:H => // ?;subst=> ->.
  move=> /andP[]/andP[]/andP[] /eqb_sop3P H /H1 [] ? Heq1;subst.
  move=> /H2[] ? Heq2;subst; move=> /H3[] ? Heq3;subst.
  by case:H => // ?;subst=> ->.
Qed.

Lemma eqb_rvalP t1 (x1:rval t1) t2 (x2:rval t2):
    eqb_rval x1 x2 -> t1 = t2 /\ JMeq x1 x2.
Proof.
(*
  elim: x1 t2 x2=> [x1 | e1|?? x11 H1 x12 H2] t2 [x2 | e2 | ?? x21 x22] //=.
  + by move=> /eqP ->.
  + by move=> /eqb_pexprP[] _ ->.
  by move=> /andP[] /H1[]?;subst=> -> /H2[]?;subst=> ->.
Qed.
*)
Admitted.




 