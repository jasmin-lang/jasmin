(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import finmap strings word dmasm_utils dmasm_type dmasm_var dmasm_expr dmasm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope fun_scope.
Local Open Scope vmap.
Local Open Scope seq_scope.

Fixpoint read_e t (e:pexpr t) (s:Sv.t) : Sv.t := 
  match e with
  | Pvar x => Sv.add x s 
  | Pconst _ => s
  | Pbool  _ => s
  | Papp1 _ _ op e1 => read_e e1 s
  | Papp2 _ _ _ op e1 e2 => read_e e1 (read_e e2 s)
  | Papp3 _ _ _ _ op e1 e2 e3 => read_e e1 (read_e e2 (read_e e3 s))
  end.
          
Fixpoint read_bcmd (s:Sv.t) (i:bcmd) : Sv.t := 
  match i with
  | Assgn _ _ e => read_e e s
  | Load _ e => read_e e s 
  | Store e1 e2 => read_e e1 (read_e e2 s)
  end.

Fixpoint read_i (s:Sv.t) (i:instr) : Sv.t :=
  match i with
  | Cbcmd i => read_bcmd s i 
  | Cif b c1 c2 => 
    let s := foldl read_i s c1 in
    let s := foldl read_i s c2 in
    read_e b s 
  | Cfor fi x (dir, e1, e2) c =>
    let s := foldl read_i s c in
    read_e e1 (read_e e2 s)
  | Ccall ta tr x fd arg => read_e arg s
  end.
                 
Definition read_c : Sv.t -> cmd -> Sv.t := foldl read_i.
  
Section CMD.

  Variable dead_code_i : instr ->  Sv.t -> Sv.t * cmd.

  Fixpoint dead_code (c:cmd) (s:Sv.t) : Sv.t * cmd :=
    match c with
    | [::] => (s, [::])
    | i::c =>
      let (s, c) := dead_code c s in
      let (s,ic) := dead_code_i i s in
      (s, ic ++ c)
    end.

End CMD.

Section LOOP.

  Variable dead_code_c : Sv.t -> Sv.t * cmd.

  Fixpoint loop (n:nat) (rc wx:Sv.t) (s:Sv.t) : Sv.t * cmd :=
    match n with
    | O => 
      let s :=  Sv.union rc s in
      let (_, c) := dead_code_c s in
      (s, c)
    | S n =>
      let (s', c') := dead_code_c s in
      let s' := Sv.diff s' wx in
      if Sv.subset s' s then (s,c') 
      else loop n rc wx (Sv.union s s')  
    end.

End LOOP.


Definition dead_code_bcmd (i:bcmd) (s:Sv.t) :=
  match i with
  | Assgn t rv e =>
    let w := write_bcmd i in
    if Sv.is_empty (Sv.inter s w) then (s,[::])
    else (read_e e (Sv.diff s w), [::Cbcmd i])
  | Load r e => 
    let w := write_bcmd i in
    (read_e e (Sv.diff s w) , [::Cbcmd i])
  | Store e1 e2 =>
    (read_e e1 (read_e e2 s), [::Cbcmd i])
  end.

Definition nb_loop := 100 %coq_nat.

Fixpoint dead_code_i (i:instr) (s:Sv.t) {struct i} : Sv.t * cmd := 
  match i with
  | Cbcmd i     => dead_code_bcmd i s 
  | Cif b c1 c2 => 
    let (s1,c1) := dead_code dead_code_i c1 s in
    let (s2,c2) := dead_code dead_code_i c2 s in
    (read_e b (Sv.union s1 s2), [:: Cif b c1 c2])
  | Cfor fi x (dir, e1, e2) c =>
    let wc := read_c Sv.empty c in
    let (s, c) := loop (dead_code dead_code_i c) nb_loop wc (vrv x) s in
    (read_e e1 (read_e e2 s),[::Cfor fi x (dir,e1,e2) c])
  | Ccall ta tr x fd arg =>
    (read_e arg (Sv.diff s (vrv x)), [::Ccall x (dead_code_call fd) arg])
  end

with dead_code_call ta tr (fd:fundef ta tr) := 
  match fd with
  | FunDef ta tr p c r =>
    let (_, c) := dead_code dead_code_i c (vrv r) in
    FunDef p c r
  end.


