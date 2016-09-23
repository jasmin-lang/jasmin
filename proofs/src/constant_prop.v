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

(* -------------------------------------------------------------------------- *)
(* ** Smart constructors                                                      *)
(* -------------------------------------------------------------------------- *)

Definition snot (e:pexpr sbool) : pexpr sbool := 
  match e with
  | Pbool b          => negb b
  | Papp1 _ _ Onot e => e 
  | _                => Papp1 Onot e
  end.

Definition sfst t1 t2 (p:pexpr (t1 ** t2)) : pexpr t1 :=
  match destr_pair p with
  | Some (p1,p2) => p1
  | _            => Papp1 (Ofst _ _) p
  end.

Definition ssnd t1 t2 (p:pexpr (t1 ** t2)) : pexpr t2 :=
  match destr_pair p with
  | Some (p1,p2) => p2
  | _            => Papp1 (Osnd _ _) p
  end.

Definition s_op1 t1 tr (op:sop1 t1 tr): pexpr t1 -> pexpr tr := 
  match op in sop1 t1 tr return pexpr t1 -> pexpr tr with
  | Onot     => snot 
  | Ofst _ _ => @sfst _ _ 
  | Osnd _ _ => @ssnd _ _
  end.

Definition is_bool (e:pexpr sbool) :=
  match e with Pbool b => Some b | _ => None end.

Definition sand e1 e2 := 
  match is_bool e1, is_bool e2 with
  | Some b, _ => if b then e2 else false
  | _, Some b => if b then e1 else false
  | _, _      => Papp2 Oand e1 e2
  end.

Definition sor (e1 e2:pexpr sbool) : pexpr sbool := 
   match is_bool e1, is_bool e2 with
  | Some b, _ => if b then Pbool true else e2
  | _, Some b => if b then Pbool true else e1
  | _, _       => Papp2 Oor e1 e2 
  end.

Definition spair {t t'} (e1:pexpr t) (e2:pexpr t') :=
  Papp2 (Opair t t') e1 e2.

Definition is_const t (e:pexpr t) := 
  match e with
  | Pconst n => Some n 
  | _        => None
  end.

Definition seq (e1 e2:pexpr sword) : pexpr sbool := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => (n1 =? n2)%num
  | _, _             => Papp2 Oeq e1 e2
  end.

Definition sadd (e1 e2:pexpr sword) : pexpr sword := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => iword_add n1 n2 
  | Some n, _ => 
    if (n =? 0)%num then e2 else Papp2 Oadd e1 e2
  | _, Some n => 
    if (n =? 0)%num then e1 else Papp2 Oadd e1 e2
  | _, _ => Papp2 Oadd e1 e2
  end.

Definition saddc (e1 e2:pexpr sword) : pexpr (sbool ** sword) := 
  Papp2 Oaddc e1 e2.

Definition ssub (e1 e2:pexpr sword) : pexpr sword := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => iword_sub n1 n2 
  | _, Some n => 
    if (n =? 0)%num then e1 else Papp2 Osub e1 e2
  | _, _ => Papp2 Osub e1 e2
  end.

Definition ssubc (e1 e2:pexpr sword) : pexpr (sbool ** sword) := 
  Papp2 Osubc e1 e2.

Definition slt (e1 e2:pexpr sword) : pexpr sbool := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => iword_ltb n1 n2 
  | _        , Some n  => if (n =? 0)%num then Pbool false else Papp2 Olt e1 e2
  | _        , _         => Papp2 Olt e1 e2 (* FIXME : false is e1 = e2 *)
  end.

Definition sle (e1 e2:pexpr sword) : pexpr sbool := 
  match is_const e1, is_const e2 with
  | Some n1, Some n2 => iword_leb n1 n2 
  | _        , _         => Papp2 Ole e1 e2 (* FIXME : true is e1 = e2 *)
  end.

(* FIXME: add other simplifications *)
Definition s_op2 t1 t2 tr (op:sop2 t1 t2 tr): pexpr t1 -> pexpr t2 -> pexpr tr := 
  match op in sop2 t1 t2 tr return pexpr t1 -> pexpr t2 -> pexpr tr with
  | Oand        => sand 
  | Oor         => sor 
  | Oeq         => seq 
  | Oadd        => sadd
  | Oaddc       => saddc
  | Osub        => ssub
  | Osubc       => ssubc
  | Olt         => slt
  | Ole         => sle
  | Oget n      => Papp2 (Oget n)
  | Opair t1 t2 => @spair t1 t2
  end.

Definition s_op3 t1 t2 t3 tr (op:sop3 t1 t2 t3 tr):=  Papp3 op.

(* ** constant propagation 
 * -------------------------------------------------------------------- *)


Local Notation map := (Mvar.t iword).

Fixpoint const_prop_e t (m:map) (e:pexpr t) : pexpr t :=
  match e in pexpr t0 return pexpr t0 with
  | Pvar x =>
    match vtype x as t0 return pexpr t0 -> pexpr t0 with
    | sword => fun e =>
      match Mvar.get m x with
      | Some n => Pconst n
      | _      => e
      end
    | _ => fun e => e
    end (Pvar x)
  | Pconst n => Pconst n
  | Pbool  b => Pbool b
  | Papp1 _ _ op e1 => 
    s_op1 op (const_prop_e m e1)
  | Papp2 _ _ _ op e1 e2 => 
    s_op2 op (const_prop_e m e1) (const_prop_e m e2)
  | Papp3 _ _ _ _ op e1 e2 e3 => 
    s_op3 op (const_prop_e m e1) (const_prop_e m e2) (const_prop_e m e3) 
  end.

Definition empty_cpm : map := @Mvar.empty iword.

Definition merge_cpm : map -> map -> map := 
  Mvar.map2 (fun _ (o1 o2: option iword) => 
   match o1, o2 with
   | Some n1, Some n2 => 
     if (n1 =? n2)%num then Some n1
     else None
   | _, _ => None
   end).

Definition remove_cpm (m:map) (s:Sv.t): map :=
  Sv.fold (fun x m => Mvar.remove m x) s m.

Fixpoint add_cpm t (m:map) (rv:rval t) : pexpr t -> map := 
  match rv in rval t0 return pexpr t0 -> map with 
  | Rvar x => fun e => 
    match is_const e with
    | Some n => Mvar.set m x n 
    | None   => m
    end
  | Rpair _ _ rv1 rv2 => fun e =>
    match destr_pair e with
    | Some (e1,e2) => add_cpm (add_cpm m rv1 e1) rv2 e2
    | None         => m
    end
  end.
                           
Section CMD.

  Variable const_prop_i : map -> instr -> map * cmd.

  Fixpoint const_prop (m:map) (c:cmd) : map * cmd :=
    match c with
    | [::] => (m, [::])
    | i::c =>
      let (m,ic) := const_prop_i m i in
      let (m, c) := const_prop m c in
      (m, ic ++ c)
    end.

End CMD.

Definition constr_prop_bcmd (m:map) (i:bcmd) :=
  match i with
  | Assgn t rv e =>
    let e := const_prop_e m e in
    (add_cpm m rv e, Assgn rv e)
  | Load r e => 
    let e := const_prop_e m e in
    (m, Load r e)
  | Store e1 e2 =>
    let e1 := const_prop_e m e1 in
    let e2 := const_prop_e m e2 in
    (m, Store e1 e2)
  end.

Fixpoint const_prop_i (m:map) (i:instr) : map * cmd := 
  match i with
  | Cbcmd _     => (m, [::i])
  | Cif b c1 c2 => 
    let b := const_prop_e m b in
    match is_bool b with
    | Some b => 
      let c := if b then c1 else c2 in 
      const_prop const_prop_i m c
    | None =>
      let (m1,c1) := const_prop const_prop_i m c1 in
      let (m2,c2) := const_prop const_prop_i m c2 in
      (merge_cpm m1 m2, [:: Cif b c1 c2])
    end
  | Cfor fi x (dir, e1, e2) c =>
    let r := write_i i in
    let m := remove_cpm m r in
    let (_,c) := const_prop const_prop_i m c in
    (m,[::Cfor fi x (dir, const_prop_e m e1, const_prop_e m e2) c])
  | Ccall ta tr x fd arg =>
    let arg := const_prop_e m arg in
    let r := write_i i in
    let m := remove_cpm m r in
    (m, [:: i])
  end

with const_prop_call ta tr (fd:fundef ta tr) := 
  match fd with
  | FunDef ta tr p c r =>
    let (_, c) := const_prop const_prop_i empty_cpm c in
    FunDef p c r
  end.


