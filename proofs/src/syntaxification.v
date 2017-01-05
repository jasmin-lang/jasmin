(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import JMeq ZArith.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple finfun.
From mathcomp Require Import choice fintype eqtype div seq zmodp.

Require Import pos_map word dmasm_utils dmasm_type dmasm_var dmasm_sem.
Require Import dmasm_sem_props dmasm_Ssem symbolic_expr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.
Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
Parameter nat2id : nat -> ident.

(* -------------------------------------------------------------------- *)
Class find (T : Type) (x : T) (xs : seq T) (p:positive).

Instance find0 (T : Type) (x : T) (xs : seq T) : find x (x :: xs) xH.

Instance findS (T : Type) (x : T) (y : T) (ys :  seq T) p {_: find x ys p}
 : find x (y :: ys) (Pos.succ p) | 1.

(* -------------------------------------------------------------------- *)
Class closed_list (T : Type) (xs : seq T).
Instance closed_nil T : closed_list (T:=T) nil.
Instance closed_cons T (x:T) (xs:seq T) {_: closed_list xs} : 
  closed_list (x :: xs).

(* -------------------------------------------------------------------- *)
Class closed_nat (n : nat).
Instance closed_O : closed_nat 0%nat.
Instance closed_S n `{closed_nat n} : closed_nat (n .+1).

(* -------------------------------------------------------------------- *)
Class closed_pos (n : positive).
Instance closed_xH : closed_pos xH.
Instance closed_xO n `{closed_pos n} : closed_pos (xO n).
Instance closed_xI n `{closed_pos n} : closed_pos (xI n).

(* -------------------------------------------------------------------- *)
Class closed_N (n : N).
Instance closed_N0: closed_N N0.
Instance closed_Npos n `{closed_pos n} : closed_N (Npos n).

(* -------------------------------------------------------------------- *)
Class closed_bool (b:bool).
Instance closed_true  : closed_bool true.
Instance closed_false : closed_bool false.

(* -------------------------------------------------------------------- *)
Class closed_ascii (c:Ascii.ascii).
Instance closed_Ascii b1 b2 b3 b4 b5 b6 b7 b8
  `{closed_bool b1} `{closed_bool b2} `{closed_bool b3} `{closed_bool b4}
  `{closed_bool b5} `{closed_bool b6} `{closed_bool b7} `{closed_bool b8}
 : closed_ascii (Ascii.Ascii b1 b2 b3 b4 b5 b6 b7 b8).

(* -------------------------------------------------------------------- *)
Class closed_string (s:String.string).
Instance closed_Emptystring : closed_string String.EmptyString.
Instance closed_String c s `{closed_ascii c} `{closed_string s} :
                closed_string (String.String c s).

(* -------------------------------------------------------------------- *)
Class closed_stype (t : stype).
Instance closed_sword : closed_stype sword.
Instance closed_sbool : closed_stype sbool.
Instance closed_sprod t1 t2 `{closed_stype t1} `{closed_stype t2} : 
  closed_stype (t1 ** t2).
Instance closed_sarr n t `{closed_nat n} `{closed_stype t} : 
  closed_stype (sarr n t).

(* -------------------------------------------------------------------- *)
Class closed_var (x : var).
Instance closed_Var x `{closed_stype x.(vtype)} 
  `{closed_string x.(vname)} : closed_var x.

(* -------------------------------------------------------------------- *)

Record box := { bt:stype; be: pexpr bt }.

Class ereify t (e:pexpr t) st (se:spexpr st) (s:seq box).

Instance ereify_Pvar (x:var) `{closed_var x} s: 
  ereify (Pvar x) (Evar x) s.
Instance ereify_Pconst (n:N) `{closed_N n} s: 
  ereify (Pconst n) (Econst n) s.
Instance ereify_Papp1 t1 tr (o:sop1 t1 tr) (e:pexpr t1) (se:spexpr t1) s
  `{ereify t1 e t1 se} : ereify (Papp1 o e) (Eapp1 o se) s.
Instance ereify_Papp2 t1 t2 tr (o:sop2 t1 t2 tr) (e1:pexpr t1) (e2:pexpr t2) 
  (se1:spexpr t1) (se2:spexpr t2) s
  `{ereify t1 e1 t1 se1} `{ereify t2 e2 t2 se2}: 
  ereify (Papp2 o e1 e2) (Eapp2 o se1 se2) s.
Instance ereify_Papp3 t1 t2 t3 tr (o:sop3 t1 t2 t3 tr) 
  (e1:pexpr t1) (e2:pexpr t2) (e3:pexpr t3) 
  (se1:spexpr t1) (se2:spexpr t2) (se3:spexpr t3) s
  `{ereify t1 e1 t1 se1} `{ereify t2 e2 t2 se2} `{ereify t3 e3 t3 se3}: 
   ereify (Papp3 o e1 e2 e3) (Eapp3 o se1 se2 se3) s.

Instance ereify_svar (t:stype) (e:pexpr t) (s:seq box) p 
  `{find box {|bt:=t;be:= e|} s p} : 
    @ereify t e t (Esvar {| svtype:= t; svname:=p|}) s | 100.

Definition ereifyl t1 e t2 se s `{ereify t1 e t2 se s} `{closed_list _ s} := (se,s).

(*
Definition foo1 := ereifyl (e:= Papp2 Oeq (Pvar (Var sword "")) (Pvar (Var sword ""))).
Compute foo1.
*)
