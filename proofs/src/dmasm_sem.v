(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
Require Import choice fintype eqtype div seq finmap strings zmodp.
Require Import dmasm_utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.
Local Open Scope fset.
Local Open Scope fmap.

(* ** Types for idents and values
 * -------------------------------------------------------------------- *)

Section Sem.

Variable word : Set.

Inductive ident :=
| Id of string.

(* *** Canonical structures *)

Definition word_eqMixin := comparableClass (@LEM word).
Canonical  word_eqType  := Eval hnf in EqType word word_eqMixin.

Canonical  word_choiceType  := ChoiceType word admit.

Definition ident_eqMixin := comparableClass (@LEM ident).
Canonical  ident_eqType  := Eval hnf in EqType ident ident_eqMixin.

Canonical  ident_choiceType  := ChoiceType ident admit.

(* ** Maps
 * -------------------------------------------------------------------- *)

Inductive map (k v : Type) :=
| Map : (k -> option v) -> map k v.

Definition mempty k v : map k v := Map (fun _ => None).

Definition mget k v (m : map k v) (x : k) :=
  match m with Map f => f x end.

Definition mset k v (m : map k v) (x : k) (y : v) : map k v :=
  admit.

(* ** Source language types
 * -------------------------------------------------------------------- *)

(* more expressive than required, but leads to simpler definitions *)
Inductive stype : Set :=
| sword : stype
| sbool : stype
| sarr  : stype -> stype.

Definition stype_eqMixin := comparableClass (@LEM stype).
Canonical  stype_eqType  := Eval hnf in EqType stype stype_eqMixin.

Fixpoint type_of_stype (t : stype) : Type :=
  match t with
  | sword   => word
  | sbool   => bool
  | sarr st => @map word (type_of_stype st)
  end.

Definition arr (st : stype) := map (type_of_stype st).

(* ** Function-local variable map
 * -------------------------------------------------------------------- *)

Inductive var (st : stype) : Type :=
| Var : ident -> var st.

Definition vname st (v : var st) :=
  let: Var s := v in s.

Definition lmap := forall st, {fmap ident -> type_of_stype st}.

Variable pexpr : stype -> Set.

Definition eval_pexpr st (lm : lmap) (pe : pexpr st) : result (type_of_stype st) :=
  admit.

(* ** Locations and sources
 * -------------------------------------------------------------------- *)

Inductive loc (st : stype) :=
| Lvar : var st -> loc st
| Aget : var (sarr st) -> pexpr sword -> loc st.

Inductive src (st : stype) : Type :=
| Imm : pexpr st -> src st
| Loc : loc st   -> src st.

(* ** Reading local variables
 * -------------------------------------------------------------------- *)

Definition read_loc st (lm : lmap) (l : loc st) : result (type_of_stype st) :=
  match l with
  | Lvar (Var vid) =>
      o2r "IdUndef" ((lm st).[? vid])
  | Aget (Var vid) pe =>
      o2r "IdUndef" ((lm (sarr st)).[? vid]) >>= fun a =>
      eval_pexpr lm pe >>= fun w =>
      o2r "IdxUndef" (mget a w)
  end.

Definition read_src st (lm : lmap) (s : src st) : result (type_of_stype st) :=
  match s with
  | Imm pe => eval_pexpr lm pe >>= fun w => Ok w
  | Loc d  => read_loc lm d
  end.

Parameter st : stype.
Parameter st' : stype.

Check (LEM st st').

(* ** Writing local variables
 * -------------------------------------------------------------------- *)
Print sumbool.

Definition write_loc st (lm : lmap) (l : loc st) (v : type_of_stype st) : lmap :=
  match l with
  | Lvar (Var vid) =>
    fun st' =>
      match LEM st st' with
      | left p => admit (lm st).[vid <- v]
      | right p => lm st'
      end
  | Aget (Var vid) pe => lm
  end.

Fixpoint write_locs (lm : lmap) (ds : seq loc) (vs : seq sval) : result lmap :=
  match ds, vs with
  | [::], [::] => Ok lm
  | [::], _    => Error "write_locs: impossible"
  | _,    [::] => Error "write_locs: impossible"
  | [:: d & ds], [:: v & vs] =>
      write_loc lm d v >>= fun lm =>
      write_locs lm ds vs
  end.

(* ** Instructions
 * -------------------------------------------------------------------- *)

Inductive instr :=
| Skip
| Seq   : instr -> instr -> instr
| Assgn : seq loc -> op -> seq src -> instr
| Load  : loc -> addr -> instr
| Store : addr -> src -> instr
| If    : pcond -> instr -> instr -> instr
| For   : ident -> pexpr -> pexpr -> instr -> instr
| Call  : seq ident ->  seq src -> instr (* function def: (args, body, ret) *)
          -> seq ident
          -> seq src
          -> instr.

Fixpoint eval_instr (lm : lmap) (i : instr) : result lmap :=
  match i with
  | Skip =>
      Ok lm

  | Seq i1 i2 =>
      eval_instr lm i1 >>= fun lm =>
      eval_instr lm i2

  | Assgn ds op ss =>
      mapM (read_src lm) ss >>= fun args =>
      eval_op op args >>= fun res =>
      write_locs lm ds res

  | If pc i1 i2 =>
      eval_pcond lm pc >>= fun cond =>
      if cond then eval_instr lm i1 else eval_instr lm i2

  | For id lb_pe ub_pe i => (* FIXME: support decreasing loop *)
      let step :=
        fun j lm =>
          eval_instr lm.[ id <- Vword j] i
      in
      eval_pexpr lm lb_pe >>= fun lb =>
      eval_pexpr lm ub_pe >>= fun ub =>
      foldM step lm (map (fun n => n2w n) (list_from_to (w2n lb) (w2n ub)))

  | Call fargs frets fbody drets args =>
      (* read values for given args *)
      mapM (read_src lm) args >>= fun args =>
      (* write given args as formal args into fresh stack frame *)
      write_locs fmap0 (map (mkLoc None) fargs) args >>= fun lm_call =>
      (* evaluate body *)
      eval_instr lm_call fbody >>= fun lm_call =>
      (* read return values *)
      mapM (read_src lm_call) frets >>= fun rets =>
      (* store return values into dret *)
      write_locs lm (map (mkLoc None) drets) rets

  | Load loc addr =>
      Ok lm

  | Store addr src =>
      Ok lm

  end.


(* ** Memory
 * -------------------------------------------------------------------- *)
(* *** QHASM memory move
Read from mem:
r = *(uint64 * ) (s + n)
  where sources int64 s, immediate n
        result  int64 r
  ASM: movq n(s),r

r = *( int64 * ) (s + t * 8)
  where sources int64 s, int64 t
        result int64 r
  ASM: movq (s,t,8),r

r = *( int64 * ) (s + n + t * 8)
  where sources: int64 s, int64 t, immediate n
        result:  int64 r
  ASM: movq n(s,t,8),r

Write to mem:
*( int64 * ) (s + t) = r
  where src int64 r, int64 s, int64 t
  ASM: movq r,(s,t)
*)
(* *** Definitions *)

Record addr := mkAddr {
  a_s : ident;
  a_n : pexpr;        (* just use Pconst 0 if not required *)
  a_t : option ident
}.

Definition gmap := {fmap word -> word}.
