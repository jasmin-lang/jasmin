From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses
     EquivDec
     Equality
     Program.Tactics.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

From ITree Require Import
     ITree
     ITreeFacts
     Monad
     Basics.HeterogeneousRelations     
     Events.Map
     Events.State
     Events.StateFacts
     Events.Reader
     Events.Exception
     Events.FailFacts.

Require Import Paco.paco.
Require Import Psatz.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype fintype.

From ITree Require Import
(*     Basics.Tacs *)
     Basics.Category
     Basics.Basics
     Basics.Function
     Core.ITreeDefinition
     Core.KTree
     Eq.Eqit
     Eq.UpToTaus
     Eq.Paco2
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Handler
     Interp.Interp
     Interp.InterpFacts
     Interp.Recursion.

From ITree Require Import Rutt RuttFacts.

From ITree Require Import EqAxiom.

From Jasmin Require Import expr psem_defs psem oseq.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope option_scope.

Obligation Tactic := done || idtac.

(* This files contains itrees general lemmas that depend on Jasmin
files *)

Section ExecT.

  Context {m : Type -> Type} {Fm: Functor.Functor m} {Mm : Monad m}
    {MIm : MonadIter m}.

  Definition execT (m : Type -> Type) (a : Type) : Type :=
    m (exec a)%type.

  Global Instance execT_fun : Functor.Functor (execT m) :=
    {| Functor.fmap :=
        fun X Y (f: X -> Y) => 
          Functor.fmap (fun x =>
                          match x with
                          | Error e => Error e
                          | Ok x => @Ok error Y (f x) end) |}.

  Global Instance execT_monad : Monad (execT m) :=
    {| ret := fun _ x => ret (ok x);
       bind := fun _ _ c k =>
                 bind (m := m) c 
                   (fun x => match x with
                             | Error e => ret (Error e)
                             | Ok x => k x end)
    |}.

  Global Instance execT_iter  : MonadIter (execT m) :=
    fun A I body i => Basics.iter (M := m) (I := I) (R := exec A) 
      (fun i => bind (m := m)
               (body i)
               (fun x => match x with
                         | Error e       => ret (inr (Error e))
                         | Ok (inl j) => ret (inl j)
                         | Ok (inr a) => ret (inr (ok a))
                         end)) i.

End ExecT.


Section Lang.
Context (asm_op: Type) (asmop: asmOp asm_op).

Section WSW.
Context {wsw: WithSubWord}.   
Context
  (dc: DirectCall)
  (syscall_state : Type)
  (ep : EstateParams syscall_state)
  (spp : SemPexprParams)
  (sip : SemInstrParams asm_op syscall_state)
  (pT : progT)
  (scP : semCallParams)
  (ev : extra_val_t).

(*** INDUCTION PRINCIPLE ****************************************************)
(** induction on Jasmin commands *)
Section CMD_IND.

Context (Pr: instr_r -> Prop) (Pi: instr -> Prop) (Pc: cmd -> Prop).
Context (Hnil : Pc [::])
        (Hcons : forall i c, Pi i -> Pc c -> Pc (i::c))

        (Hinstr : forall ii ir, Pr ir -> Pi (MkI ii ir))
        
        (Hassgn : forall x tg ty e, Pr (Cassgn x tg ty e))
        (Hopn : forall x tg o e, Pr (Copn x tg o e))
        (Hsyscall : forall x sc e, Pr (Csyscall x sc e))
        (Hif   : forall e c1 c2, Pc c1 -> Pc c2 -> Pr (Cif e c1 c2))
        (Hfor  : forall i rn c, Pc c -> Pr (Cfor i rn c))
        (Hwhile : forall a c1 e c2, Pc c1 -> Pc c2 -> Pr (Cwhile a c1 e c2))
        (Hcall  : forall xs fn es, Pr (Ccall xs fn es)).

Fixpoint cmd_IndF (Hi : forall i, Pi i) (c : cmd) : Pc c := 
  match c with
  | [::] => Hnil
  | i :: c => Hcons i c (Hi i) (cmd_IndF Hi c)
  end.

Definition instr_Ind (Hr : forall i, Pr i) (i : instr) : Pi i :=
  match i with MkI ii ir => Hinstr ii ir (Hr ir) end.

Fixpoint instr_r_Ind (ir: instr_r) : Pr ir :=
  let R := cmd_IndF (instr_Ind instr_r_Ind) in 
  match ir return Pr ir with
  | Cassgn x tg ty e => Hassgn x tg ty e 
  | Copn x tg o e => Hopn x tg o e
  | Csyscall x sc e => Hsyscall x sc e                        
  | Cif e c1 c2 => Hif e c1 c2 (R c1) (R c2)
  | Cfor i rn c => Hfor i rn c (R c)                     
  | Cwhile a c1 e c2 => Hwhile a c1 e c2 (R c1) (R c2)
  | Ccall xs fn es => Hcall xs fn es
  end.

Definition cmd_Ind := cmd_IndF (instr_Ind instr_r_Ind).

End CMD_IND.

End WSW.

End Lang.

