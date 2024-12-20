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

From Jasmin Require Import utils. (*expr psem_defs psem oseq. *)

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
    {| ret := fun _ x => @ret m _ _ (Ok _ x);
       bind := fun _ _ c k =>
                 bind (m := m) c 
                   (fun x => match x with
                             | Error e => @ret m _ _ (Error e)
                             | Ok x => k x end)
    |}.

  Global Instance execT_iter  : MonadIter (execT m) :=
    fun A I body i => Basics.iter (M := m) (I := I) (R := exec A) 
      (fun i => bind (m := m)
               (body i)
               (fun x => match x with
                         | Error e       => ret (inr (Error e))
                         | Ok (inl j) => @ret m _ _ (inl j)
                         | Ok (inr a) => @ret m _ _ (inr (Ok _ a))
                         end)) i.

End ExecT.


Section ExecTLaws. 

Definition result_rel (W: Set) {X} (R : relation X) (Re : relation W) :
   relation (result W X) :=
fun (mx my : result W X) =>
match mx with
| Ok x => match my with
            | Ok y => R x y
            | Error _ => False
            end
| Error e0 => match my with
          | Ok _ => False
          | Error e1 => Re e0 e1 
          end
end.

Definition exec_rel {X: Type} (R : relation X) :
   relation (exec X) := result_rel error R (fun x y => True). 

Definition foo (X: Type) (ls: list X) : exec (list X) := Ok _ ls.

From Jasmin Require Import var xseq type warray_ word. (*  psem_defs psem oseq. *)
Require Import BinNums.


Definition sem_t (t : stype) : Type :=
  match t with
  | sbool    => bool
  | sint     => Z
  | sarr n   => WArray.array n
  | sword s  => unit (* Jasmin.word.word s *)
  end.

(*
Print stype.
Print map.
Print WArray.array.
Print Mz.t.
Print Mz.Map.t.
Print Mz.Map.bst.

Record array' (s : positive) : Set := Build_array'
  { arr_data : Mz.t (ssralg.GRing.ComRing.sort u8) }.
*)

Definition sem_prod (ts: list stype) := @map stype Type sem_t ts.

Print map.

(*
Print WArray.array.
Print Eq1.
Definition sem_ot (t:stype) : Type :=
  if t is sbool then option bool
  else sem_t t.

Definition sem_tuple ts := ltuple (map sem_ot ts).

Fixpoint sem_prod_ok {T: Type} (tin : seq stype) : sem_prod tin T -> sem_prod tin (exec T) :=
  match tin return sem_prod tin T -> sem_prod tin (exec T) with
  | [::] => fun o => ok o
  | t :: ts => fun o v => @sem_prod_ok T ts (o v)
  end.
Arguments sem_prod_ok {T}%type_scope tin%seq_scope _.
*)

(* Universe inconsistency - and can't find a way to fix it *)
(* Unset Universe Checking.  *)
Fail Global Instance execT_Eq1 {E} : Eq1 (execT (itree E)) :=
  fun _ => eutt (exec_rel eq).

Set Printing Universes.

About result.
Print result.
(*
Variant
result (E : Type@{result.u0}) (A : Type@{result.u1})
  : Type@{max(Set,result.u0,result.u1)} :=
    Ok : A -> result E A | Error : E -> result E A.

Arguments result (E A)%type_scope
Arguments Ok E%type_scope [A]%type_scope _
Arguments Error {E A}%type_scope s
  (where some original arguments have been renamed)
 *)
Check Ok.

About Ok.
Unset Printing Universes.

Check Ok.

Print exec.
(*
exec = [eta result error]
     : Type@{exec.u0} -> Type@{max(Set,exec.u0)}

Arguments exec t%type_scope
*)

End ExecTLaws.



