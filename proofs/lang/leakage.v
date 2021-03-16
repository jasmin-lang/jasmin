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
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Psatz xseq.
Require Export array expr gen_map low_memory warray_ sem_type.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope leakage_scope with leakage.
Open Scope leakage_scope.

Inductive leak_e :=
| LEmpty : leak_e (* no leak *)
| LIdx : Z -> leak_e (* array access at given index *)
| LAdr : pointer -> leak_e (* memory access at given address *)
| LSub: (seq leak_e) -> leak_e. (* forest of leaks *)

(* why we don't name this function as cost of expression *)
Fixpoint size_leak_e (l : leak_e) : nat :=
match l with 
 | LEmpty => 1
 | LIdx z => 1 
 | LAdr p => 1
 | LSub le => List.length le
end.

Section Eq_leak_e.

Variable eq_leak_e : leak_e -> leak_e -> bool.

Fixpoint eq_leak_es (les: seq leak_e) (les' : seq leak_e) : bool :=
match les, les' with 
| [::], [::] => true
| a :: l, a' :: l' => andb (eq_leak_e a a') (eq_leak_es l l')
| _, _ => false
end.

End Eq_leak_e.

Fixpoint eq_leak_e (le : leak_e) (le' : leak_e) : bool :=
match le, le' with 
| LEmpty, LEmpty => true
| LIdx z, LIdx z' => if z == z' then true else false
| LAdr p, LAdr p' => if p == p' then true else false
| LSub les, LSub les' => eq_leak_es eq_leak_e les les'
| _, _ => false
end.

Definition leak_lea_exp : leak_e :=
  LSub [:: LEmpty; LSub [:: LEmpty; LSub [:: LEmpty; LEmpty]]].
  
Definition get_seq_leak_e (l : leak_e) : seq leak_e := 
match l with 
| LSub le => le
| _ => [::]
end.

Fixpoint get_nth_leak (l : seq leak_e) n : leak_e := 
 match l with 
  | [::] => LEmpty
  | x :: l => if n == 0 then x else get_nth_leak l (n-1)
 end.

Definition get_leak_e (l : leak_e) : leak_e := 
match l with 
| LSub le => if (size le) == 1 then (get_nth_leak le 0) else LEmpty
| _ => LEmpty
end.

Fixpoint make_leak_e_sub (l : leak_e) : leak_e :=
match l with 
| LSub le => LSub (map make_leak_e_sub le)
| _ => LSub [:: l]
end.

Inductive leak_i : Type :=
  | Lopn  : leak_e ->leak_i                                                  (* 1 *)      
  | Lcond  : leak_e -> bool -> seq leak_i -> leak_i                          (* 1 + cost (seq leak_i) *)
  | Lwhile_true : seq leak_i -> leak_e -> seq leak_i -> leak_i -> leak_i     
  | Lwhile_false : seq leak_i -> leak_e -> leak_i
  | Lfor : leak_e -> seq (seq leak_i) -> leak_i                              (* seq (seq leak_i) + size (seq (seq leak_i)) *) 
  | Lcall : leak_e -> (funname * seq leak_i) -> leak_e -> leak_i.            (* size leak_e + cost (seq leak_i) + size leak_e *)

Notation leak_c := (seq leak_i).

Notation leak_for := (seq leak_c) (only parsing).

Notation leak_fun := (funname * leak_c)%type.

(** Label **)

Inductive label_elem : Type :=
  | LblF of funname  
  | LblN of nat
  | LblB of bool.

(**** Some examples for Labelling ****)
(* LblF sub,0 :    fn sub(reg u64[1] z) { 
   LblF sub,LblN 0,0:     z[0] = 1; 
   }

          fn scalarmult(reg u64 n) {
                     stack u64[1] x;
                     reg u64[1] y;
0:                   x[0] = 0;
1:                   while (n >u 0) { 
1,0:                 y = x;                                  
1,1:                 sub(y);     (* in case if this function is inlined then the label will be 1,1,0 *)                        
1,2:                 n -= 1;
1,3:                 sub(y);     (* in case if this function is inlined then the label will be 1,3,0 *)
    }
}

*)

(* Defines equality on label_elem: return true if they are equal else returns false *)
Definition label_elem_beq (l1 l2: label_elem) : bool :=
match l1, l2 with 
 | LblF fn, LblF fn' => if fn == fn' then true else false
 | LblN n, LblN n' => if n == n' then true else false
 | LblB b, LblB b' => if b == b' then true else false
 | _, _ => false
end.

Lemma label_elem_eq_axiom : Equality.axiom label_elem_beq.
Proof.
  move=> [f | n | b] [f' | n' | b'] /=; 
   (by constructor ||  by case: eqP => [ -> | h]; constructor => // -[]).
Qed.

Definition label_elem_eqMixin     := Equality.Mixin label_elem_eq_axiom.
Canonical  label_elem_eqType      := Eval hnf in EqType label_elem label_elem_eqMixin.

Definition lbl := (seq label_elem * nat)%type.

Definition label_map := lbl -> nat.

(* This is like a counter for the label annotated with each instruction *)
Definition update_label_map (m:label_map) (l:lbl) : label_map :=
fun (l':lbl) => if l == l' then (m l) + 1 else (m l').

(* Takes a bool and a label and generates label depending on bool *)
Definition lbl_b (b:bool) (l:lbl) : lbl := (LblB b :: LblN l.2::l.1, 0).

Definition lbl_t (l:lbl) : lbl := lbl_b true l.

Definition lbl_f (l:lbl) : lbl := lbl_b false l.

Definition lbl_for (l:lbl) : lbl := (LblN l.2::l.1, 0).

Definition lbl_call fn (l:lbl) : lbl := (LblF fn :: LblN l.2::l.1, 0).

Definition next_lbl (l:lbl) := (l.1, l.2 + 1).

Definition empty_label_map : label_map := (fun _ => O).

(**************** EXAMPLES **********************************)

(* Exmaple 1 *)
(*                                              fn foo1 () {                  Lcall _ 
 ( [:: LblF foo1],0:                               x := 2;                    (foo1, [:: Lopn (LSub [:: LEmpty; LEmpty]  
   [:: LblF foo1],1:                               if (x <= 3) {                       ; Lcond LEmpty true (Lopn (LSub [:: LEmpty; LEmpty])]) _  
   [:: LblB true::LblN 1::LblF foo1],0:                 x := x + x;           
   [:: LblB false::LblN 1::LblF foo1],0:           else x := x - x;
                                                   }
                                                }  *)

(* Example 2 *)
(*                                              main () {                    [:: Lopn (LSub [:: LEmpty; LEmpty]
   [:: LblF main],0:                               x := 5;                    ; Lcall _  
   [:: LblF main],1:                               call foo1();                 (foo1, [:: Lopn (LSub [:: LEmpty; LEmpty]                  
                                                                                         ;  Lcond LEmpty true (Lopn (LSub [:: LEmpty; LEmpty])])]  
                                                }*)

(* Exmaple 3 *)
(*                                              fn foo2 () {                  Lcall _ 
   [:: LblF foo2],0:                               x := 2;                    (foo2, [:: Lopn (LSub [:: LEmpty; LEmpty]  
   [:: LblF foo2],1:                               if (x != 0) {                       ; Lcond LEmpty true (Lopn (LSub [:: LEmpty; LEmpty])
   [:: LblN true::LblN 1:: LblF foo2,0:                  x := x + 1;    
   [:: LblN false::LblN 1:: LblF foo2,0:            else x := x - 1; 
                                                    } ;
   [:: LblF foo2], 2:                               if (x <= 3) {                      ; Lcond LEmpty true (Lopn (LSub [:: LEmpty; LEmpty]))])
   [:: LblB true::LblN 2:: LblF foo2],0:                  x := x + x;
   [:: LblB false::LblN 2:: LblF foo2],0:            else x := x - x;
                                                    };
                                                } *)


(* Example 4 *)
(*                                             fn foo3 () {                   Lcall _           
   LblF foo3,0:                                   x := 4;                     (foo2, [:: Lopn (LSub [:: LEmpty; LEmpty])  
   LblF foo3,1:                                   r := 0                               ; Lopn (LSub [:: LEmpty; LEmpty])
   LblN foo3,3:                                   while (x <= 10) {(*7*)               ; Lwhile_true [::] _ 
   LblB true::LblN 3::LblN foo3,0                    r = r + 1;                                      [:: Lopn (LSub [:: LEmpty; LEmpty]);       
   LblB true::LblN 3::LblN foo3,1                    x++; }                                           Lopn (LSub [:: LEmpty; LEmpty])]; lw])
                                               } *)

(* Example 5 *)
(*                                             main () {
   [:: Lblf F main],0:                          call foo3();
                                               }  *)

Section Cost_C.

Variable cost_i : label_map -> lbl -> leak_i -> label_map.

Fixpoint cost_c (m:label_map) (l:lbl) (lc:leak_c) :=
 match lc with 
 | [::] => m 
 | li :: lc => let m1 := cost_i m l li in 
               cost_c m1 (next_lbl l) lc
end.

Fixpoint cost_cs (m:label_map) (l:lbl) (lc:seq leak_c) :=
 match lc with 
 | [::] => m
 | lc1 :: lcs1 => let m1 := cost_c m l lc1 in 
                  cost_cs m1 (next_lbl l) lcs1
 end.

End Cost_C.

(* l is the label for current instruction *)
Fixpoint cost_i (m : label_map) (l:lbl) (li : leak_i) : label_map :=
match li with 
 | Lopn _ => update_label_map m l 
 | Lcond _ b lc => let m := update_label_map m l in 
                   cost_c cost_i m (lbl_b b l) lc
 | Lwhile_true lc1 _ lc2 li => let m1 := update_label_map m l in 
                               let m2 := cost_c cost_i m1 (lbl_f l) lc1 in 
                               let m3 := cost_c cost_i m2 (lbl_t l) lc2 in 
                               cost_i m3 l li
 | Lwhile_false lc1 _ => let m1 := update_label_map m l in 
                         cost_c cost_i m1 (lbl_f l) lc1 
 | Lfor _ lcs => let m1 := update_label_map m l in 
                 cost_cs cost_i m1 (lbl_for l) lcs
 | Lcall _ (fn, lc) _ => let m1 := update_label_map m l in 
                         cost_c cost_i m (lbl_call fn l) lc
end.

Section Cost_leak_i.

Variable cost_leak_i : leak_i -> nat.

Fixpoint cost_leak_is (ls : seq leak_i) : nat :=
match ls with 
  | [::] => O
  | l' :: ls' => cost_leak_i l' + cost_leak_is ls'
end.

Fixpoint cost_leak_iss (ls : seq (seq leak_i)) : nat :=
match ls with 
  | [::] => O
  | l' :: ls' => cost_leak_is l' + cost_leak_iss ls'
end. 

End Cost_leak_i.
  
(* Cost of leak_i *)
Fixpoint cost_leak_i (l : leak_i) : nat :=
match l with 
  | Lopn le => 1 (* we assume cost of operation and assignment to be 1 *) (* we don't think about cost of reducing the expression *)
  | Lcond le b li => 1 (* cost of le *) +  cost_leak_is cost_leak_i li (* cost of the branch taken *)
  | Lwhile_true li le li' lw => cost_leak_is cost_leak_i li (* cost of false *) + 1 + 
                                cost_leak_is cost_leak_i li' (* cost of true *) +
                                cost_leak_i lw (* cost depending on number of iteration *) 
                                               (* it will depend on lw and no of iterations which we don't know here *)
  | Lwhile_false li le => cost_leak_is cost_leak_i li (* cost of false branch *) + 1 (* cost of condition *)
  | Lfor le liss => cost_leak_iss cost_leak_i liss + List.length liss (* length gives the cost of range? *)
  | Lcall le (fn, li) le' => size_leak_e le (* cost of arguments *)
                           + cost_leak_is cost_leak_i li (* cost of function body *) 
                           + size_leak_e le' (* cost of writing the results in lvals *)
end.

Section Eq_leak_i.

Variable eq_leak_i : leak_i -> leak_i -> bool.

Fixpoint eq_leak_is (les: seq leak_i) (les' : seq leak_i) : bool :=
match les, les' with 
| [::], [::] => true
| a :: l, a' :: l' => andb (eq_leak_i a a') (eq_leak_is l l')
| _, _ => false
end.

Fixpoint eq_leak_iss (les: seq (seq leak_i)) (les' : seq (seq leak_i)) : bool :=
match les, les' with 
| [::], [::] => true
| a :: l, a' :: l' => andb (eq_leak_is a a') (eq_leak_iss l l')
| _, _ => false
end.

End Eq_leak_i.

Fixpoint eq_leak_i (li : leak_i) (li' : leak_i) : bool :=
match li, li' with 
 | Lopn le, Lopn le' => eq_leak_e le le'
 | Lcond le b lis, Lcond le' b' lis' => andb (eq_leak_e le le') (andb (andb b b') (eq_leak_is eq_leak_i lis lis'))
 | Lwhile_true lis le lis' l, Lwhile_true lis1 le' lis1' l'=> 
   andb (andb (eq_leak_is eq_leak_i lis lis1) (eq_leak_e le le'))
        (andb (eq_leak_is eq_leak_i lis' lis1') (eq_leak_i l l'))
  | Lwhile_false lis le, Lwhile_false lis' le' => andb (eq_leak_is eq_leak_i lis lis') (eq_leak_e le le')
  | Lfor le liss, Lfor le' liss' => andb (eq_leak_e le le') (eq_leak_iss eq_leak_i liss liss')
  | Lcall le (fn, lis) le', Lcall le1 (fn1, lis1) le1' => if fn == fn1 
    then andb (andb (eq_leak_e le le1) (eq_leak_is eq_leak_i lis lis1))
              (eq_leak_e le' le1') else false
  | _, _ => false
end.

(* ------------------------------------------------------------------------ *)
(* Leakage trees and leakage transformations. *)

Inductive leak_tr_p :=
  | LS_const of pointer 
  | LS_stk
  | LS_Add `(leak_tr_p) `(leak_tr_p) 
  | LS_Mul `(leak_tr_p) `(leak_tr_p).

Fixpoint eq_leak_tr_p (ltp : leak_tr_p) (ltp' : leak_tr_p) : bool :=
match ltp, ltp' with 
 | LS_const p, LS_const p' => if p == p' then true else false
 | LS_stk, LS_stk => true
 | LS_Add l l', LS_Add l1 l1' => andb (eq_leak_tr_p l l1) (eq_leak_tr_p l' l1')
 | LS_Mul l l', LS_Mul l1 l1' => andb (eq_leak_tr_p l l1) (eq_leak_tr_p l' l1')
 | _, _ => false
end.

(*Inductive leak_tr_const := 
  | LTleak  `(leak_e)
  | LTAdr   `(leak_tr_p).
(*  | LTSub   `(seq leak_tr_const). *)
*)

(* Leakage transformer for expressions *)
Inductive leak_e_tr :=
| LT_id (* preserve *)
| LT_remove (* remove *)
| LT_const : leak_tr_p -> leak_e_tr
| LT_subi : nat -> leak_e_tr (* projection *)
| LT_lidx : (Z -> leak_tr_p) -> leak_e_tr
| LT_map : seq leak_e_tr -> leak_e_tr (* parallel transformations *)
| LT_seq : seq leak_e_tr -> leak_e_tr
| LT_compose: leak_e_tr -> leak_e_tr -> leak_e_tr (* compositon of transformations *)
(* lowering *)
| LT_rev : leak_e_tr. (* reverse transformation *)
(*| LT_var : leak_e_tr -> leak_e -> leak_e_tr
| LT_adr : Z -> Z -> leak_e_tr 
| LT_adrptr : pointer -> Z -> Z -> leak_e_tr.*)

Section Eq_leak_e_tr.
Variable eq_leak_e_tr : leak_e_tr -> leak_e_tr -> bool.

Fixpoint eq_leak_e_trs (ltes : seq leak_e_tr) (ltes' : seq leak_e_tr) : bool :=
match ltes, ltes' with 
| [::], [::] => true 
| [::], _ => false
| a :: l, a' :: l' => andb (eq_leak_e_tr a a') (eq_leak_e_trs l l')
| _, _ => false
end.

End Eq_leak_e_tr.

Fixpoint eq_leak_e_tr (lte : leak_e_tr) (lte' : leak_e_tr) : bool :=
match lte, lte' with 
| LT_id, LT_id => true
| LT_remove, LT_remove => true
| LT_const ltp, LT_const ltp' => eq_leak_tr_p ltp ltp'
| LT_subi n, LT_subi n' => if n == n' then true else false
| LT_map ltes, LT_map ltes' => eq_leak_e_trs eq_leak_e_tr ltes ltes'
| LT_seq ltes, LT_seq ltes' => eq_leak_e_trs eq_leak_e_tr ltes ltes'
| LT_compose lte lte', LT_compose lte1 lte1' => andb (eq_leak_e_tr lte lte1) (eq_leak_e_tr lte' lte1')
| LT_rev, LT_rev => true
| _, _ => false
(* need to include case of LT_lidx *)
end.

Inductive leak_e_es_tr :=
| LT_leseq : leak_e_es_tr
| LT_emseq : leak_e_es_tr
| LT_subseq : leak_e_tr -> leak_e_es_tr
| LT_idseq : leak_e_tr -> leak_e_es_tr
| LT_dfst : leak_e_es_tr
| LT_dsnd : leak_e_es_tr.

Definition eq_leak_e_es_tr (lts lts' : leak_e_es_tr) : bool :=
match lts, lts' with 
| LT_leseq, LT_leseq => true 
| LT_emseq, LT_emseq => true 
| LT_subseq lte, LT_subseq lte' => eq_leak_e_tr lte lte' 
| LT_idseq lte, LT_idseq lte' => eq_leak_e_tr lte lte'
| LT_dfst, LT_dfst => true 
| LT_dsnd, LT_dsnd => true
| _, _ => false
end.

Definition get_seq_leak_e_tr (l : leak_e_tr) : seq leak_e_tr := 
match l with 
| LT_seq le => le
| _ => [::]
end.

Fixpoint eval_leak_tr_p stk lp : pointer :=
  match lp with
  | LS_const p => p 
  | LS_stk     => stk
  | LS_Add p1 p2 => (eval_leak_tr_p stk p1 + eval_leak_tr_p stk p2)%R
  | LS_Mul p1 p2 => (eval_leak_tr_p stk p1 * eval_leak_tr_p stk p2)%R
  end.

Fixpoint leak_E (stk:pointer) (lt : leak_e_tr) (l : leak_e) : leak_e :=
  match lt, l with
  | LT_map lts, LSub xs => LSub (map2 (leak_E stk) lts xs)
  | LT_seq lts, _ => LSub (map (fun lt => leak_E stk lt l) lts)
  | LT_lidx f, LIdx i => LAdr (eval_leak_tr_p stk (f i))
  | LT_const f, _     => LAdr (eval_leak_tr_p stk f)
  | LT_id, _ => l
  | LT_remove, _ => LEmpty
  | LT_subi i, LSub xs => nth LEmpty xs i
  | LT_compose lt1 lt2, _ => leak_E stk lt2 (leak_E stk lt1 l)
  | LT_rev, LSub xs => LSub (rev xs)
  (*| LT_adr z1 z2 , LIdx i => LAdr (wrepr U64 (i*z1+z2))
  | LT_var lte le , LEmpty => LSub [:: leak_E lte LEmpty; le]
  | LT_adrptr p1 z1 z2 , LIdx i => LAdr (p1 + (wrepr U64 (i*z1+z2)))*)
  | _, _ => LEmpty
  end.

Definition leak_E_S (stk: pointer) (lts: seq leak_e_tr) (ls : seq leak_e) : seq leak_e :=
  map2 (leak_E stk) lts ls.

(* Transformation from leakage to sequence of leakage *)
Fixpoint leak_ES (stk : pointer) (lte : leak_e_es_tr) (le : leak_e) : seq leak_e :=
match lte, le with
| LT_leseq, le => [:: le]
| LT_emseq, le => [::]
| LT_subseq lte, le => [:: leak_E stk lte le]
| LT_idseq lte, le => get_seq_leak_e (leak_E stk lte le)
| LT_dfst, le => [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; le; LEmpty]
| LT_dsnd, le => [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; le]
end.            

Inductive leak_e_i_tr :=
| LT_iconditionl : leak_e_tr -> leak_e_i_tr (* lower condition transformer *)
| LT_iemptyl : leak_e_i_tr.

Definition eq_leak_e_i_tr (lei : leak_e_i_tr) (lei' : leak_e_i_tr) : bool :=
match lei, lei' with 
| LT_iconditionl lte, LT_iconditionl lte' => eq_leak_e_tr lte lte'
| LT_iemptyl, LT_emptyl => true
| _, _ => false
end.

Inductive leak_es_i_tr :=
| LT_iopn5f_large : leak_es_i_tr
| LT_iopn5f_other : leak_es_i_tr
| LT_iaddcarryf : leak_es_i_tr -> leak_es_i_tr
| LT_iaddcarry : leak_es_i_tr -> leak_es_i_tr
| LT_ianone : leak_es_i_tr
| LT_imul1 : leak_es_i_tr
| LT_imul2 : leak_es_i_tr
| LT_imul3 : leak_es_i_tr
| LT_imul4 : leak_es_i_tr
| LT_iemptysl : leak_es_i_tr.

Fixpoint eq_leak_es_i_tr (ltes ltes' : leak_es_i_tr) : bool :=
match ltes, ltes' with 
| LT_iopn5f_large, LT_iopn5f_large => true 
| LT_iopn5f_other, LT_iopn5f_other => true  
| LT_iaddcarryf lts, LT_iaddcarryf lts' => eq_leak_es_i_tr lts lts'
| LT_iaddcarry lts, LT_iaddcarry lts' => eq_leak_es_i_tr lts lts'
| LT_ianone, LT_ianone => true 
| LT_imul1, LT_imul1 => true 
| LT_imul2, LT_imul2 => true
| LT_imul3, LT_imul3 => true 
| LT_imul4, LT_imul4 => true 
| LT_iemptysl, LT_iemptysl => true
| _, _ => false
end.

(* Leakge transformer for instructions *)

(* tr_cost lt -> Exact n1 n2  | Linear a  
   lt' = leak_i_tr lt
   cost lt' <= a cost lt + b
*) 

Inductive cost_tr :=
| c_exact : nat -> nat -> cost_tr
| c_dummy : cost_tr.

Inductive leak_i_tr :=
(* structural transformation *)
| LT_ikeep : leak_i_tr                                                                  (* Exact 1 1 *)   (* same as source *)
| LT_ile : leak_e_tr -> leak_i_tr  (* assign and op *)                                  (* Exact 1 1 *)  (* same as source *)     
| LT_icond : leak_e_tr -> seq leak_i_tr -> seq leak_i_tr -> leak_i_tr (* if *)          (* linear comp *)  (* same as source *) 
| LT_iwhile : seq leak_i_tr -> leak_e_tr -> seq leak_i_tr -> leak_i_tr (* while *)      (* *)
| LT_ifor : leak_e_tr -> seq leak_i_tr -> leak_i_tr                  (* for c --> for c'     
  cost c' <= a cost c   cost (for c) = n * (cost c + 1)  <= n * (a cost c' + 1) <= max(1,a)cost (for c')  *)
| LT_icall : funname -> leak_e_tr -> leak_e_tr -> leak_i_tr      

| LT_iremove : leak_i_tr                                                                 (* 1 -> 0 *)      


| LT_icond_eval : bool -> seq leak_i_tr -> leak_i_tr     (* if b then c1 else c0   -> cb   wh*)  
                                                 (* cost cb' <= a cost cb + b   cost cb' <= cost (if b then ...) *) 
                                                 (* same as source *)
| LT_ifor_unroll: nat -> seq leak_i_tr -> leak_i_tr
| LT_icall_inline: nat -> nat -> nat -> leak_i_tr
(* lowering leak transformers *)
| LT_icondl : leak_e_i_tr -> leak_e_tr -> seq leak_i_tr -> seq leak_i_tr -> leak_i_tr
| LT_iwhilel :  leak_e_i_tr -> leak_e_tr -> seq leak_i_tr -> seq leak_i_tr -> leak_i_tr
| LT_icopn : leak_es_i_tr -> leak_i_tr
(* lowering assgn *)
| LT_ilmov1 : leak_i_tr
| LT_ilmov2 : leak_i_tr
| LT_ilmov3 : leak_i_tr
| LT_ilmov4 : leak_i_tr
| LT_ilinc : leak_e_es_tr -> leak_i_tr
| LT_ilcopn : leak_e_es_tr -> leak_i_tr
| LT_ilsc : leak_i_tr
| LT_ild : leak_i_tr
| LT_ildc : leak_i_tr
| LT_ildcn : leak_i_tr
| LT_ilmul : leak_es_i_tr -> leak_e_tr -> leak_i_tr
| LT_ileq : leak_e_es_tr -> leak_i_tr
| LT_illt : leak_e_es_tr -> leak_i_tr
| LT_ilif : leak_e_i_tr -> leak_e_tr -> leak_i_tr
| LT_ilea : leak_i_tr
| LT_ilfopn : leak_es_i_tr -> leak_e_es_tr -> leak_i_tr
| LT_ilds : leak_i_tr
| LT_ildus : leak_i_tr
| LT_ildiv : leak_i_tr -> leak_e_es_tr -> leak_i_tr
| LT_ilasgn : leak_i_tr.

Definition is_LT_ilds li := if li is LT_ilds then true else false.

(* Transformation from expression leakage to instruction leakage *)
Fixpoint leak_EI (stk : pointer) (lti : leak_e_i_tr) (le : leak_e) : seq leak_i :=
match lti, le with 
| LT_iconditionl lte, le => [:: Lopn (LSub [:: leak_E stk lte le; LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty]])]
| LT_iemptyl, le => [::]
end.

Fixpoint remove_leak (ls: seq leak_e) : seq leak_e :=
match ls with
| a :: l =>  List.tl l
| [::] => [::]
            end.

Fixpoint remove_last_leak (ls: seq leak_e) : seq leak_e :=
match ls with
| [::] => [::]
| [:: a] => [::]
| a :: l => a :: remove_last_leak l
end.

Fixpoint last_leak (ls : seq leak_e) : leak_e :=
match ls with 
| [::] => LEmpty
| [:: a] => a
| a :: l => last_leak l
end.

Section Leak_Equal.
Variable eq_leak : leak_e -> leak_e -> bool.

Fixpoint eq_leaks (les: seq leak_e) (les' : seq leak_e) : bool :=
match les, les' with 
| [::], [::] => true
| [::], _ => false
| a :: l, a' :: l' => (andb (eq_leak a a') (eq_leaks l l'))
| _, _ => false
end.

End Leak_Equal.

Fixpoint eq_leak (le le' : leak_e) : bool :=
match le, le' with
| LEmpty, LEmpty => true
| LIdx i, LIdx i' => if i == i' then true else false
| LAdr a , LAdr a' => if a == a' then true else false
| LSub l, LSub l' => eq_leaks eq_leak l l'
| _, _ => false
end. 

(* Transformation from expressions (seq of expression) leakage to instruction leakage *)
Fixpoint leak_ESI (stk : pointer) (lti : leak_es_i_tr) (les: seq leak_e) (les': seq leak_e) : seq leak_i :=
match lti with 
| LT_iopn5f_large => 
  ([:: Lopn (LSub [:: LSub [:: nth LEmpty les 1]; LSub [:: LEmpty]])] ++
   [:: Lopn (LSub [:: LSub ([::nth LEmpty les 0; LEmpty] ++ (remove_leak les)); LSub les'])])
| LT_iopn5f_other =>
  [:: Lopn (LSub [:: LSub les ; LSub les'])]
| LT_iaddcarryf ltes => 
  leak_ESI stk ltes (remove_last_leak les) 
     [:: LEmpty; get_nth_leak les' 0; LEmpty; LEmpty; LEmpty; get_nth_leak les' 1]
| LT_iaddcarry ltes =>  
   leak_ESI stk ltes les 
     [:: LEmpty; get_nth_leak les' 0; LEmpty; LEmpty; LEmpty; get_nth_leak les' 1]
| LT_ianone => 
  [:: Lopn (LSub [:: LSub les ; LSub les'])]
| LT_imul1 => 
  ([:: Lopn (LSub [:: LSub [:: nth LEmpty les 0]; LSub [:: LEmpty]])] ++
   [:: Lopn (LSub [:: LSub [:: nth LEmpty les 1; LEmpty]; 
              LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; nth LEmpty les' 0; nth LEmpty les' 1]])])
| LT_imul2 => 
  ([:: Lopn (LSub [:: LSub [:: nth LEmpty les 1]; LSub [:: LEmpty]])] ++
   [:: Lopn (LSub [:: LSub [:: nth LEmpty les 0; LEmpty]; 
              LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; nth LEmpty les' 0; nth LEmpty les' 1]])])
| LT_imul3 => 
  [:: Lopn (LSub [:: LSub les; 
              LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; nth LEmpty les' 0; nth LEmpty les' 1]])]
| LT_imul4 => 
  [:: Lopn (LSub [:: LSub les ; LSub les'])]
| LT_iemptysl => [::]
end.

Section Leak_I.

  Variable leak_I : pointer -> leak_i -> leak_i_tr -> seq leak_i.

  Definition leak_Is (stk : pointer) (lts : seq leak_i_tr) (ls : seq leak_i) : seq leak_i :=
    flatten (map2 (leak_I stk) ls lts).

  Definition leak_Iss (stk: pointer) (ltss : seq leak_i_tr) (ls : seq (seq leak_i)) : seq (seq leak_i) :=
    (map (leak_Is stk ltss) ls). 

End Leak_I.

Section Leak_Call.

Variable leak_Fun : funname -> seq leak_i_tr.

Definition dummy_lit := Lopn LEmpty.

Definition leak_assgn := 
(Lopn (LSub [:: LEmpty ; LEmpty])).

Definition get_empty_leak_seq (l : seq leak_e_tr) :=
(map (fun x => LEmpty) l).

Fixpoint leak_I (stk:pointer) (l : leak_i) (lt : leak_i_tr) {struct l} : seq leak_i :=
  match lt, l with
  | LT_iremove, _ => [::]
  | LT_ikeep, _ => [::l]
  | LT_ile lte, Lopn le   => [:: Lopn (leak_E stk lte le) ]
  | LT_icond lte ltt ltf, Lcond le b lti => 
    [:: Lcond (leak_E stk lte le) b (leak_Is leak_I stk (if b then ltt else ltf) lti) ]
  | LT_iwhile ltis lte ltis', Lwhile_true lts le lts' lw => 
    [:: Lwhile_true (leak_Is leak_I stk ltis lts)
                     (leak_E stk lte le)
                     (leak_Is leak_I stk ltis' lts')
                     (head dummy_lit (leak_I stk lw lt))]
  | LT_iwhile ltis lte ltis', Lwhile_false lts le => 
    [::Lwhile_false (leak_Is leak_I stk ltis lts)
                     (leak_E stk lte le)]
  | LT_icond_eval _b lts, Lcond _ b lti => (* _b should be equal b *)
    leak_Is leak_I stk lts lti
  | LT_icond_eval false lts, Lwhile_false lti le => 
    leak_Is leak_I stk lts lti
  | LT_ifor lte ltiss, Lfor le ltss => [:: Lfor (leak_E stk lte le)
                                                (leak_Iss leak_I stk ltiss ltss) ]
  | LT_icall _f lte lte', Lcall le (f, lts) le' => (* _f should be equal to f *)
    [:: Lcall (leak_E stk lte le)
              (f, (leak_Is leak_I stk (leak_Fun f) lts))
              (leak_E stk lte' le') ]
  | LT_ifor_unroll _n ltiss, Lfor le ltss => (* _n should be equal to size ltss *)
    flatten (map (fun l => leak_assgn :: l) (leak_Iss leak_I stk ltiss ltss))
  | LT_icall_inline nargs ninit nres, Lcall le (f, lts) le' => (* nargs = size le, nres = size le') *)
    map (fun x => (Lopn (LSub [:: x; LEmpty]))) (get_seq_leak_e le) ++ 
    nseq ninit (Lopn (LSub [:: LEmpty; LEmpty])) ++ 
    leak_Is leak_I stk (leak_Fun f) lts ++
    map (fun y => (Lopn (LSub [:: LEmpty; y]))) (get_seq_leak_e le')
 (* lowering *)
  | LT_icondl lti' lte ltt ltf, Lcond le b lti => 
     (leak_EI stk lti' le) ++ [:: Lcond (leak_E stk lte le) b (leak_Is leak_I stk (if b then ltt else ltf) lti) ]
  | LT_iwhilel lti lte ltis ltis', Lwhile_true lts le lts' lw => 
    [:: Lwhile_true ((leak_Is leak_I stk ltis lts) ++ (leak_EI stk lti le))
                     (leak_E stk lte le)
                     (leak_Is leak_I stk ltis' lts')
                     (head dummy_lit (leak_I stk lw lt))]
  | LT_iwhilel lti lte ltis ltis', Lwhile_false lts le => 
    [::Lwhile_false ((leak_Is leak_I stk ltis lts) ++ (leak_EI stk lti le)) (leak_E stk lte le)]
  | LT_icopn ltes, Lopn le => leak_ESI stk ltes (get_seq_leak_e (leak_E stk (LT_subi 0) le)) (get_seq_leak_e (leak_E stk (LT_subi 1) le))
  | LT_ilmov1, Lopn le => [:: Lopn (LSub [:: LSub [:: leak_E stk (LT_subi 0) le]; LSub [:: LEmpty]]) ; 
                              Lopn (LSub [:: LSub [:: LEmpty]; LSub [:: leak_E stk (LT_subi 1) le]])]
  | LT_ilmov2, Lopn le => [:: Lopn (LSub [:: LSub [::];
                                        LSub[:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le]])]
  | LT_ilmov3, Lopn le => [:: Lopn (LSub [:: LSub [::]; LSub [:: leak_E stk (LT_subi 1) le]])]
  | LT_ilmov4, Lopn le => [:: Lopn (LSub [:: LSub [:: leak_E stk (LT_subi 0) le]; 
                                             LSub [:: leak_E stk (LT_subi 1) le]])] 
  | LT_ilinc ltes, Lopn le => [:: Lopn (LSub [:: LSub (leak_ES stk ltes (leak_E stk (LT_subi 0) le)); 
                                            LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le]])]
  | LT_ilcopn ltes, Lopn le => [:: Lopn (LSub [:: LSub (leak_ES stk ltes (leak_E stk (LT_subi 0) le));
                                                       LSub [:: leak_E stk (LT_subi 1) le]])]
  | LT_ild, Lopn le => [:: Lopn (LSub [:: LSub[:: LEmpty]; 
                                      LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le]])]
  | LT_ildc, Lopn le => [:: Lopn (LSub [:: LSub[:: LEmpty; LEmpty]; 
                                       LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le]])]
  | LT_ildcn, Lopn le => [:: Lopn (LSub [:: LSub [:: LEmpty]; LSub [:: LEmpty]]);
                             Lopn (LSub [:: LSub [:: LEmpty; LEmpty]; 
                                            LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le]])]
  | LT_ileq ltes, Lopn le => [:: Lopn (LSub [:: LSub (leak_ES stk ltes (leak_E stk (LT_subi 0) le));
                                            LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le]])]
  | LT_illt ltes, Lopn le => [:: Lopn (LSub [:: LSub (leak_ES stk ltes (leak_E stk (LT_subi 0) le));
                                      LSub [:: LEmpty; leak_E stk (LT_subi 1) le; LEmpty; LEmpty; LEmpty]])]
  | LT_ilif lti le', Lopn le => 
    ((leak_EI stk lti (get_nth_leak (get_seq_leak_e (leak_E stk (LT_subi 0) le)) 0)) ++ 
    [:: Lopn (LSub [:: LSub [:: leak_E stk le' (leak_E stk (LT_subi 0) (leak_E stk (LT_subi 0) le));
                            (leak_E stk (LT_subi 1) (leak_E stk (LT_subi 0) le));
                (leak_E stk (LT_subi 2) (leak_E stk (LT_subi 0) le))]; LSub [:: leak_E stk (LT_subi 1) le]])])
  | LT_ilea, Lopn le => [:: Lopn (LSub [:: LSub [:: leak_lea_exp]; LSub [:: leak_E stk (LT_subi 1) le]])]
  | LT_ilsc, Lopn le => [:: Lopn (LSub [:: leak_E stk (LT_subi 1) (leak_E stk (LT_subi 1) leak_lea_exp); 
                                       LSub [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le]])]
  | LT_ilmul lest ltes, Lopn le =>  (leak_ESI stk lest (get_seq_leak_e (leak_E stk ltes (LSub [:: LEmpty; LEmpty])))
                                              [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le])
  | LT_ilfopn lest lte, Lopn le => (leak_ESI stk lest (leak_ES stk lte (leak_E stk (LT_subi 0) le)) 
                                             [:: LEmpty; LEmpty; LEmpty; LEmpty; LEmpty; leak_E stk (LT_subi 1) le])
  | LT_ilds, Lopn le => [:: Lopn (LSub [:: LSub [:: nth LEmpty (get_seq_leak_e (leak_E stk (LT_subi 0) le)) 0]; LSub[:: LEmpty]])]
  | LT_ildus, Lopn le => [:: Lopn (LSub [:: LSub [:: LEmpty]; LSub[:: LEmpty]])]
  | LT_ildiv lti ltes, Lopn le =>  
    if is_LT_ilds lti then 
      [:: Lopn (LSub [:: LSub [:: nth LEmpty (get_seq_leak_e (leak_E stk (LT_subi 0) le)) 0]; 
                        LSub[:: LEmpty]])] ++ 
      [:: Lopn (LSub [:: LSub [:: LEmpty; nth LEmpty (get_seq_leak_e (leak_E stk (LT_subi 0) le)) 0; 
                                 nth LEmpty (get_seq_leak_e (leak_E stk (LT_subi 0) le)) 1]; 
                        LSub (leak_ES stk ltes (leak_E stk (LT_subi 1) le))])]
    else [:: Lopn (LSub [:: LSub [:: LEmpty]; LSub[:: LEmpty]])]  ++ 
         [:: Lopn (LSub [:: LSub [:: LEmpty; nth LEmpty (get_seq_leak_e (leak_E stk (LT_subi 0) le)) 0; 
                                    nth LEmpty (get_seq_leak_e (leak_E stk (LT_subi 0) le)) 1]; 
                           LSub (leak_ES stk ltes (leak_E stk (LT_subi 1) le))])]
                                 
  | LT_ilasgn, Lopn le=>  [:: Lopn (LSub [:: (leak_E stk (LT_subi 0) le);
                                                        leak_E stk (LT_subi 1) le])]

 (*| LT_icompose lt1 lt2 => leak_I (leak_I l lt1) lt2*) (* le = LSub [:: l; l'] *)
                                            
  | _, _ => [:: l]
  end.

End Leak_Call.

Notation leak_c_tr := (seq leak_i_tr).

Definition leak_f_tr := seq (funname * leak_c_tr).

Section Leak_Call_Imp.

Variable Fs: leak_f_tr.

Definition leak_Fun (f: funname) : leak_c_tr := odflt [::] (assoc Fs f).

End Leak_Call_Imp.

Fixpoint leak_compile (stk : pointer) (lts: seq leak_f_tr) (lf: leak_fun) := 
match lts with 
| [::] => lf.2
| x :: xs => let r := (leak_Is (leak_I (leak_Fun x)) stk (leak_Fun x lf.1)
                   lf.2) in 
             leak_compile stk xs (lf.1, r)
end.

Fixpoint leak_compiles (stk: pointer) (ltss: seq (seq leak_f_tr)) (lf: leak_fun) :=
match ltss with 
| [::] => lf.2
| x :: xs => let r := leak_compile stk x lf in 
              leak_compiles stk xs (lf.1, r)
end.

(*Fixpoint trasform_cost (m:label_map) (l:label) (lt: leak_i_tr): label_map :=
match lt with 
 | LT_iremove => empty_label_map
 (*| LT_ikeep => empty_label_map *)
 | LT_ile lte => update_label_map m l
 | LT_icond ltis _ ltis' => let m1 := update_label_map m l in 
                            let m2 := transform_cost m1 l ltis in 
                            let m3 := tramform_cost m2 l ltis'
 | _ => empty_label_map
end.*)


(** Leakage for intermediate-level **)

Inductive leak_il : Type :=
| Lempty : leak_il
| Lopnl : leak_e -> leak_il
| Lcondl : leak_e -> bool -> leak_il.

Notation leak_funl := (funname * seq leak_il).

Definition leak_cl := seq leak_il.

Inductive leak_i_il_tr : Type :=
| LT_ilremove : leak_i_il_tr
| LT_ilkeep : leak_i_il_tr
| LT_ilkeepa : leak_i_il_tr
| LT_ilcond_0 : leak_e_tr -> seq leak_i_il_tr -> leak_i_il_tr (*c1 is empty*)
| LT_ilcond_0' : leak_e_tr -> seq leak_i_il_tr -> leak_i_il_tr (*c2 is empty*)
| LT_ilcond : leak_e_tr -> seq leak_i_il_tr -> seq leak_i_il_tr -> leak_i_il_tr (* c1 and c2 are not empty *)
| LT_ilwhile_c'0 : align -> seq leak_i_il_tr -> leak_i_il_tr
| LT_ilwhile_f : seq leak_i_il_tr -> leak_i_il_tr
| LT_ilwhile : seq leak_i_il_tr -> seq leak_i_il_tr -> leak_i_il_tr.

Section Leak_IL.

  Variable leak_i_iL : pointer -> leak_i ->  leak_i_il_tr -> seq leak_il.

  Definition leak_i_iLs (stk : pointer) (lts : seq leak_i_il_tr) (ls : seq leak_i) : seq leak_il :=
    flatten (map2 (leak_i_iL stk) ls lts).

  Fixpoint ilwhile_c'0 (stk: pointer) (lti : seq leak_i_il_tr) (li : leak_i) : seq leak_il :=
    match li with 
      | Lwhile_false lis le => leak_i_iLs stk lti lis ++ [:: Lcondl le false]
      | Lwhile_true lis le lis' li' => leak_i_iLs stk lti lis ++ [:: Lcondl le true] ++
                                       ilwhile_c'0 stk lti li'
      | _ => [::]
    end.

  Fixpoint ilwhile (stk : pointer) (lts : seq leak_i_il_tr) (lts' : seq leak_i_il_tr) (li : leak_i) : seq leak_il :=
    match li with 
      | Lwhile_false lis le => leak_i_iLs stk lts lis ++ [:: Lcondl le false]
      | Lwhile_true lis le lis' li' => 
        leak_i_iLs stk lts lis ++ [:: Lcondl le true] ++ leak_i_iLs stk lts' lis' ++ [:: Lempty] ++ ilwhile stk lts lts' li'
      | _ => [::]
    end.

End Leak_IL.

(* Computes the leakage depending on alignment *) 
Definition get_align_leak_il a : seq leak_il :=
  match a with 
  | NoAlign => [::]
  | Align => [:: Lempty]
  end.

Fixpoint leak_i_iL (stk:pointer) (li : leak_i) (l : leak_i_il_tr) {struct li} : seq leak_il :=
match l, li with 
| LT_ilremove, _ => [:: Lempty]
| LT_ilkeepa, Lopn le => [:: Lopnl (LSub (map (fun x => LSub [:: x]) (get_seq_leak_e le)))]
| LT_ilkeep, Lopn le => [:: Lopnl le]
| LT_ilcond_0 lte lti, Lcond le b lis => [:: Lcondl (leak_E stk lte le) b] ++ 
  (if b then [::] else leak_i_iLs leak_i_iL stk lti lis ++ [:: Lempty])
| LT_ilcond_0' lte lti, Lcond le b lis => [:: Lcondl (leak_E stk lte le) (negb b)] ++ 
  (if (negb b) then [::] else leak_i_iLs leak_i_iL stk lti lis ++ [:: Lempty])
| LT_ilcond lte lti lti', Lcond le b lis => 
  [:: Lcondl (leak_E stk lte le) b] ++ if b then leak_i_iLs leak_i_iL stk lti lis ++ [:: Lempty]
                           else leak_i_iLs leak_i_iL stk lti' lis ++ [:: Lempty]
| LT_ilwhile_c'0 a lti, _ => get_align_leak_il a ++ [:: Lempty & ilwhile_c'0 leak_i_iL stk lti li]
| LT_ilwhile_f lti, Lwhile_false lis le => leak_i_iLs leak_i_iL stk lti lis
| LT_ilwhile lti lti', _ => [:: Lempty] ++ ilwhile leak_i_iL stk lti lti' li 
| _, _ => [::]
end.

Definition leak_f_lf_tr := seq (funname * seq leak_i_il_tr).

Section Leak_Call_Imp_L.

Variable Fs: leak_f_lf_tr.

Definition leak_Fun_L (f: funname) : seq leak_i_il_tr := odflt [::] (assoc Fs f).

End Leak_Call_Imp_L.

(** Leakage for assembly-level **)

Inductive leak_asm : Type :=
| Laempty
| Lacond of bool (* bool represents the condition in conditional jump *)
| Laop of seq pointer.

(* Extracts the sequence of pointers from leak_e *)
Fixpoint leak_e_asm (l : leak_e) : seq pointer :=
match l with 
| LEmpty => [::]
| LIdx i => [::]
| LAdr p => [:: p]
| LSub l => flatten (map leak_e_asm l)
end.

(* Transforms leakage for intermediate langauge to leakage for assembly *)
Definition leak_i_asm (l : leak_il) : leak_asm :=
match l with 
| Lempty => Laempty
| Lopnl le => Laop (leak_e_asm le)
| Lcondl le b => Lacond b
end.

Definition leak_compile_prog (stk: pointer) (ltss: leak_f_lf_tr * (seq leak_f_tr * (seq (seq leak_f_tr) * seq leak_f_tr))) (lf: leak_fun) : seq leak_il :=
let r := leak_compile stk ltss.2.1 lf in 
let rs := leak_compiles stk ltss.2.2.1 (lf.1, r) in 
leak_i_iLs leak_i_iL stk (leak_Fun_L ltss.1 lf.1) (leak_compile stk ltss.2.2.2 (lf.1, rs)). 

Definition leak_compile_x86 (stk: pointer) (ltss: leak_f_lf_tr * (seq leak_f_tr * (seq (seq leak_f_tr) * seq leak_f_tr))) (lf: leak_fun) : seq leak_asm := 
let r := leak_compile_prog stk ltss lf in
map (fun x=> leak_i_asm x) r.



(* ------------------------------------------------------------------- *)
(* Syntaxic transformation of the cost                                 *)

Module CmpLbl.

  Definition cmp_label_elem (l1 l2: label_elem) := 
    match l1, l2 with
    | LblF f1, LblF f2 => gcmp f1 f2
    | LblF _ , _       => Lt
    | _      , LblF _  => Gt
    | LblN n1, LblN n2 => gcmp n1 n2
    | LblN _ , _       => Lt
    | _      , LblN _  => Gt
    | LblB b1, LblB b2 => gcmp b1 b2
    end.

  Instance LabelElemO : Cmp cmp_label_elem.
  Proof.
    constructor.
    + by move=> [f1 | n1 | b1] [f2 | n2 | b2] //=; apply cmp_sym.
    + move=> [yf | yn | yb] [xf | xn | xb] //= [zf | zn | zb] c //=;
      try (by apply cmp_ctrans ||
           by apply ctrans_Lt  ||
           by apply ctrans_Gt  ).
    by move=> [f1 | n1 | b1] [f2 | n2 | b2] //= h; rewrite (cmp_eq h). 
  Qed.
   
  Definition t := [eqType of lbl].

  Definition cmp (l1 l2: lbl) := 
    lex (cmp_list cmp_label_elem) Nat.compare l1 l2.

  Instance cmpO : Cmp cmp.
  Proof.  
    apply LexO; [apply ListO; apply LabelElemO | apply natO].
  Qed.

End CmpLbl.

Record scost := 
  { sc_divfact : nat
  ; sc_lbl     : lbl }. (* source label *)

Definition scost_beq sc1 sc2 := 
 (sc1.(sc_divfact) == sc2.(sc_divfact)) && 
 (sc1.(sc_lbl) == sc2.(sc_lbl)).

Lemma scost_eq_axiom : Equality.axiom scost_beq.
Proof.
  move=> [d1 l1] [d2 l2]; rewrite /scost_beq.
  case: eqP => /= [-> | h]; last by constructor => -[].
  by case: eqP => /= [-> | h]; constructor => // -[].
Qed.

Definition scost_eqMixin     := Equality.Mixin scost_eq_axiom.
Canonical  scost_eqType      := Eval hnf in EqType scost scost_eqMixin.

Definition prefix_lbl (pre: list label_elem) (l:lbl) := 
  (l.1 ++ pre, l.2).

Definition has_prefix pre (l:lbl) := 
   drop (size l.1 - size pre) l.1 == pre.

Definition drop_lbl n (l:lbl) :=
  (take (size l.1 - n) l.1, l.2).

Lemma prefix_lbl_drop pre l : has_prefix pre l -> 
  l = prefix_lbl pre (drop_lbl (size pre) l).
Proof.
  rewrite /prefix_lbl /has_prefix /drop_lbl => /eqP.
  by case: l => [l n] /= {2}<-; rewrite cat_take_drop.
Qed.

(* FIXME: move this in utils.v *)
Lemma catsI T : right_injective (@cat T).
Proof.
by move=> xs ys zs /(congr1 (drop (size xs))); rewrite !drop_size_cat.
Qed.

Lemma catIs T : left_injective (@cat T).
Proof.
move=> xs ys zs /(congr1 (rotr (size xs))).
by rewrite !rotr_size_cat => /catsI.
Qed.

Lemma prefix_lbl_inj pre l1 l2: prefix_lbl pre l1 = prefix_lbl pre l2 -> l1 = l2.
Proof. by case: l1 l2 => l1 n1 [l2 n2] [] /catIs -> ->. Qed.

Lemma drop_eq pre l l1: 
  drop (size l.1 - size pre) l.1 = pre ->
  (prefix_lbl pre l1 == l) = (drop_lbl (size pre) l == l1).
Proof.
  rewrite /prefix_lbl /drop_lbl; case: l l1 => [l n] [l1 n1] /=.
  case: eqP => [[] <- <- | hne].
  + by rewrite size_cat addnK take_size_cat ?eqxx.
  case: eqP => [[] h1 h2 h| //]; elim hne.
  by rewrite h2 -h -h1 cat_take_drop.
Qed.

Lemma drop_prefix_lbl pre l: 
  drop (size (prefix_lbl pre l).1 - size pre) (prefix_lbl pre l).1 = pre.
Proof. by rewrite /prefix_lbl /= size_cat addnK drop_size_cat. Qed.

Lemma drop_lbl_prefix_lbl pre l : drop_lbl (size pre) (prefix_lbl pre l) = l.
Proof. by rewrite /prefix_lbl /drop_lbl /= size_cat addnK take_size_cat //; case: l. Qed.


(* Provide map of lbl *)

Module Sm.

Module Ml := Mmake CmpLbl.

Definition t := Ml.t scost.

Definition empty : t := Ml.empty scost.

Definition get (m:t) (tl:lbl) : option scost := Ml.get m tl.

Definition set (m:t) (tl:lbl) (sl:lbl) divfact : t :=
  Ml.set m tl {| sc_divfact := divfact; sc_lbl := sl |}.

(* Merging map *)
Definition merge_scost (_:lbl) (o1 o2 : option scost) := 
  match o1, o2 with
  | None, None => None
  | Some o, None | _ , Some o => Some o
  end.

Definition merge (m1 m2: t) : t := 
  Ml.map2 merge_scost m1 m2.

Definition disjoint (m1 m2: t) := 
  forall l, get m1 l <> None -> get m2 l = None.

(* m -> l -> c *)
(* prefix pre m -> (pre::l) -> c 
                   (l.1 ++ pre, l.2) -> c *)
Definition prefix (pre: list label_elem) (m:t) : t := 
  Ml.fold (fun lbl sc m => Ml.set m (prefix_lbl pre lbl) sc) m empty.

Definition rm_prefix n (m:t) : t := 
  Ml.fold (fun lbl sc m => Ml.set m (drop_lbl n lbl) sc) m empty.

Definition compose (m1 m2: t) : t :=
  Ml.fold (fun lbl2 sc2 m3 => 
     match get m1 sc2.(sc_lbl) with
     | None => m3
     | Some sc1 => set m3 lbl2 sc1.(sc_lbl) (sc1.(sc_divfact) * sc2.(sc_divfact))
     end) m2 empty.

Definition interp (sc:label_map) (m:t) : label_map := 
  fun l => 
    match get m l with
    | Some c => divn (sc c.(sc_lbl)) c.(sc_divfact)
    | None => 0
    end.

(* Properties *)
Lemma setP m x y sl divfact : 
  get (set m x sl divfact) y = 
   if x == y then Some {| sc_divfact := divfact; sc_lbl := sl |} 
   else get m y.
Proof. by rewrite /get /set Ml.setP. Qed.

Lemma setP_eq m x sl divfact : 
  get (set m x sl divfact) x = Some {| sc_divfact := divfact; sc_lbl := sl |}.
Proof. by rewrite setP eqxx. Qed.

Lemma setP_neq m x y sl divfact : 
  x <> y ->
  get (set m x sl divfact) y = get m y.
Proof. by move=> /eqP/negbTE h ;rewrite setP h. Qed.

Lemma disjoint_sym m1 m2: 
  disjoint m1 m2 -> disjoint m2 m1.
Proof.
  move=> h l; have := h l.
  by case: (get m1) => // c1; case: (get m2) => // c2 ->.
Qed.

Lemma mergeP m1 m2 l :
  get (merge m1 m2) l = merge_scost l (get m1 l) (get m2 l).
Proof. by rewrite /get Ml.map2P. Qed.

Lemma assoc_get (m:t) l : assoc (Ml.elements m) l = get m l.
Proof.
  rewrite /get.
  case heq : assoc => [sc | ].
  + by have /Ml.elementsP /= -> := assoc_mem heq.
  case heqg : (Ml.get m l) => [sc | //].
  by have /introT /(_ heqg) /assocP -/(_ (Ml.elementsU m)):= Ml.elementsP (l,sc) m; rewrite heq.
Qed.

Lemma prefixP pre m l : 
  get (prefix pre m) l = 
   if drop (size l.1 - size pre) l.1 == pre then
     get m (drop_lbl (size pre) l)
   else None.
Proof.
  rewrite /prefix Ml.foldP.
  suff : forall m0, 
    get
      (foldl (λ (a : Ml.t scost) (kv : Ml.K.t * scost), Ml.set a (prefix_lbl pre kv.1) kv.2) m0
      (Ml.elements m)) l =
    if drop (size l.1 - size pre) l.1 == pre then
       match assoc (Ml.elements m) (drop_lbl (size pre) l) with
       | Some sc => Some sc
       | None => get m0 l
       end
    else get m0 l.
  + by move=> ->; rewrite /get Ml.get0 assoc_get /get; case: Ml.get.
  elim: Ml.elements (Ml.elementsU m) => /=.
  + by move=> *;case:eqP.
  move=> -[l1 sc1] es hrec /andP [he hu] m0.
  rewrite hrec // /get; case: eqP => hpre.
  + case heq: assoc => [sc' | ].
    + case: eqP => // ?; subst l1.
      by rewrite (assoc_mem_dom' heq) in he.
    by rewrite Ml.setP (drop_eq _ hpre) /=; case: eqP.
  rewrite Ml.setP; case: eqP => // h.
  by move: hpre; rewrite -h drop_prefix_lbl.
Qed.

Lemma get_prefix_lbl pre m l : get (prefix pre m) (prefix_lbl pre l) = get m l.
Proof. by rewrite prefixP drop_prefix_lbl eqxx drop_lbl_prefix_lbl. Qed.

Lemma composeP m1 m2 l : 
  get (compose m1 m2) l = 
    match get m2 l with
    | Some sc2 =>
      match get m1 sc2.(sc_lbl) with
      | Some sc1 => Some {| sc_lbl := sc1.(sc_lbl); sc_divfact := sc1.(sc_divfact) * sc2.(sc_divfact) |}
      | None => None
      end
    | None => None
    end.
Proof.
  rewrite /compose Ml.foldP.
  suff : forall m0,
     get (foldl
       (λ (a : t) (kv : Ml.K.t * scost),
          match get m1 (sc_lbl kv.2) with
          | Some sc1 => set a kv.1 (sc_lbl sc1) (sc_divfact sc1 * sc_divfact kv.2)
          | None => a
          end) m0 (Ml.elements m2)) l =
     match assoc (Ml.elements m2) l with
     | Some sc2 =>
        match get m1 (sc_lbl sc2) with
        | Some sc1 => Some {| sc_divfact := sc_divfact sc1 * sc_divfact sc2; sc_lbl := sc_lbl sc1 |}
        | None => get m0 l
        end
     | None => get m0 l
     end.
  + by move => ->; rewrite /get Ml.get0 assoc_get /get; case: Ml.get.
  elim: Ml.elements (Ml.elementsU m2) => //= -[l2 sc2] es hrec /andP /= [he hu] m0.
  rewrite hrec // /get; case: eqP => [-> | hne] /= {hrec}; case heq: assoc => [sc' | ].
  + by rewrite (assoc_mem_dom' heq) in he.
  + by case: (Ml.get m1) => // sc1; rewrite Ml.setP_eq.
  + by case: (Ml.get m1) => //; case: (Ml.get m1) => // ?; rewrite Ml.setP_neq // eq_sym; apply /eqP.
  by case: (Ml.get m1) => // ?; rewrite Ml.setP_neq // eq_sym; apply /eqP.
Qed.

(*Definition valid (sc:label_map) m (tc:label_map) := 
  forall l, tc l <= interp sc m l. *)
 
Lemma interp_compose sc m1 m2 l : 
  interp sc (compose m1 m2) l = interp (interp sc m1) m2 l.
Proof.
  rewrite /interp composeP.
  case: (get m2) => // sc2.
  case: (get m1) => [sc1 /= | ]; last by rewrite div0n.
  by rewrite -divnMA.
Qed.

(* sc <= sc' -> interp sc m <= interp sc' m. *)

End Sm.

Section Transform_Cost_c.

Variable transform_cost_i : leak_i_tr -> Sm.t -> lbl -> lbl -> nat -> Sm.t * lbl. 

Fixpoint transform_cost_c (lt:seq leak_i_tr) (m:Sm.t) (tl:lbl) (sl:lbl) (divfact:nat) : Sm.t * lbl :=
match lt with
 | [::] => (m, next_lbl tl)
 | lti :: lt => 
   let (m1, ntl) := transform_cost_i lti m tl sl divfact in 
   transform_cost_c lt m1 ntl (next_lbl sl) divfact
end.

Variable (lt:seq leak_i_tr).
 
Fixpoint transform_cost_unroll n m tl sl divfact divfact_in := 
  match n with
  | 0 => (m, tl)
  | S n => 
    let m := Sm.set m tl sl divfact in
    let (m,tl) := transform_cost_c lt m (next_lbl tl) (lbl_for sl) divfact_in in
    transform_cost_unroll n m tl sl divfact divfact_in
  end.

End Transform_Cost_c.
   
Section Transform_Cost_i.

Variable transform_cost_f : funname -> Sm.t * lbl. (* started with tl = ([LblF fn], 0) *)

Fixpoint transform_cost_i (lt:leak_i_tr) (m:Sm.t) (tl:lbl) (sl:lbl) divfact : Sm.t * lbl :=
  match lt with 
  | LT_ikeep => 
    (* We assume it is used only for base instruction.
       It is not true for inlining so fix it *)
    (Sm.set m tl sl divfact, next_lbl tl)

  | LT_ile _ => 
    (Sm.set m tl sl divfact, next_lbl tl)

  | LT_icond _ lt1 lt2 =>
    (* sl: if e then c1 else c2  ---> tl: (if e' then c1' else c2'); *)
    let  m     := Sm.set m tl sl divfact in
    let (m, _) := transform_cost_c transform_cost_i lt1 m (lbl_t tl) (lbl_t sl) divfact in
    let (m, _) := transform_cost_c transform_cost_i lt2 m (lbl_f tl) (lbl_f sl) divfact in
    (m, next_lbl tl)

  | LT_iwhile lt1 _ lt2 =>
    let  m     := Sm.set m tl sl divfact in
    let (m, _) := transform_cost_c transform_cost_i lt1 m (lbl_f tl) (lbl_f sl) divfact in
    let (m, _) := transform_cost_c transform_cost_i lt2 m (lbl_t tl) (lbl_t sl) divfact in
    (m, next_lbl tl)

  | LT_ifor _ lt1 =>
    let  m     := Sm.set m tl sl divfact in
    let (m, _) := transform_cost_c transform_cost_i lt1 m (lbl_for tl) (lbl_for sl) divfact in
    (m, next_lbl tl)

  | LT_icall fn _ _ => 
    let m := Sm.set m tl sl divfact in
    let (mf, _) := transform_cost_f fn in
    let mf := Sm.prefix (LblN tl.2::tl.1) m in
    let m  := Sm.merge m mf in
    (m, next_lbl tl)

  | LT_iremove => 
    (m, tl)
 
  | LT_icond_eval b ltb => 
    transform_cost_c transform_cost_i ltb m tl (lbl_b b sl) divfact 

  | LT_ifor_unroll n lt => 
    transform_cost_unroll transform_cost_i lt n m tl sl divfact (n * divfact)

  | LT_icall_inline nargs ninit nres => 
    (m, tl) (* FIXME *)

  | LT_icondl lei lte lt1 lt2 =>
    (m, tl) (* FIXME *)

  | LT_iwhilel lei lte lt1 lt2 =>
    (* while c1 {e} c2  
       while c1'; b = e' { b } c2' *)
    (m, tl) (* FIXME *)

  | LT_icopn lesi => 
    (m, tl) (* FIXME *)

  | LT_ilmov1 => 
    (* sl:i --->    tl:i1; tl': i2; next_lbl tl' *)
    let  m   := Sm.set m tl sl divfact in 
    let  tl := next_lbl tl in
    let  m  := Sm.set m tl sl divfact in 
    (m, next_lbl tl)

  | LT_ilmov2 | LT_ilmov3 | LT_ilmov4 =>
    (m, tl) (* FIXME *)

  | LT_ilinc lte | LT_ilcopn lte =>
    (m, tl) (* FIXME *)

  | LT_ilsc | LT_ild | LT_ildc | LT_ildcn => 
    (m, tl) (* FIXME *)
  | LT_ilmul ltes lte => 
    (m, tl) (* FIXME *)
  | LT_ileq ltes | LT_illt ltes => 
    (m, tl) (* FIXME *)
  | LT_ilif ltei lte => 
    (m, tl) (* FIXME *)
  | LT_ilea => 
    (m, tl) (* FIXME *)
  | LT_ilfopn ltesi ltes =>
    (m, tl) (* FIXME *)
  | LT_ilds | LT_ildus =>
    (m, tl) (* FIXME *)

  | LT_ildiv lti ltes => 
    (m, tl) (* FIXME *)
  | LT_ilasgn => 
    (m, tl) (* FIXME *)
  end.

(*
Lemma transform_cost_i_merge : 
  transform_cost_i lt m tl sl divfact =
  Sl.merge m (transform_cost_i lt Sm.empty tl sl divfact).

Lemma transform_ok lt l : 
  wf lt l ->
  cost (leak_I lt l) = interp (cost l) (transform_cost lt).

*)

End Transform_Cost_i.

