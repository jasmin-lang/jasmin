From mathcomp Require Import all_ssreflect.
Require Import ZArith var expr type.

Delimit Scope expr_scope with E.
Delimit Scope lval_scope with L.
Delimit Scope prog_scope with P.

(* ----------------------------------------------------------- *)
(* Expression                                                  *)

Notation "~~ e" := (Pnot e) : expr_scope.
Notation "x .[ n ]" := (Pget x n) : expr_scope.
Notation load := Pload. 

Notation "e1 && e2" := (Papp2 Oand e1 e2) : expr_scope.
Notation "e1 || e2" := (Papp2 Oor  e1 e2) : expr_scope.
Notation "e1 + e2"  := (Papp2 Oadd e1 e2) : expr_scope.
Notation "e1 - e2"  := (Papp2 Osub e1 e2) : expr_scope.
Notation "e1 * e2"  := (Papp2 Omul e1 e2) : expr_scope.
Notation "e1 == e2" := (Papp2 Oeq  e1 e2) : expr_scope.
Notation "e1 != e2" := (Papp2 Oneq e1 e2) : expr_scope.
Notation "e1 < e2"  := (Papp2 Olt  e1 e2) : expr_scope.
Notation "e1 <= e2" := (Papp2 Ole  e1 e2) : expr_scope.
Notation "e1 > e2"  := (Papp2 Ogt  e1 e2) : expr_scope.
Notation "e1 >= e2" := (Papp2 Oge  e1 e2) : expr_scope.

(* ----------------------------------------------------------- *)
(* lval                                                        *) 

Arguments Lmem _ _%E.
Arguments Laset _ _%E.
Arguments Lnone _%positive.

Notation "'#_'" := Lnone (at level 0): lval_scope. 
Notation "'__'" := (#_ 1)%L (at level 200): lval_scope. 
Notation "x .[ n ]" := (Laset x n) : lval_scope. 
Notation store := Lmem.

(* ----------------------------------------------------------- *)
(* Instruction                                                 *) 

Arguments MkI _%positive _%P.

Definition mki : instr_r -> instr := MkI 1%positive.

Coercion mki : instr_r >-> instr.

Notation "i ':@' x" := (MkI i x%P) (at level 0, x at level 200): prog_scope.

(* Cassign *)
Notation "x ::= e" := (Cassgn x%L AT_keep e%E)   (at level 70) : prog_scope.
Notation "x :r= e" := (Cassgn x%L AT_rename e%E) (at level 70) : prog_scope.
Notation "x :i= e" := (Cassgn x%L AT_inline e%E) (at level 70) : prog_scope.

(* Copn *)
Arguments Copn _%L _ _%E.
 
Notation " x := ! e" := 
  (Copn (Cons lval x%L nil) Olnot (Cons pexpr e nil))
  (at level 70) : prog_scope. 

Notation "x := e1 ^ e2" := 
  (Copn (Cons lval x%L nil) Oxor 
        (Cons pexpr e1%E (Cons pexpr e2%E nil)))
  (at level 70, e1 at level 0, e2 at level 0) : prog_scope. 

Notation "x := e1 & e2" := 
  (Copn (Cons lval x%L nil) Oland 
        (Cons pexpr e1%E (Cons pexpr e2%E nil)))
  (at level 70, e1 at level 0, e2 at level 0) : prog_scope. 

Notation "x := e1 | e2" := 
  (Copn (Cons lval x%L nil) Olor 
        (Cons pexpr e1%E (Cons pexpr e2%E nil)))
  (at level 70, e1 at level 0, e2 at level 0) : prog_scope. 

Notation "x := e1 << e2" := 
  (Copn (Cons lval x%L nil) Olsl
        (Cons pexpr e1%E (Cons pexpr e2%E nil)))
  (at level 70, e1 at level 0, e2 at level 0) : prog_scope. 

Notation "x := e1 >> e2" := 
  (Copn (Cons lval x%L nil) Olsr
        (Cons pexpr e1%E (Cons pexpr e2%E nil)))
  (at level 70, e1 at level 0, e2 at level 0) : prog_scope. 

Notation "x := e1 ?  e2 : e3 " := 
  (Copn (Cons lval x%L nil) Oif 
        (Cons pexpr e1%E (Cons pexpr e2%E (Cons pexpr e3%E nil))))
   (at level 70, e1 at level 0, e2 at level 0, e3 at level 200) : prog_scope. 

Notation "x := e1 * e2" := 
  (Copn (Cons lval x%L nil) Omuli 
        (Cons pexpr e1%E (Cons pexpr e2%E nil)))
  (at level 70, e1 at level 0, e2 at level 0) : prog_scope.

Notation "'[p' x , y ] := e1 * e2" := 
  (Copn (Cons lval x%L (Cons lval y%L nil)) Omulu 
        (Cons pexpr e1%E (Cons pexpr e2%E nil)))
  (at level 70, e1 at level 0, e2 at level 0) : prog_scope. 


Notation "'[p' c1 , x ] := '++' ( e1 , e2 , c2 )" := 
  (Copn (Cons lval c1%L (Cons lval x%L nil)) Oaddcarry
        (Cons pexpr e1%E (Cons pexpr e2%E (Cons pexpr c2 nil))))
  (at level 70) : prog_scope.

Notation "'[p' c , x ] := '++' ( e1 , e2 ) " := 
  ([p c , x ] := ++(e1, e2, false))%P
  (at level 70) : prog_scope.

Notation " x := '++' ( e1 , e2 )" := 
  ([p __ , x ] := ++(e1, e2))%P
  (at level 70) : prog_scope.

Notation "'[p' c1 , x ] := '--' ( e1 , e2 , c2 )" := 
  (Copn (Cons lval c1%L (Cons lval x%L nil)) Oaddcarry
        (Cons pexpr e1%E (Cons pexpr e2%E (Cons pexpr c2 nil))))
  (at level 70) : prog_scope.

Notation "'[p' c , x ] := '--' ( e1 , e2 ) " := 
  ([p c , x ] := --(e1, e2, false))%P
  (at level 70) : prog_scope.

Notation " x := '--' ( e1 , e2 )" := 
  ([p __ , x ] := --(e1, e2))%P
  (at level 70) : prog_scope.

(* Sequence of instructions *)

Notation "{ }" :=  (Nil instr) : prog_scope.

Notation "{:: i }" :=  (Cons instr i%P (Nil instr)) (at level 0): prog_scope.

Notation "{ x1 ; x2 ; .. ; xn }" :=  
  (Cons instr x1%P (Cons instr x2%P .. (Cons instr xn%P (Nil instr)) ..))
  (at level 0, format "'[v  ' { '/' x1 ; '/' x2 ; '/' .. ; '/' xn } ']'") : prog_scope.

Notation "'If' e 'then' c1 'else' c2" := 
  (Cif e%E c1%P c2%P)
  (at level 200, right associativity, format
      "'[v   ' 'If'  e  'then' '/' c1 '/' 'else' '/' c2 ']'") : prog_scope.

Notation "'If' e 'then' c1" := 
  (Cif e%E c1%P (Nil instr))
  (at level 200, right associativity, format
      "'[v   ' 'If'  e  'then' '/' c1 ']'") : prog_scope.

Notation "'While' e 'do' c" := 
  (Cwhile e%E c%P)
  (at level 200, right associativity, format
      "'[v   ' 'While'  e  'do' '/' c ']'") : prog_scope.

Notation "'For' i 'from' e1 'to' e2 'do' c" := 
  (Cfor i (@pair _ pexpr (@pair dir pexpr UpTo e1%E) e2%E) c)
  (at level 200, right associativity, format
      "'[v   ' 'For'  i  'from'  e1  'to'  e2  'do' '/' c ']'") : prog_scope.

Notation "'For' i 'from' e2 'downto' e1 'do' c" := 
  (Cfor i (@pair _ pexpr (@pair dir pexpr DownTo e1%E) e2%E) c)
  (at level 200, right associativity, format
      "'[v   ' 'For'  i  'from'  e2  'downto'  e1  'do' '/' c ']'") : prog_scope.

(* FIXME Notation for Ccall *)


(*
Open Scope string_scope.

Notation y := ((VarI (Var (sarr 4) "y") 1%positive)).
Notation cf := ((VarI (Var sbool "cf") 1%positive)).
Notation add1 := ((VarI (Var sword "add1") 1%positive)).
Notation add0 := ((VarI (Var sword "add0") 1%positive)).
Notation x := ((VarI (Var (sarr 4) "x") 1%positive)).
Notation i := ((VarI (Var sword "i") 1%positive)).
Notation ya := ((VarI (Var (sarr 4) "ya") 1%positive)).

Open Scope prog_scope.
Open Scope Z_scope.

Check (x := x ? (x + x) : x).

Definition program := [::
  ("add",
  MkFun 2%positive [:: x; ya] {
  1 :@ y.[i] ::= 0;
  2 :@ For i from 0 to 4 do {::
  3 :@   y.[i] ::= 0 
       };
  If x then {:: x ::= x }
  }%P
  [::])].

Print program.

Definition program1 := [::
  ("add",
  MkFun 2%positive [:: x; ya] {
  y.[i] ::= 0;
  [p cf , x] := ++(x,x,false);
  [p cf , x] := ++(x,x,cf);
  For i from 0 to 4 do {:: y.[i] ::= 0 }
  }%P
  [::])].


*)