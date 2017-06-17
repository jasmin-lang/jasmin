From mathcomp Require Import all_ssreflect.
Require Import expr.

Delimit Scope expr_scope with E.
Delimit Scope lval_scope with L.
Delimit Scope prog_scope with P.

(* ----------------------------------------------------------- *)
(* Expression                                                  *)

Notation "~~ e" := (Papp1 Onot e) : expr_scope.
Notation "~! e"  := (Papp1 Olnot e) (at level 35, right associativity) : expr_scope.
Notation "x .[ n ]" := (Pget x n) : expr_scope.
Notation load := Pload. 

Notation "e1 && e2" := (Papp2 Oand e1 e2) : expr_scope.
Notation "e1 || e2" := (Papp2 Oor  e1 e2) : expr_scope.

Notation "e1 +i e2"  := (Papp2 (Oadd Op_int) e1 e2) (at level 50, left associativity) : expr_scope.
Notation "e1 -i e2"  := (Papp2 (Osub Op_int) e1 e2) (at level 50, left associativity) : expr_scope.
Notation "e1 *i e2"  := (Papp2 (Omul Op_int) e1 e2) (at level 40, left associativity) : expr_scope.

Notation "e1 +w e2"  := (Papp2 (Oadd Op_w) e1 e2) (at level 50, left associativity) : expr_scope.
Notation "e1 -w e2"  := (Papp2 (Osub Op_w) e1 e2) (at level 50, left associativity) : expr_scope.
Notation "e1 *w e2"  := (Papp2 (Omul Op_w) e1 e2) (at level 40, left associativity) : expr_scope.

Notation "e1 ==i e2" := (Papp2 (Oeq  Cmp_int) e1 e2) (at level 70, no associativity) : expr_scope.
Notation "e1 !=i e2" := (Papp2 (Oneq Cmp_int) e1 e2) (at level 70, no associativity) : expr_scope.
Notation "e1 <i e2"  := (Papp2 (Olt  Cmp_int) e1 e2) (at level 70, no associativity) : expr_scope.
Notation "e1 <=i e2" := (Papp2 (Ole  Cmp_int) e1 e2) (at level 70, no associativity) : expr_scope.
Notation "e1 >i e2"  := (Papp2 (Ogt  Cmp_int) e1 e2) (at level 70, no associativity) : expr_scope.
Notation "e1 >=i e2" := (Papp2 (Oge  Cmp_int) e1 e2) (at level 70, no associativity) : expr_scope.
                               
Notation "e1 ==u e2" := (Papp2 (Oeq  Cmp_uw) e1 e2) (at level 70, no associativity) : expr_scope.
Notation "e1 !=u e2" := (Papp2 (Oneq Cmp_uw) e1 e2) (at level 70, no associativity) : expr_scope.
Notation "e1 <u e2"  := (Papp2 (Olt  Cmp_uw) e1 e2) (at level 70, no associativity) : expr_scope.
Notation "e1 <=u e2" := (Papp2 (Ole  Cmp_uw) e1 e2) (at level 70, no associativity) : expr_scope.
Notation "e1 >u e2"  := (Papp2 (Ogt  Cmp_uw) e1 e2) (at level 70, no associativity) : expr_scope.
Notation "e1 >=u e2" := (Papp2 (Oge  Cmp_uw) e1 e2) (at level 70, no associativity) : expr_scope.
                               
Notation "e1 ==s e2" := (Papp2 (Oeq  Cmp_sw) e1 e2) (at level 70, no associativity) : expr_scope.
Notation "e1 !=s e2" := (Papp2 (Oneq Cmp_sw) e1 e2) (at level 70, no associativity) : expr_scope.
Notation "e1 <s e2"  := (Papp2 (Olt  Cmp_sw) e1 e2) (at level 70, no associativity) : expr_scope.
Notation "e1 <=s e2" := (Papp2 (Ole  Cmp_sw) e1 e2) (at level 70, no associativity) : expr_scope.
Notation "e1 >s e2"  := (Papp2 (Ogt  Cmp_sw) e1 e2) (at level 70, no associativity) : expr_scope.
Notation "e1 >=s e2" := (Papp2 (Oge  Cmp_sw) e1 e2) (at level 70, no associativity) : expr_scope.

Notation "e1 ^^ e2" := (Papp2 Olxor e1 e2) (at level 60) : expr_scope. 

Notation "e1 & e2" := (Papp2 Oland e1 e2) (at level 40) : expr_scope. 

Notation "e1 | e2" := (Papp2 Olor e1 e2) (at level 50) : expr_scope.

Notation "e1 << e2" := (Papp2 Olsl e1 e2) (at level 35) : expr_scope.
 
Notation "e1 >> e2" := (Papp2 Olsr e1 e2) (at level 35) : expr_scope.

Notation "e1 ?  e2 : e3 " := (Pif e1 e2 e3) (at level 70) : expr_scope.

(* ----------------------------------------------------------- *)
(* lval                                                        *) 

Arguments Lmem _ _%E.
Arguments Laset _ _%E.
Arguments Lnone _%positive _.

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
Notation "x :k= e" := (Cassgn x%L AT_keep e%E)   (at level 70) : prog_scope.
Notation "x ::= e" := (Cassgn x%L AT_none e%E)   (at level 70) : prog_scope.
Notation "x :r= e" := (Cassgn x%L AT_rename e%E) (at level 70) : prog_scope.
Notation "x :i= e" := (Cassgn x%L AT_inline e%E) (at level 70) : prog_scope.


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
