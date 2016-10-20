(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import ZArith gen_map dmasm_utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Syntax
 * -------------------------------------------------------------------- *)

(* more expressive than required, but leads to simpler definitions *)
Inductive stype : Set :=
| sword : stype
| sbool : stype
| sprod : stype -> stype -> stype
| sarr  : positive -> (* stype -> *) stype.

Notation "st1 ** st2" := (sprod st1 st2) (at level 40, left associativity).

(* -------------------------------------------------------------------- *)
Scheme Equality for stype. 
(* Definition stype_beq : stype -> stype -> bool *)

Definition eq_stype (st1 st2 : stype) : {st1 = st2} + {st1<>st2}.
Proof. apply stype_eq_dec. Qed.

Lemma steq_axiom : Equality.axiom stype_beq. 
Proof. 
  move=> x y;apply:(iffP idP).
  + by apply: internal_stype_dec_bl.
  by apply: internal_stype_dec_lb.
Qed.

Definition stype_eqMixin     := Equality.Mixin steq_axiom.
Canonical  stype_eqType      := Eval hnf in EqType stype stype_eqMixin.

(* ** Comparison 
 * -------------------------------------------------------------------- *)

Fixpoint stype_cmp t t' :=
  match t, t' with
  | sword      , sword         => Eq 
  | sword      , _             => Lt
  | sbool      , sword         => Gt
  | sbool      , sbool         => Eq 
  | sbool      , _             => Lt
  | sprod _  _ , sword         => Gt
  | sprod _  _ , sbool         => Gt
  | sprod t1 t2, sprod t1' t2' => Lex (stype_cmp t1 t1') (stype_cmp t2 t2')
  | sprod _  _ , sarr  _       => Lt
  | sarr  n    , sarr  n'      => Pos.compare n n'
  | sarr  _    , _             => Gt
  end.

Instance stypeO : Cmp stype_cmp.
Proof.
  constructor.
  + elim=> [||t1 Ht1 t2 Ht2 |n] [||t1' t2'|n'] //=.
    + by rewrite !Lex_lex;apply lex_sym; auto;apply cmp_sym.
    apply cmp_sym.
  + move=> y x;elim: x y=> 
    [||t1 Ht1 t2 Ht2 |n] [||t1' t2'|n'] [||t1'' t2''|n''] c//=;
    try (by apply ctrans_Eq);eauto using ctrans_Lt, ctrans_Gt.
    + by rewrite !Lex_lex;apply lex_trans=> /=;eauto; apply cmp_ctrans.
    apply cmp_ctrans.
  elim=> [||t1 Ht1 t2 Ht2 |n] [||t1' t2'|n'] //=.
  rewrite !Lex_lex; by move=> /lex_eq /= [] /Ht1 -> /Ht2 ->.
  by move=> H; have -> := (@cmp_eq _ _ positiveO _ _ H). 
Qed.

Module CmpStype.

  Definition t : eqType := [eqType of stype].

  Definition cmp : t -> t -> comparison := stype_cmp.

  Definition cmpO : Cmp cmp := stypeO.
  
End CmpStype.

Module CEDecStype.

  Definition t := [eqType of stype].
  

  Fixpoint pos_dec (p1 p2:positive) : {p1 = p2} + {True} :=
    match p1 as p1' return {p1' = p2} + {True} with
    | xH =>
      match p2 as p2' return {xH = p2'} + {True} with
      | xH => left (erefl xH)
      | _  => right I
      end
    | xO p1' => 
      match p2 as p2' return {xO p1' = p2'} + {True} with
      | xO p2' => 
        match pos_dec p1' p2' with
        | left eq => 
          left (eq_rect p1' (fun p => xO p1' = xO p) (erefl (xO p1')) p2' eq)
        | _ => right I
        end
      | _ => right I
      end
    | xI p1' =>
      match p2 as p2' return {xI p1' = p2'} + {True} with
      | xI p2' => 
        match pos_dec p1' p2' with
        | left eq => 
          left (eq_rect p1' (fun p => xI p1' = xI p) (erefl (xI p1')) p2' eq)
        | _ => right I
        end
      | _ => right I
      end
    end.

  Fixpoint eq_dec (t1 t2:t) : {t1 = t2} + {True} :=
    match t1 as t return {t = t2} + {True} with 
    | sword =>
      match t2 as t0 return {sword = t0} + {True} with
      | sword => left (erefl sword)
      | _     => right I
      end
    | sbool =>
      match t2 as t0 return {sbool = t0} + {True} with
      | sbool => left (erefl sbool)
      | _     => right I
      end
    | sprod t1 t1' =>
      match t2 as t0 return {t1 ** t1' = t0} + {True} with
      | sprod t2 t2' =>
        match eq_dec t1 t2 with
        | left eq1 =>
          match eq_dec t1' t2' with
          | left eq2 => 
            let aux  := eq_rect t1 (fun t => t1 ** t1' = t ** t1') (erefl (t1 ** t1')) t2 eq1 in
            let aux' := eq_rect t1' (fun t => t1 ** t1' = t2 ** t) aux t2' eq2 in
            left aux'
          | right _  => right I
          end
        | right _  => right I
        end
      | _            => right I
      end
    | sarr n1 =>
      match t2 as t0 return {sarr n1 = t0} + {True} with
      | sarr n2 =>
        match pos_dec n1 n2 with
        | left eqn => left (eq_rect n1 (fun n => sarr n1 = sarr n) (erefl (sarr n1)) n2 eqn)
        | right _ => right I
        end
      | _          => right I
      end
    end.

  Lemma pos_dec_r n1 n2 tt: pos_dec n1 n2 = right tt -> n1 != n2.
  Proof.
    case: tt.
    elim: n1 n2 => [n1 Hrec|n1 Hrec|] [n2|n2|] //=. 
    + by case: pos_dec (Hrec n2) => //= -[] /(_ (erefl _)).
    by case: pos_dec (Hrec n2) => //= -[] /(_ (erefl _)).
  Qed.
 
  Lemma eq_dec_r t1 t2 tt: eq_dec t1 t2 = right tt -> t1 != t2.
  Proof.
    case: tt;elim:t1 t2=> [|| t1 Ht1 t2 Ht2 | n] [|| t1' t2' | n'] //=.
    + case: eq_dec (Ht1 t1') => [? _ | [] neq _ ].
      + case: eq_dec (Ht2 t2') => // -[] neq _.
        by move: (neq (erefl _));rewrite !eqE /= andbC => /negPf ->. 
      by move: (neq (erefl _));rewrite !eqE /= => /negPf ->.   
    case: pos_dec (@pos_dec_r n n' I) => [Heq _ | [] neq ] //=.
    move: (neq (erefl _))=> /eqP H _;rewrite !eqE /=.
    by case H':positive_beq=> //;move:H'=> /internal_positive_dec_bl.
  Qed.

End CEDecStype.

Module Mt := DMmake CmpStype CEDecStype.

Delimit Scope mtype_scope with mt.
Notation "m .[ x ]" := (@Mt.get _ m x) : mtype_scope.
Notation "m .[ x  <- v ]" := (@Mt.set _ m x v) : mtype_scope.
Arguments Mt.get P m%mtype_scope k.
Arguments Mt.set P m%mtype_scope k v.
