(* ** Imports and settings *)
From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Import gen_map utils strings ident.
Require Export wsize.
Import Utf8.

(* ** Syntax
 * -------------------------------------------------------------------- *)

(* Low-level (or linear?) types, i.e. types that exist in architectures. *)
#[only(eqbOK)] derive
Variant ltype : Set :=
| lbool
| lword of wsize.

Record length_var := LV { lvname : Ident.ident }.

Definition length_var_beq (v1 v2:length_var) :=
  let (i1) := v1 in
  let (i2) := v2 in
  i1 == i2.

Lemma length_var_eqP : Equality.axiom length_var_beq.
Proof.
  by move=> [i1] [i2]; apply (iffP eqP); congruence.
Qed.

(* Dummy definition *)
Definition is_length_var (v : length_var) := unit.
Lemma is_length_var_inhab v : is_length_var v.
Proof. apply tt. Qed.

Lemma length_var_beq_correct v1 v2 : length_var_beq v1 v2 = true -> v1 = v2.
Proof.
  by move=> /length_var_eqP.
Qed.

Lemma length_var_beq_refl v : length_var_beq v v = true.
Proof.
  by apply /length_var_eqP.
Qed.

derive.eqbOK.register_axiom length_var is_length_var is_length_var_inhab length_var_beq length_var_beq_correct length_var_beq_refl.

HB.instance Definition _ := hasDecEq.Build length_var length_var_eqP.

#[only(eqbOK)] derive
Inductive array_length :=
| ALConst : Z -> array_length
| ALVar : length_var -> array_length
| ALAdd : array_length -> array_length -> array_length
| ALMul : array_length -> array_length -> array_length.

HB.instance Definition _ := hasDecEq.Build array_length array_length_eqb_OK.

(* Syntax types, i.e. types that appear in programs *)
#[only(eqbOK)] derive
Variant atype :=
| abool
| aint
| aarr of wsize & array_length
| aword of wsize.

(* Value types, i.e. types appearing in the semantics *)
#[only(eqbOK)] derive
Variant ctype : Set :=
| cbool
| cint
| carr  of Z
| cword of wsize.

Definition atype_of_ltype ty :=
  match ty with
  | lbool => abool
  | lword ws => aword ws
  end.

Definition ltype_of_atype ty :=
  match ty with
  | abool => Some lbool
  | aword ws => Some (lword ws)
  | _ => None
  end.

(* -------------------------------------------------------------------- *)
Notation lword8   := (lword U8).
Notation lword16  := (lword U16).
Notation lword32  := (lword U32).
Notation lword64  := (lword U64).
Notation lword128 := (lword U128).
Notation lword256 := (lword U256).

(* -------------------------------------------------------------------- *)
Notation ty_msf := (aword msf_size).
Notation cty_msf := (cword msf_size).

(* -------------------------------------------------------------------- *)
HB.instance Definition _ := hasDecEq.Build ltype ltype_eqb_OK.
HB.instance Definition _ := hasDecEq.Build atype atype_eqb_OK.
HB.instance Definition _ := hasDecEq.Build ctype ctype_eqb_OK.


(* ** Comparison
 * -------------------------------------------------------------------- *)

Definition length_var_cmp (v1 v2 : length_var) :=
  let (i1) := v1 in
  let (i2) := v2 in
  Ident.Mid.K.cmp i1 i2.
  (* for some reason, this works while the more natural [Tident.cmp i1 i2]
     produces ill-typed OCaml code *)

Fixpoint array_length_cmp al1 al2 :=
  match al1, al2 with
  | ALConst z1, ALConst z2 => Z.compare z1 z2
  | ALConst _, _ => Lt

  | ALVar _, ALConst _ => Gt
  | ALVar x1, ALVar x2 => length_var_cmp x1 x2
  | ALVar _, _ => Lt

  | ALAdd _ _, ALConst _ => Gt
  | ALAdd _ _, ALVar _ => Gt
  | ALAdd al11 al12, ALAdd al21 al22 => Lex (array_length_cmp al11 al21) (array_length_cmp al12 al22)
  | ALAdd _ _, _ => Lt

  | ALMul al11 al12, ALMul al21 al22 => Lex (array_length_cmp al11 al21) (array_length_cmp al12 al22)
  | ALMul _ _, _ => Gt
  end.

Instance length_varO : Cmp length_var_cmp.
Proof.
  constructor.
  + move=> [i1] [i2] /=.
    by apply (cmp_sym (Cmp:=Ident.Mid.K.cmpO)).
  + move=> [i1] [i2] [i3] /=.
    by apply (cmp_ctrans (Cmp:=Ident.Mid.K.cmpO)).
  move=> [i1] [i2] /=.
  by move=> /(cmp_eq (Cmp:=Ident.Mid.K.cmpO)) ->.
Qed.

Instance array_lengthO : Cmp array_length_cmp.
Proof.
  constructor.
  + elim=>
      [z1|x1|al11 ih1 al12 ih2|al11 ih1 al12 ih2]
      [z2|x2|al21     al22    |al21     al22    ] //=.
    + by apply cmp_sym.
    + by apply cmp_sym.
    + by rewrite !Lex_lex; apply lex_sym.
    by rewrite !Lex_lex; apply lex_sym.
  + elim=>
      [z1|x1|al11 ih1 al12 ih2|al11 ih1 al12 ih2]
      [z2|x2|al21     al22    |al21     al22    ]
      [z3|x3|al31     al32    |al31     al32    ] //=;
       try (by apply ctrans_Eq); eauto using ctrans_Lt, ctrans_Gt; try apply cmp_ctrans.
    + move=> c.
      by rewrite !Lex_lex; apply lex_trans; eauto.
    move=> c.
    by rewrite !Lex_lex; apply lex_trans; eauto.
  elim=>
    [z1|x1|al11 ih1 al12 ih2|al11 ih1 al12 ih2]
    [z2|x2|al21     al22    |al21     al22    ] //=.
  + by move=> /cmp_eq ->.
  + by move=> /cmp_eq ->.
  + by rewrite Lex_lex => /lex_eq /= [/ih1 <- /ih2 <-].
  by rewrite Lex_lex => /lex_eq /= [/ih1 <- /ih2 <-].
Qed.

Definition atype_cmp t t' :=
  match t, t' with
  | abool   , abool         => Eq
  | abool   , _             => Lt

  | aint    , abool         => Gt
  | aint    , aint          => Eq
  | aint    , _             => Lt

  | aword _ , aarr _ _      => Lt
  | aword w , aword w'      => wsize_cmp w w'
  | aword _ , _             => Gt

  | aarr ws al , aarr ws' al' => Lex (wsize_cmp ws ws') (array_length_cmp al al')
  | aarr _ _  , _           => Gt
  end.

#[global]
Instance atypeO : Cmp atype_cmp.
Proof.
  constructor.
  + case => [||ws al|w] [||ws' al'|w'] //=.
    + by rewrite !Lex_lex lex_sym //=; apply cmp_sym.
    by apply cmp_sym.
  + move=> y x; case: x y=> [||ws al|w] [||ws' al'|w'] [||ws'' al''|w''] c //=;
       try (by apply ctrans_Eq);eauto using ctrans_Lt, ctrans_Gt.
    + by rewrite !Lex_lex; apply lex_trans; apply cmp_ctrans.
    by apply cmp_ctrans.
  case=> [||al ws|w] [||al' ws'|w'] //=.
  + by rewrite Lex_lex => /lex_eq /= [/cmp_eq <- /cmp_eq <-].
  by move=> /cmp_eq <-.
Qed.

Module CmpAtype.

  Definition t : eqType := atype.

  Definition cmp : t -> t -> comparison := atype_cmp.

  Definition cmpO : Cmp cmp := atypeO.

End CmpAtype.

Module CEDecAtype.

  Definition t : eqType := atype.

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

  Definition eq_dec (t1 t2:t) : {t1 = t2} + {True} :=
    match t1 as t return {t = t2} + {True} with
    | abool =>
      match t2 as t0 return {abool = t0} + {True} with
      | abool => left (erefl abool)
      | _     => right I
      end
    | aint =>
      match t2 as t0 return {aint = t0} + {True} with
      | aint => left (erefl aint)
      | _     => right I
      end
    | aarr ws1 al1 =>
      match t2 as t0 return {aarr ws1 al1 = t0} + {True} with
      | aarr ws2 al2 =>
        match wsize_eq_dec ws1 ws2 with
        | left eqw =>
          match array_length_eqb_OK_sumbool al1 al2 with
          | left eqn => left (f_equal2 aarr eqw eqn)
          | right _ => right I
          end
        | _ => right I
        end
      | _          => right I
      end
    | aword w1 =>
      match t2 as t0 return {aword w1 = t0} + {True} with
      | aword w2 =>
        match wsize_eq_dec w1 w2 with
        | left eqw => left (f_equal aword eqw)
        | right _ => right I
        end
      | _     => right I
      end
    end.

  Lemma pos_dec_r n1 n2 tt: pos_dec n1 n2 = right tt -> n1 != n2.
  Proof.
    case: tt.
    elim: n1 n2 => [n1 Hrec|n1 Hrec|] [n2|n2|] //=.
    + case: pos_dec (Hrec n2) => //= -[] /(_ (erefl _)) /eqP ? _.
      by apply /eqP; congruence.
    case: pos_dec (Hrec n2) => //= -[] /(_ (erefl _)) /eqP ? _.
    by apply /eqP; congruence.
  Qed.

  Lemma eq_dec_r t1 t2 tt: eq_dec t1 t2 = right tt -> t1 != t2.
  Proof.
    case: tt;case:t1 t2=> [||ws al|w] [||ws' al'|w'] //=.
    + case: wsize_eq_dec => eqw.
      + case: array_length_eqb_OK_sumbool => // eqal.
        by move=> _; apply /eqP; congruence.
      by move=> _; apply/eqP => -[].
    case: wsize_eq_dec => // eqw.
    by move=> _;apply /eqP;congruence.
  Qed.

End CEDecAtype.

Module Mt := DMmake CmpAtype CEDecAtype.

Declare Scope mtype_scope.
Delimit Scope mtype_scope with mt.
Notation "m .[ x ]" := (@Mt.get _ m x) : mtype_scope.
Notation "m .[ x  <- v ]" := (@Mt.set _ m x v) : mtype_scope.
Arguments Mt.get P m%_mtype_scope k.
Arguments Mt.set P m%_mtype_scope k v.

(* A bit hacky: to avoid some nameclashes with the names generated
   by elpi.derive, we put these definitions in a module.
   A better solution would be to change elpi.derive to ensure that all
   names obey the "prefix" parameter. *)
Module Export OtherDefs.

Definition is_abool t := if t is abool then true else false.

Lemma is_aboolP t : reflect (t=abool) (is_abool t).
Proof. by case: t => /=; constructor. Qed.

Definition is_aword t := if t is aword _ then true else false.

Definition is_aarr t := if t is aarr _ _ then true else false.

Definition is_not_aarr t := ~~is_aarr t.

Lemma is_aarrP ty : reflect (exists ws n, ty = aarr ws n) (is_aarr ty).
Proof. by case: ty; constructor; eauto => -[?] [?]. Qed.

Definition is_word_type (t:atype) :=
  if t is aword sz then Some sz else None.

Lemma is_word_typeP ty ws :
  is_word_type ty = Some ws -> ty = aword ws.
Proof. by case: ty => //= w [->]. Qed.

Definition is_cword t := if t is cword _ then true else false.
Definition is_carr t := if t is carr _ then true else false.
Definition is_not_carr t := ~~ is_carr t.

End OtherDefs.

(* -------------------------------------------------------------------- *)

Section EVAL.

Context (env : length_var -> option Z).

Fixpoint eval_opt (al:array_length) : option Z :=
  match al with
  | ALConst z => Some z
  | ALVar v => env v
  | ALAdd al1 al2 =>
    let%opt z1 := eval_opt al1 in
    let%opt z2 := eval_opt al2 in
    Some (z1 + z2)
  | ALMul al1 al2 =>
    let%opt z1 := eval_opt al1 in
    let%opt z2 := eval_opt al2 in
    Some (z1 * z2)
  end%Z.

Definition eval al :=
  if eval_opt al is Some z then
    if (0 <? z)%Z then z
    else 0%Z
  else 0%Z.

Definition eval_atype ty :=
  match ty with
  | abool => cbool
  | aint => cint
  | aarr ws len => carr (arr_size ws (eval len))
  | aword ws => cword ws
  end.

Definition eval_ltype ty :=
  match ty with
  | lbool => cbool
  | lword ws => cword ws
  end.

End EVAL.

(* We define a polynom equality checker. This is what ring or lia know how to do.
   We could probably call functions coming from their implementation instead. *)
From Equations Require Import Equations.
(* importing equations messes with erefl/refl_equal for some reason... *)
Arguments Logic.eq_refl {_} {_}, [_] _.
From Coq Require Import Lia.

Fixpoint size_poly poly : nat :=
  match poly with
  | ALConst _ | ALVar _ => 1
  | ALAdd p1 p2 | ALMul p1 p2 =>
    size_poly p1 + size_poly p2
  end.

Lemma lt0_size_poly p : (0 < size_poly p)%nat.
Proof. by elim: p => /=; lia. Qed.

Fixpoint size_Mul poly : nat :=
  match poly with
  | ALConst _ | ALVar _ => 0
  | ALAdd p1 p2 => size_Mul p1 + size_Mul p2
  | ALMul p1 p2 => 1 + size_Mul p1 + size_Mul p2
  end.

Fixpoint left_Mul_under_Mul poly : nat :=
  match poly with
  | ALConst _ | ALVar _ => 0
  | ALAdd p1 p2 => left_Mul_under_Mul p1 + left_Mul_under_Mul p2
  | ALMul p1 p2 => size_Mul p1 + left_Mul_under_Mul p2
  end.

Fixpoint insert_mono x mono :=
  match mono with
  | [::] => [:: x]
  | x2 :: mono =>
    match length_var_cmp x x2 with
    | Lt | Eq => x :: x2 :: mono
    | Gt => x2 :: insert_mono x mono
    end
  end.

Fixpoint insert_term cm terms :=
  match terms with
  | [::] => [:: cm]
  | cm2 :: terms =>
    match List.list_compare length_var_cmp (snd cm) (snd cm2) with
    | Lt => cm :: cm2 :: terms
    | Eq => let new_coeff := fst cm + fst cm2 in (* if new_coeff =? 0 then terms else *) (new_coeff, snd cm) :: terms
    | Gt => cm2 :: insert_term cm terms
    end
  end%Z.
Definition insert_term_nice cm terms :=
  (* if (fst cm =? 0)%Z then terms else *) insert_term cm terms.

Equations expanded_form (p : array_length) : list (Z * list length_var) :=
  expanded_form p := aux [::] 1 [::] p

  where aux (terms : list (Z * list length_var)) (coeff : Z) (mono : list length_var) (p : array_length) : list (Z * list length_var) by wf (size_poly p, left_Mul_under_Mul p) (lexprod _ _ lt lt)  :=
    aux terms coeff mono (ALConst n) := let coeff := (n * coeff)%Z in insert_term_nice (coeff, mono) terms;
    aux terms coeff mono (ALVar x) := let mono := insert_mono x mono in insert_term_nice (coeff, mono) terms;
    aux terms coeff mono (ALAdd e1 e2) := aux (aux terms coeff mono e1) coeff mono e2;
    aux terms coeff mono (ALMul (ALConst n) e) := let coeff := (n * coeff)%Z in aux terms coeff mono e;
    aux terms coeff mono (ALMul (ALVar x) e) := let mono := insert_mono x mono in aux terms coeff mono e;
    aux terms coeff mono (ALMul (ALAdd e11 e12) e2) := aux (aux terms coeff mono (ALMul e11 e2)) coeff mono (ALMul e12 e2);
    aux terms coeff mono (ALMul (ALMul e11 e12) e2) := aux terms coeff mono (ALMul e11 (ALMul e12 e2)).
Next Obligation.
  simpl.
  left. have := lt0_size_poly e2. lia.
Qed.
Next Obligation.
  simpl.
  left. have := lt0_size_poly e1. lia.
Qed.
Next Obligation.
  simpl. left. have := lt0_size_poly e12. lia.
Qed.
Next Obligation.
  simpl. left. have := lt0_size_poly e11. lia.
Qed.
Final Obligation.
  simpl. rewrite Nat.add_assoc. right.
  lia.
Qed.

Definition compare_array_length '(ws, al) '(ws', al') :=
  let ef := expanded_form (ALMul (ALConst (wsize_size ws)) al) in
  let ef' := expanded_form (ALMul (ALConst (wsize_size ws')) al') in
  ef == ef'.

Definition convertible (t t' : atype) :=
  match t with
  | aarr ws al =>
    if t' is aarr ws' al' then compare_array_length (ws, al) (ws', al') else false
  | _ => t == t'
  end.

Lemma convertible_refl t : convertible t t.
Proof. by case: t => //=. Qed.
#[global]
Hint Resolve convertible_refl : core.

Lemma convertible_sym ty1 ty2 : convertible ty1 ty2 -> convertible ty2 ty1.
Proof.
  case: ty1 ty2 => [||ws1 al1|ws1] [||ws2 al2|ws2] //=.
  + by rewrite eq_sym.
  by rewrite eq_sym.
Qed.

Lemma convertible_trans ty2 ty1 ty3 :
  convertible ty1 ty2 -> convertible ty2 ty3 -> convertible ty1 ty3.
Proof.
  case: ty1 ty2 => [||ws1 al1|ws1] [||ws2 al2|ws2] //=.
  + by move=> /eqP ->.
  by move=> /eqP ->.
Qed.

Fixpoint eval_mono (env : length_var -> option Z) (mono : list length_var) : option Z :=
  match mono with
  | [::] => Some 1
  | x :: mono =>
    let%opt zx := env x in
    let%opt zmono := eval_mono env mono in
    Some (zx * zmono)
  end%Z.

Fixpoint eval_expand (env : length_var -> option Z) terms : option Z :=
  match terms with
  | [::] => Some 0
  | (count, mono) :: terms =>
    let%opt zmono := eval_mono env mono in
    let%opt zterms := eval_expand env terms in
    Some (count * zmono + zterms)
  end%Z.

Lemma insert_mono_correct env x mono :
  eval_mono env (insert_mono x mono) =
    let%opt zx := env x in
    let%opt zmono := eval_mono env mono in
    Some (zx * zmono)%Z.
Proof.
Local Opaque Z.add Z.mul.
  elim: mono => [|x2 mono ih] /=.
  - done.
  - case: length_var_cmp => //=.
    rewrite ih.
    case: (env x) (env x2) => [zx|] [zx2|] //=.
    case: eval_mono => [?|//]. apply f_equal. lia.
Local Transparent Z.add Z.mul.
Qed.

Lemma insert_term_correct env cm terms :
  eval_expand env (insert_term cm terms) =
    let%opt zterms := eval_expand env terms in
    let%opt zmono := eval_mono env (snd cm) in
    Some (zterms + fst cm * zmono)%Z.
Proof.
  elim: terms => [|cm2 terms ih] //=.
  - case: cm => [count mono] /=.
    case: eval_mono => [?|//].
    apply f_equal. lia.
  case: List.list_compareP.
  + move=> x y. split.
    + by apply cmp_eq.
    move=> <-. by apply cmp_refl.
  + case: cm ih => [coeff mono] /= ih.
    case: cm2 => [coeff2 mono2] /=.
    move=> ?; subst mono2. (*
    case: Z.eqb_spec.
    + move=> ?.
      case: eval_mono => [?|//].
      case: eval_expand => [?|//].
      move=> [<-] [->].
      apply f_equal. lia.
    move=> _ /=. *)
    case: eval_mono => [?|//].
    case: eval_expand => [?|//].
    apply f_equal. lia.
  + case: cm ih => [coeff mono] /= ih.
    case: cm2 => [coeff2 mono2] /=. move=> ???.
    case: (eval_mono env mono) (eval_mono env mono2) (eval_expand env terms) => [?|] [?|] [?|] //.
    apply f_equal. lia.
  + case: cm ih => [coeff mono] /= ih.
    case: cm2 => [coeff2 mono2] /=. move=> ???.
    rewrite ih.
    case: eval_mono => [?|//].
    case: eval_expand => [?|//].
    case: eval_mono => [?|//].
    apply f_equal. lia.
  + case: cm ih => [coeff mono] /= ih.
    case: cm2 => [coeff2 mono2] /=. move=> ????????.
    case: (eval_mono env mono) (eval_mono env mono2) (eval_expand env terms) => [?|] [?|] [?|] //.
    apply f_equal. lia.
  case: cm ih => [coeff mono] /= ih.
  case: cm2 => [coeff2 mono2] /=. move=> ????????.
  rewrite ih.
  case: eval_mono => [?|//].
  case: eval_expand => [?|//].
  case: eval_mono => [?|//].
  apply f_equal. lia.
Qed.

Lemma insert_term_nice_correct env cm terms :
  eval_expand env (insert_term_nice cm terms) =
    let%opt zterms := eval_expand env terms in
    let%opt zmono := eval_mono env (snd cm) in
    Some (zterms + fst cm * zmono)%Z.
Proof.
  rewrite /insert_term_nice. (*
  case: Z.eqb_spec.
  + move=> -> -> _.
    apply f_equal. lia.
  move=> _. *)
  by apply insert_term_correct.
Qed.

Lemma expanded_form_sound p :
  forall env,
    eval_expand env (expanded_form p) = eval_opt env p.
Proof.
Local Opaque Z.add Z.mul.
  move=> env. move: p.
  apply (expanded_form_elim
    (P := fun p terms => eval_expand env terms = eval_opt env p)
    (P0 := fun _ terms coeff mono p' terms' =>
             eval_expand env terms' =
               let%opt zterms := eval_expand env terms in
               let%opt zmono := eval_mono env mono in
               let%opt zp' := eval_opt env p' in
               Some (zterms + coeff * zmono * zp')))%Z. (*
         match eval_expand env terms, eval_mono env mono, eval env p' with
         | Some zterms, Some zmono, Some zp' => Some (zterms + coeff * zmono * zp')
         | _, _, _ => None
         end))%Z. *)
  - move=> p /= ->.
    case: eval_opt => [?|//].
    apply f_equal. lia.
  - move=> _ terms coeff mono n /=.
    rewrite insert_term_nice_correct /=.
    case: eval_expand => [?|//].
    case: eval_mono => [?|//].
    apply f_equal. lia.
  - move=> _ terms coeff mono x /=.
    rewrite insert_term_nice_correct /= insert_mono_correct.
    case: (eval_expand env terms) (eval_mono env mono) (env x) => [?|] [?|] [?|] //.
    apply f_equal. lia.
  - move=> p terms coeff mono e1 e2 /= h1 h2.
    rewrite h2 h1.
    case: eval_expand => [?|//].
    case: eval_mono => [?|//].
    case: eval_opt => [?|//].
    case: eval_opt => [?|//].
    apply f_equal. lia.
  - move=> p terms coeff mono n e /= h.
    rewrite h.
    case: eval_expand => [?|//].
    case: eval_mono => [?|//].
    case: eval_opt => [?|//].
    apply f_equal. lia.
  - move=> p terms coeff mono x e /= h.
    rewrite h insert_mono_correct.
    case: eval_expand => [?|//].
    case: (eval_mono env mono) (eval_opt env e) (env x) => [?|] [?|] [?|] //.
    apply f_equal. lia.
  - move=> p terms coeff mono e11 e12 e2 /= h1 h2.
    rewrite h2 h1.
    case: eval_expand => [?|//].
    case: eval_mono => [?|//].
    case: (eval_opt env e11) (eval_opt env e12) (eval_opt env e2) => [?|] [?|] [?|] //.
    apply f_equal. lia.
  - move=> p terms coeff mono e11 e12 e2 /= h.
    rewrite h.
    case: eval_expand => [?|//].
    case: eval_mono => [?|//].
    case: (eval_opt env e11) (eval_opt env e12) (eval_opt env e2) => [?|] [?|] [?|] //.
    apply f_equal. lia.
Local Transparent Z.add Z.mul.
Qed.


Lemma compare_array_length_eval ws1 len1 ws2 len2 :
  compare_array_length (ws1, len1) (ws2, len2) ->
  forall env,
  arr_size ws1 (eval env len1) = arr_size ws2 (eval env len2).
Proof.
Local Opaque wsize_size Z.mul.
  rewrite /compare_array_length => /eqP heq.
  move=> env.
  have := expanded_form_sound (ALMul (ALConst (wsize_size ws1)) len1) env.
  have := expanded_form_sound (ALMul (ALConst (wsize_size ws2)) len2) env.
  rewrite /= heq => ->.
  rewrite /eval.
  case: (eval_opt env len1) (eval_opt env len2) => [z1|] [z2|] //.
  move=> [].
  rewrite !arr_sizeE.
  have ?: (0 < wsize_size ws1)%Z by [].
  have ?: (0 < wsize_size ws2)%Z by [].
  by case: (ZltP 0 z1) (ZltP 0 z2) => [?|?] [?|?]; nia.
Local Transparent wsize_size Z.mul.
Qed.

Lemma convertible_eval_atype ty1 ty2 :
  convertible ty1 ty2 ->
  forall env,
    eval_atype env ty1 = eval_atype env ty2.
Proof.
Local Opaque wsize_size Z.mul.
  move=> hc env.
  case: ty1 ty2 hc => [||ws1 n1|ws1] [||ws2 n2|ws2] //=.
  + by move=> /compare_array_length_eval ->.
  by move=> /eqP [<-].
Local Transparent wsize_size Z.mul.
Qed.

Lemma all2_convertible_eval_atype tys1 tys2 :
  all2 convertible tys1 tys2 ->
  forall env,
    map (eval_atype env) tys1 = map (eval_atype env) tys2.
Proof.
  move=> hc env.
  elim: tys1 tys2 hc => [|ty1 tys1 ih1] [|ty2 tys2] //=.
  by move=> /andP [/convertible_eval_atype -> /ih1 ->].
Qed.

Definition subatype (t t': atype) :=
  match t with
  | aword w => if t' is aword w' then (w ≤ w')%CMP else false
  | _ => convertible t t'
  end.

Lemma subatypeE ty ty' :
  subatype ty ty' →
  match ty' return Prop with
  | aword sz' => ∃ sz, ty = aword sz ∧ (sz ≤ sz')%CMP
  | _         => convertible ty ty'
end.
Proof.
  case: ty => [||ws al|ws]; try by move/eqP => <-.
  + by case: ty'.
  by case: ty' => //; eauto.
Qed.

Lemma subatypeEl ty ty' :
  subatype ty ty' →
  match ty return Prop with
  | aword sz => ∃ sz', ty' = aword sz' ∧ (sz ≤ sz')%CMP
  | _        => convertible ty ty'
  end.
Proof.
  case: ty => [||ws al|ws] //=.
  by case: ty' => //; eauto.
Qed.

Lemma subatype_refl ty : subatype ty ty.
Proof. by case: ty => //= ??; rewrite !eq_refl. Qed.
#[global]
Hint Resolve subatype_refl : core.

Lemma subatype_trans ty2 ty1 ty3 :
  subatype ty1 ty2 -> subatype ty2 ty3 -> subatype ty1 ty3.
Proof.
  case: ty1 => //= [/eqP<-|/eqP<-|ws1 al1|ws1] //.
  + by case: ty2 => //= ws2 al2 /eqP ->.
  by case: ty2 => //= ws2 hle; case: ty3 => //= ws3; apply: cmp_le_trans hle.
Qed.

Lemma is_aword_subatype t1 t2 : subatype t1 t2 -> is_aword t1 = is_aword t2.
Proof.
  by case: t1 => //= [/eqP <-|/eqP <-|??|?] //; case:t2.
Qed.

Definition subctype (t t': ctype) :=
  match t with
  | cword w => if t' is cword w' then (w ≤ w')%CMP else false
  | _ => t == t'
  end.

Lemma subctypeE ty ty' :
  subctype ty ty' →
  match ty' with
  | cword sz' => ∃ sz, ty = cword sz ∧ (sz ≤ sz')%CMP
  | _         => ty = ty'
end.
Proof.
  case: ty => [||n|ws]; try by move/eqP => <-.
  by case: ty' => //; eauto.
Qed.

Lemma subctypeEl ty ty' :
  subctype ty ty' →
  match ty return Prop with
  | cword sz => ∃ sz', ty' = cword sz' ∧ (sz ≤ sz')%CMP
  | _        => ty = ty'
  end.
Proof.
  case: ty => [||n|ws] //=; try by move/eqP => <-.
  by case: ty' => //; eauto.
Qed.

Lemma subctype_refl ty : subctype ty ty.
Proof. case: ty => //=. Qed.
#[global]
Hint Resolve subctype_refl : core.

Lemma subctype_trans ty2 ty1 ty3 :
  subctype ty1 ty2 -> subctype ty2 ty3 -> subctype ty1 ty3.
Proof.
  case: ty1 => //= [/eqP<-|/eqP<-|n1|ws1] //.
  + by case: ty2 => //= n2 /eqP ->.
  by case: ty2 => //= ws2 hle; case: ty3 => //= ws3; apply: cmp_le_trans hle.
Qed.

Lemma subatype_subctype ty1 ty2 :
  subatype ty1 ty2 ->
  forall env,
    subctype (eval_atype env ty1) (eval_atype env ty2).
Proof.
Local Opaque convertible.
  move=> hsub env.
  have suff hc: convertible ty1 ty2.
  + by move=> /convertible_eval_atype ->.
  case: ty1 ty2 hsub hc => [||ws1 n1|ws1] [||ws2 n2|ws2] // hsub hc; eauto.
Local Transparent convertible.
Qed.

(* -------------------------------------------------------------------- *)
#[only(eqbOK)] derive
Variant extended_type : Type :=
  | ETbool
  | ETint
  | ETarr of wsize & array_length
  | ETword of (option signedness) & wsize.

Definition tbool := ETbool.
Definition tint  := ETint.
Definition tarr  (ws : wsize) (al : array_length) := ETarr ws al.
Definition tword ws : extended_type := ETword None ws.
Definition twint (s : signedness) (ws : wsize) := ETword (Some s) ws.
Definition tuint ws : extended_type := twint Unsigned ws.
Definition tsint ws : extended_type := twint Signed ws.

Definition to_atype (t:extended_type) : atype :=
  match t with
  | ETbool      => abool
  | ETint       => aint
  | ETarr ws l  => aarr ws l
  | ETword _ ws => aword ws
  end.

HB.instance Definition _ := hasDecEq.Build extended_type extended_type_eqb_OK.
