(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
Require Import choice fintype eqtype div seq finmap strings zmodp.
Require Import dmasm_utils dmasm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope fmap.
Local Open Scope fset.

(* ** Set up canonical instances for loc so we can use fset
 * -------------------------------------------------------------------- *)

Definition code_pexpr (l : pexpr) : nat := admit.
Definition decode_pexpr (l : nat) : pexpr := admit.

Lemma codeK_pexpr : cancel code_pexpr decode_pexpr.
Admitted.

Definition pexpr_eqMixin := comparableClass (@LEM pexpr).
Canonical  pexpr_eqType  := Eval hnf in EqType pexpr pexpr_eqMixin.

Definition pexpr_choiceMixin := CanChoiceMixin codeK_pexpr.
Canonical  pexpr_choiceType  := ChoiceType pexpr pexpr_choiceMixin.

Fixpoint code_loc (l : loc) : option pexpr * ident :=
  (l.(l_oidx), l.(l_id)).

Fixpoint decode_loc (s : option pexpr * ident) : loc :=
  let: (oi, id) := s in mkLoc oi id.

Lemma codeK_loc : cancel code_loc decode_loc.
Proof. by elim=> //= a s ->. Qed.

Definition loc_choiceMixin := CanChoiceMixin codeK_loc.
Canonical  loc_choiceType  := ChoiceType loc loc_choiceMixin.

(* ** Occurences of idents
 * -------------------------------------------------------------------- *)

Fixpoint id_occ_pexpr pe :=
  match pe with
  | Pvar id          => [fset id]
  | Pbinop _ pe1 pe2 => id_occ_pexpr pe1 `|` id_occ_pexpr pe2
  | Pconst _         => fset0
  end.

Definition id_occ_oidx (op : option pexpr) :=
  match op with
  | None => fset0
  | Some pe => id_occ_pexpr pe
  end.

Definition id_occ_loc (l : loc) :=
  l.(l_id) |` id_occ_oidx l.(l_oidx).

Definition id_occ_src (s : src) :=
  match s with
  | Imm pe => id_occ_pexpr pe
  | Loc(l) => id_occ_loc l
  end.

Fixpoint id_occ_pcond (pc : pcond) :=
  match pc with
  | Ptrue           => fset0
  | Pnot pc         => id_occ_pcond pc
  | Pand pc1 pc2    => id_occ_pcond pc1 `|` id_occ_pcond pc2
  | Pcond _ pe1 pe2 => id_occ_pexpr pe1 `|` id_occ_pexpr pe2
  end.

Fixpoint id_occ_instr i : {fset ident} :=
  match i with
  | Skip =>
      fset0
  | Seq i1 i2 =>
      id_occ_instr i1 `|` id_occ_instr i2
  | Assgn ds _ ss =>
      unions_seq (map id_occ_loc ds) `|` unions_seq (map id_occ_src ss)
  | Call fd drets args => (* ignore fd here *)
      seq_fset drets `|` unions_seq (map id_occ_src args)
  | If pc i1 i2 =>
      id_occ_pcond pc `|` id_occ_instr i1 `|` id_occ_instr i2
  | For id lb ub i =>
          id
       |` id_occ_pexpr lb `|` id_occ_pexpr ub
      `|` id_occ_instr i
  end.

(* ** Irrelevant local variables for eval_instr *)

Lemma eq_on_eval_pexpr_eq pe lm1 lm2:
  lm1 = lm2 [& id_occ_pexpr pe] ->
  eval_pexpr lm1 pe = eval_pexpr lm2 pe.
Proof.
elim: pe.
+ by rewrite /= => i Heq; rewrite (eq_on_get_fset1 Heq).
+ move=> pop pe1 H1 pe2 H2.
  rewrite /= => Heq. move: (eq_on_U Heq) => [Heq1  Heq2].
  by rewrite (H1 Heq1) (H2 Heq2); case (eval_pexpr _ _).
+ done.
Qed.

Lemma eq_on_eval_pcond_eq pc lm1 lm2:
  lm1 = lm2 [& id_occ_pcond pc] ->
  eval_pcond lm1 pc = eval_pcond lm2 pc.
Proof.
elim: pc.
+ done.
+ by move=> pc => //=; move=> H1 Heq; rewrite (H1 Heq).
+ move=> pc1 H1 pc2 H2 => //=. move=> Heq.
  by rewrite (H1 (eq_on_Ul Heq)) (H2 (eq_on_Ur Heq)).
+ rewrite /= => pob p1 p2 Heq.
  move: (eq_on_U Heq) => [Heq1 Heq2].
  by rewrite (eq_on_eval_pexpr_eq Heq1) (eq_on_eval_pexpr_eq Heq2).
Qed.

Lemma eq_on_read_oidx_eq oi lm1 lm2:
  lm1 = lm2 [& id_occ_oidx oi]->
  read_oidx lm1 oi = read_oidx lm2 oi.
Proof.
rewrite /=; case oi => //=; move=> p Heq.
by rewrite /read_oidx (eq_on_eval_pexpr_eq Heq).
Qed.
  
Lemma eq_on_read_loc_eq l lm1 lm2:
  lm1 = lm2 [& id_occ_loc l] ->
  read_loc lm1 l = read_loc lm2 l.
Proof.
case l => /= ope lid; rewrite /id_occ_loc /read_loc //= => Heq.
move: (eq_on_U Heq) => [Heq1 Heq2].
by rewrite (eq_on_get_fset1 Heq1) (eq_on_read_oidx_eq Heq2).
Qed.

Lemma eq_on_read_src_eq src lm1 lm2:
  lm1 = lm2 [& id_occ_src src] ->
  read_src lm1 src = read_src lm2 src.
Proof.
case src => /= pe Heq.
+ by rewrite (eq_on_eval_pexpr_eq Heq).
+ by rewrite (eq_on_read_loc_eq Heq).
Qed.

Lemma eq_on_mapM_read_src_eq srcs lm1 lm2 ids:
  lm1 = lm2 [& ids] ->
  unions_seq [seq id_occ_src i | i <- srcs] `<=` ids ->
  mapM (read_src lm1) srcs = mapM (read_src lm2) srcs.
Proof.
move=> HeqOn; elim: srcs => // src srcs IH.
rewrite /= fsubUset; move/andP => [] Hsub1_ Hsub2_.
rewrite (IH Hsub2_) (@eq_on_read_src_eq src lm1 lm2 _) => //=.
by apply: (eq_on_fsubset Hsub1_).
Qed.

Lemma eq_on_write_loc_eq lm1 lm2 loc sval:
  lm1 = lm2 [& id_occ_loc loc] ->
  write_loc lm1 loc sval = write_loc lm2 loc sval [&& id_occ_loc loc].
Proof.
case loc => /=; case => pe; last first.
rewrite /id_occ_loc /= /write_loc => Heq.
+ by apply eq_on_setf_same.
rewrite /id_occ_loc /write_loc => id.
case sval => //= w Heq. move: (eq_on_U Heq) => [Heq1 Heq2].
(* FIXME: move: (eq_on_read_loc_eq Heq) hangs here *)
have ->:   read_loc lm1 {| l_oidx := Some pe; l_id := id |}
         = read_loc lm2 {| l_oidx := Some pe; l_id := id |} => /=.
+ by apply: eq_on_read_loc_eq.
case (read_loc _ _) => //=; last first.
+ rewrite (@eq_on_eval_pexpr_eq pe lm1 lm2) => //=.
  case (eval_pexpr _ _) => //= w2.
  by apply: eq_on_setf_same.
case => //= a.
rewrite (@eq_on_eval_pexpr_eq pe lm1 lm2) => //=.
case (eval_pexpr _ _) => //= w2.
by apply: eq_on_setf_same.
Qed.

Lemma eq_on_write_locs_eq locs sval ids:
  forall lm1 lm2,
    unions_seq [seq id_occ_loc i | i <- locs] `<=` ids -> 
    lm1 = lm2 [& ids] ->
    write_locs lm1 locs sval = write_locs lm2 locs sval [&& ids].
Proof.
elim: locs => //=.
+ by case sval => //=.
move=> loc locs IH lm1 lm2 Hsub Heq.
case sval => //= sv svs.
admit.
Qed.

Lemma eq_on_eval_instr_eq (i : instr):
  forall lm1 lm2 ids,
    id_occ_instr i `<=` ids ->
    lm1 = lm2 [&ids]->
    eval_instr lm1 i = eval_instr lm2 i [&& ids].
Proof.
move: i; elim/instr_ind.
  (* Skip *)
+ by move=> lm1 lm2; rewrite /= /eq_on; move=> ids Hsub ->.
  (* Seq *)
+ move=> i1 Hi1 i2 Hi2 lm1 lm2 ids.
  rewrite /= fsubUset => Hsub Heq.
  move/andP: Hsub => [Hsub1 Hsub2].
  move: (Hi1 lm1 lm2 ids Hsub1 Heq) => /=.
  case: (eval_instr lm1 i1); case: (eval_instr lm2 i1) => //=.
  move=> lm1_ lm2_ HeqSome.
  by apply: Hi2 => //.
  (* Assgn *)
+ move=> dlocs op srcs lm1 lm2 ids => /=.
  rewrite fsubUset; move/andP => [] Hsub1 Hsub2 Heq.
  rewrite (@eq_on_mapM_read_src_eq srcs lm1 lm2 ids Heq Hsub2).
  case (mapM _ _) => //= loc.
  case (eval_op op loc) => //= svals.
  by apply: eq_on_write_locs_eq.
  (* If *)
+ move=> pc i1 Hi1 i2 Hi2 lm1 lm2 ids.
  rewrite /= !fsubUset. move/andP => []. move/andP => [] Hsub1 Hsub2 Hsub3 Heq.
  have ->: eval_pcond lm1 pc = eval_pcond lm2 pc.
  + apply: eq_on_eval_pcond_eq.
    by apply: (eq_on_fsubset Hsub1).
  case (eval_pcond lm2 pc) => /= ; last done.
  by move=> b; case b; [ apply Hi1 | apply Hi2].
  (* For *)
+ admit.
  (* Call *)
+ admit.
Qed.

(* ** Occurences of locations (FIXME: unclear this is what we'll need)
 * -------------------------------------------------------------------- *)

Fixpoint loc_occ_pexpr pe :=
  match pe with
  | Pvar id          => [fset mkLoc None id]
  | Pbinop _ pe1 pe2 => loc_occ_pexpr pe1 `|` loc_occ_pexpr pe2
  | Pconst _         => fset0
  end.

Definition loc_occ_src (s : src) :=
  match s with
  | Imm pe => loc_occ_pexpr pe
  | Loc(l) => [fset l]
  end.

Fixpoint loc_occ_pcond (pc : pcond) :=
  match pc with
  | Ptrue           => fset0
  | Pnot pc         => loc_occ_pcond pc
  | Pand pc1 pc2    => loc_occ_pcond pc1 `|` loc_occ_pcond pc2
  | Pcond _ pe1 pe2 => loc_occ_pexpr pe1 `|` loc_occ_pexpr pe2
  end.

Fixpoint loc_occ_instr i :=
  match i with
  | Skip =>
      fset0
  | Seq i1 i2 =>
      loc_occ_instr i1 `|` loc_occ_instr i2
  | Assgn ds _ ss =>
      seq_fset ds `|` unions_seq (map loc_occ_src ss)
  | Call fd drets args => (* ignore fd here *)
      seq_fset (map (mkLoc None) drets) `|` unions_seq (map loc_occ_src args)
  | If pc i1 i2 =>
      loc_occ_pcond pc `|` loc_occ_instr i1 `|` loc_occ_instr i2
  | For id lb ub i =>
          [fset mkLoc None id]
      `|` loc_occ_pexpr lb `|` loc_occ_pexpr ub
      `|` loc_occ_instr i
  end.