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
  | Call fargs frets fbody drets args => (* ignore fd here *)
      seq_fset drets `|` unions_seq (map id_occ_src args)
  | If pc i1 i2 =>
      id_occ_pcond pc `|` id_occ_instr i1 `|` id_occ_instr i2
  | For id lb ub i =>
          id
       |` id_occ_pexpr lb `|` id_occ_pexpr ub
      `|` id_occ_instr i
  end.

(* ** Irrelevant local variables for eval_instr
 * -------------------------------------------------------------------- *)

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

Lemma oeq_on_write_loc_eq lm1 lm2 loc sval ids:
  id_occ_loc loc `<=` ids ->
  lm1 = lm2 [& ids] ->
  write_loc lm1 loc sval = write_loc lm2 loc sval [&& ids].
Proof.
case loc => /=; case => pe; last first.
rewrite /id_occ_loc /= /write_loc => Hsub Heq.
+ by apply eq_on_setf_same.
rewrite /id_occ_loc /write_loc => id.
case sval => //= w Hsub Heq.
move: (Hsub). rewrite /= fsubUset; move/andP => [] Hsub1 Hsub2.
(* FIXME: move: (eq_on_read_loc_eq Heq) hangs here *)
have ->:   read_loc lm1 {| l_oidx := Some pe; l_id := id |}
         = read_loc lm2 {| l_oidx := Some pe; l_id := id |} => /=.
+ apply: eq_on_read_loc_eq; rewrite /id_occ_loc //=.
  by apply: (eq_on_fsubset Hsub).
case (read_loc _ _) => //=; last first.
+ rewrite (@eq_on_eval_pexpr_eq pe lm1 lm2) => //=.
  + case (eval_pexpr _ _) => //= w2.
    by apply: eq_on_setf_same.
  by apply: (eq_on_fsubset Hsub2).  
case => //= a.
+ rewrite (@eq_on_eval_pexpr_eq pe lm1 lm2) => //=.
  case (eval_pexpr _ _) => //= w2.
  by apply: eq_on_setf_same.
by apply: (eq_on_fsubset Hsub2).
Qed.

Lemma oeq_on_write_locs_eq locs ids:
  forall lm1 lm2 svals,
    unions_seq [seq id_occ_loc i | i <- locs] `<=` ids -> 
    lm1 = lm2 [& ids] ->
    write_locs lm1 locs svals = write_locs lm2 locs svals [&& ids].
Proof.
elim: locs => //=.
+ by move=> lm1 lm2 svals; case svals => //=.
move=> loc locs IH lm1 lm2 svals Hsub Heq.
move: Hsub. rewrite /= fsubUset; move/andP => [] Hsub1 Hsub2.
case svals => //= sv svs.
apply:
  (@oeq_on_obind _ _
     (fun lm => write_loc lm loc sv) (fun lm => write_locs lm locs svs)
     lm1 lm2 ids Heq).
+ by apply: oeq_on_write_loc_eq.
move=> lm1_ lm2_ Heq_.
by apply: (@IH lm1_ lm2_ svs Hsub2 Heq_).
Qed.

Lemma unions_set_map_fset1 (aT : choiceType) (vs : seq aT):
  unions_seq (map fset1 vs) = seq_fset vs.
Proof.
elim: vs; last by move=> v vs; rewrite /= fset_cons => ->.
by rewrite /=; apply/fsetP => x; rewrite in_seq_fsetE in_fset0 in_nil.
Qed.

Lemma oeq_on_eval_instr_eq (i : instr):
  forall (lm1 lm2 : lmap) (ids : {fset ident}) ,
    id_occ_instr i `<=` ids ->
    lm1 = lm2 [&ids]->
    eval_instr lm1 i = eval_instr lm2 i [&& ids].
Proof.
move: i; elim/instr_ind.
  (* Skip *)
+ by move=> lm1 lm2; rewrite /= /eq_on; move=> ids Hsub ->.
  (* Seq *)
+ move=> i1 Hi1 i2 Hi2 lm1 lm2 ids.
  rewrite /= fsubUset => Hsub Heq. move/andP: Hsub => [Hsub1 Hsub2].
  apply: (@oeq_on_obind _ _ (fun lm => eval_instr lm i1) (fun lm => eval_instr lm i2)
             lm1 lm2 ids) => //=.
  + by apply: Hi1.
  + by move=> lm1_ lm2_; apply: Hi2.
  (* Assgn *)
+ move=> dlocs op srcs lm1 lm2 ids => /=.
  rewrite fsubUset; move/andP => [Hsub1 Hsub2] Heq.
  rewrite (@eq_on_mapM_read_src_eq srcs lm1 lm2 ids Heq Hsub2).
  case (mapM _ _) => //= loc.
  case (eval_op op loc) => //= svals.
  by apply: oeq_on_write_locs_eq.
  (* If *)
+ move=> pc i1 Hi1 i2 Hi2 lm1 lm2 ids.
  rewrite /= !fsubUset. move/andP => []. move/andP => [] Hsub1 Hsub2 Hsub3 Heq.
  have ->: eval_pcond lm1 pc = eval_pcond lm2 pc.
  + apply: eq_on_eval_pcond_eq.
    by apply: (eq_on_fsubset Hsub1).
  case (eval_pcond lm2 pc) => /= ; last done.
  by move=> b; case b; [apply Hi1 | apply Hi2].
  (* For *)
+ move=> id pe1 pe2 instr IH lm1 lm2 ids Hsub Heq.
  move: (Hsub); rewrite /= !fsubUset.
  move/andP => [Hsub123 Hsub4]. move/andP: Hsub123 => [Hsub12 Hsub3].
  move/andP: Hsub12 => [Hsub1 Hsub2].
  rewrite (@eq_on_eval_pexpr_eq pe1 lm1 lm2); last first.
  + by apply: (eq_on_fsubset Hsub2).
  case (eval_pexpr lm2 _) => //= w1.
  rewrite (@eq_on_eval_pexpr_eq pe2 lm1 lm2); last first.
  + by apply: (eq_on_fsubset Hsub3).
  case (eval_pexpr lm2 _) => //= w2.
  set ws := [seq n2w n | n <- list_from_to (w2n w1) (w2n w2)].
  apply: (@oeq_on_ofold _ _ _
             (fun j lm => eval_instr lm.[id <- Vword j] instr) ids ws lm1 lm2 Heq).
  move=> lm1_ lm2_ w_ Hin HeqOn.
  apply IH; first done.
  by rewrite /eq_on !restrictf_set HeqOn.
  (* Call *)
+ move=> f_rets f_args f_body IH rets args lm1 lm2 ids.
  rewrite /= => Hsub Heq. move: (Hsub); rewrite /= !fsubUset.
  move/andP => [Hsub1 Hsub2].
  rewrite (@eq_on_mapM_read_src_eq args lm1 lm2 ids Heq Hsub2).
  case (mapM _ _) => //= svals.
  case (write_locs _ _ _) => //= lm_call.
  case (eval_instr _ _) => //= lm_call_.
  case (mapM _ _) => //= svals_.
  apply: oeq_on_write_locs_eq => //=.
  rewrite -map_comp.
  have Hfeq: id_occ_loc \o mkLoc None =1 (fun x => [fset x]).
  + by move=> x; rewrite /comp /id_occ_loc /= fsetU0.
  have ->: map (id_occ_loc \o mkLoc None) rets = map fset1 rets.
  + by rewrite -eq_in_map; case => //; rewrite /comp /id_occ_loc /= fsetU0.
  by rewrite unions_set_map_fset1.
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
  | Call fargs frets fbody drets args => (* ignore fd here *)
      seq_fset (map (mkLoc None) drets) `|` unions_seq (map loc_occ_src args)
  | If pc i1 i2 =>
      loc_occ_pcond pc `|` loc_occ_instr i1 `|` loc_occ_instr i2
  | For id lb ub i =>
          [fset mkLoc None id]
      `|` loc_occ_pexpr lb `|` loc_occ_pexpr ub
      `|` loc_occ_instr i
  end.