(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat fintype finfun.
Require Import choice seq tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Printing Projections.

(* -------------------------------------------------------------------- *)
Local Notation efst := (@fst _ _).
Local Notation esnd := (@snd _ _).

Local Notation "f [@ b <- v ]" :=
  ([ffun x => if x == b then v else f x])
  (at level 20, format "f [@ b  <-  v ]").

(* -------------------------------------------------------------------- *)
Section GenFin.
Variable T : eqType.
Variable e : seq T.

Hypothesis total : forall x, x \in e.

Definition tonatr (x : T   ) := tag (seq_tnthP (total x)).
Definition ofnatr (i : 'I__) := tnth (in_tuple e) i.

Lemma tonatrK : cancel tonatr ofnatr.
Proof. by move=> x; rewrite /tonatr; case: seq_tnthP. Qed.
End GenFin.

(* -------------------------------------------------------------------- *)
Parameter w64 : eqType.

Parameter addc : w64 -> w64 -> bool -> (bool * w64).
Parameter mulc : w64 -> w64 -> (w64 * w64).

(* -------------------------------------------------------------------- *)
Inductive reg :=
  | RAX | RBX | RCX | RDX | RDI | RSI | RBP | RSP
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15.

Scheme Equality for reg.

Lemma reg_eqP r1 r2 : reflect (r1 = r2) (reg_beq r1 r2).
Proof. by apply/(iffP idP)=> [/internal_reg_dec_bl|/internal_reg_dec_lb]. Qed.

Definition reg_eqMixin := EqMixin reg_eqP.
Canonical  reg_eqType  := Eval hnf in EqType reg reg_eqMixin.

Definition regs := 
  [:: RAX; RBX; RCX; RDX; RDI; RSI; RBP; RSP;
      R8 ; R9 ; R10; R11; R12; R13; R14; R15].

Lemma total_regs x : x \in regs.
Proof. by case: x. Qed.

Definition reg_choiceMixin := CanChoiceMixin (tonatrK total_regs).
Canonical  reg_choiceType  := Eval hnf in ChoiceType reg reg_choiceMixin.
Definition reg_countMixin  := CanCountMixin (tonatrK total_regs).
Canonical  reg_countType   := Eval hnf in CountType reg reg_countMixin.
Definition reg_finMixin    := CanFinMixin (tonatrK total_regs).
Canonical  reg_finType     := Eval hnf in FinType reg reg_finMixin.

(* -------------------------------------------------------------------- *)
Inductive flagid := CF | ZF.

Scheme Equality for flagid.

Lemma flagid_eqP f1 f2 : reflect (f1 = f2) (flagid_beq f1 f2).
Proof. by apply/(iffP idP)=> [/internal_flagid_dec_bl|/internal_flagid_dec_lb]. Qed.

Definition flagid_eqMixin := EqMixin flagid_eqP.
Canonical  flagid_eqType  := Eval hnf in EqType flagid flagid_eqMixin.

Definition flagids := [:: CF; ZF].

Lemma total_flagids x : x \in flagids.
Proof. by case: x. Qed.

Definition flagid_choiceMixin := CanChoiceMixin (tonatrK total_flagids).
Canonical  flagid_choiceType  := Eval hnf in ChoiceType flagid flagid_choiceMixin.
Definition flagid_countMixin  := CanCountMixin (tonatrK total_flagids).
Canonical  flagid_countType   := Eval hnf in CountType flagid flagid_countMixin.
Definition flagid_finMixin    := CanFinMixin (tonatrK total_flagids).
Canonical  flagid_finType     := Eval hnf in FinType flagid flagid_finMixin.

(* -------------------------------------------------------------------- *)
Inductive  rvalue   := Imm of w64 | Reg of reg.
Definition cmovcond := (flagid * bool)%type.

Inductive instr :=
| ADC   of rvalue   & reg
| ADD   of rvalue   & reg
| MOV   of rvalue   & reg
| CMOV  of cmovcond & rvalue & reg
| MUL   of rvalue.

(* -------------------------------------------------------------------- *)
Record rstate := MkState {
  s_regs  : {ffun reg -> w64};
  s_flags : {ffun flagid -> option bool}
}.

Implicit Types f : flagid.
Implicit Types r : reg.

Definition get_flag ps f := ps.(s_flags) f.
Definition get_reg  ps r := ps.(s_regs ) r.

Definition set_flag ps f b :=
  {| s_regs  := ps.(s_regs);
     s_flags := ps.(s_flags)[@ f <- b] |}.

Definition set_reg ps r w :=
  {| s_flags := ps.(s_flags);
     s_regs  := ps.(s_regs)[@ r <- w] |}.

Definition get_ir ps ir :=
  match ir with
  | Imm w => w
  | Reg r => get_reg ps r
  end.

(* -------------------------------------------------------------------- *)
Notation "''C_' T" := (rstate -> option (rstate * T))
  (at level 8, T at level 2, format "''C_' T").

(* -------------------------------------------------------------------- *)
Definition munit {T : Type} (x : T) : 'C_T :=
  fun state => Some (state, x).

Definition mfail {T : Type} : 'C_T :=
  fun _ => None.

Definition mlet {T U : Type} (m1 : 'C_T) (m2 : T -> 'C_U) : 'C_U :=
  fun state =>
    if   m1 state is Some (state, x)
    then m2 x state
    else None.

(* -------------------------------------------------------------------- *)
Notation "'mlet' x := m1 'in' m2" := (mlet m1 (fun x => m2))
  (at level 50, m1, m2 at level 40, x ident,
     format "'mlet'  x  :=  m1  'in'  m2").

Notation "'mreturn' e" := (munit e)
  (at level 50, e at level 40, format "'mreturn'  e").

(* -------------------------------------------------------------------- *)
Definition mread : 'C_rstate :=
  fun state => Some (state, state).

Definition mwrite (new : rstate) : 'C_unit :=
  fun _ => Some (new, tt).

Definition mcomp {T : Type} (m : 'C_T) (state : rstate) :=
  m state.

Definition mexec {T : Type} (m : 'C_T) (state : rstate) :=
  omap efst (mcomp m state).

(* -------------------------------------------------------------------- *)
Definition mreadF (f : flagid) :=
  mlet state := mread in
    if get_flag state f is Some b then mreturn b else mfail.

Definition mreadR (r : reg) :=
  mlet state := mread in mreturn (get_reg state r).

(* -------------------------------------------------------------------- *)
Definition mwriteF (f : flagid) b :=
  mlet state := mread in mwrite (set_flag state f b).

Definition mwriteR (r : reg) w :=
  mlet state := mread in mwrite (set_reg state r w).

(* -------------------------------------------------------------------- *)
Definition mreadir ir :=
  mlet state := mread in mreturn (get_ir state ir).

(* -------------------------------------------------------------------- *)
Definition exec_ADD ir r cf :=
  mlet x := mreadir ir in
  mlet y := mreadR  r  in

  let (c, z) := addc x y cf in

  mlet _ := mwriteR r z in
  mlet _ := mwriteF CF (Some c) in

  mreturn tt.

Definition exec_ADC ir r :=
  mlet cf := mreadF CF in exec_ADD ir r cf.

Definition exec_MUL ir :=
  mlet x := mreadir ir in
  mlet y := mreadR RDX in

  let (z1, z2) := mulc x y in

  mlet _ := mwriteR RDX z1 in
  mlet _ := mwriteR RAX z2 in

  mreturn tt.

Definition exec_MOV ir r :=
  mlet x := mreadir ir in mwriteR r x.

Definition exec_CMOV c ir r :=
  mlet v := mreadF c.1 in
  if v == c.2 then exec_MOV ir r else mreturn tt.

(* -------------------------------------------------------------------- *)
Definition step i :=
  match i with
  | ADC  ir r   => exec_ADC  ir r
  | ADD  ir r   => exec_ADD  ir r false
  | MUL  ir     => exec_MUL  ir
  | CMOV c ir r => exec_CMOV c ir r
  | MOV  ir r   => exec_MOV  ir r
  end.

Fixpoint steps (s : seq instr) :=
  if s is i :: s then
    mlet _ := step i in steps s
  else
    mreturn tt.

(* -------------------------------------------------------------------- *)
Definition peq (rs : seq (reg * w64)) (fs : seq (flagid * option bool)) :=
  fun s1 s2 =>
    [/\ forall r, r \notin [seq x.1 | x <- rs] ->
          get_reg s1 r = get_reg s2 r
      , forall f, f \notin [seq x.1 | x <- fs] ->
          get_flag s1 f = get_flag s2 f
      , all [pred rs | get_reg  s2 rs.1 == rs.2] rs
      & all [pred fs | get_flag s2 fs.1 == fs.2] fs].

(* -------------------------------------------------------------------- *)
Lemma get_set_reg s r r' w:
    get_reg (set_reg s r w) r'
  = if r' == r then w else get_reg s r'.
Proof. by rewrite /set_reg /get_reg ffunE. Qed.

Lemma peq_setreg r w s: peq [:: (r, w)] [::] s (set_reg s r w).
Proof.
split=> //=; do? (apply/andP; split)=> //.
+ by move=> r'; rewrite mem_seq1 get_set_reg => /negbTE->.
+ by rewrite get_set_reg eqxx.
Qed.

(* -------------------------------------------------------------------- *)
Lemma MOV_P ir r s s' :
     mexec (step (MOV ir r)) s = Some s'
  -> peq [:: (r, get_ir s ir)] [::] s s'.
Proof. by case=> <-; apply/peq_setreg. Qed.
