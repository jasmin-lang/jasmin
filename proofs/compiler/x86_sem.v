(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
Require oseq.
Require Import memory word expr sem.
Import Utf8 Relation_Operators.
Import Memory.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ==================================================================== *)
Definition label := positive.

(* -------------------------------------------------------------------- *)
Variant register : Type :=
  | RAX | RCX | RDX | RBX | RSP | RBP | RSI | RDI
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15.

(* -------------------------------------------------------------------- *)
Variant rflag : Type := CF | PF | ZF | SF | OF | DF.

(* -------------------------------------------------------------------- *)
Variant scale : Type := Scale1 | Scale2 | Scale4 | Scale8.

(* -------------------------------------------------------------------- *)
(* disp + base + scale × offset *)
Record address : Type := mkAddress {
  ad_disp   : word;
  ad_base   : option register;
  ad_scale  : scale;
  ad_offset : option register;
}.

(* -------------------------------------------------------------------- *)
Variant oprd : Type :=
| Imm_op     of word
| Glo_op     of global
| Reg_op     of register
| Adr_op     of address.

Definition string_of_oprd (o: oprd) : string :=
  match o with
  | Imm_op x => "Imm"
  | Glo_op x => "Glo"
  | Reg_op x => "Reg"
  | Adr_op x => "Adr"
  end.

(* -------------------------------------------------------------------- *)
Variant ireg : Type :=
| Imm_ir of word
| Reg_ir of register.

(* -------------------------------------------------------------------- *)
Variant condt : Type :=
| O_ct                  (* overflow *)
| NO_ct                 (* not overflow *)
| B_ct                  (* below, not above or equal *)
| NB_ct                 (* not below, above or equal *)
| E_ct                  (* equal, zero *)
| NE_ct                 (* not equal, not zero *)
| BE_ct                 (* below or equal, not above *)
| NBE_ct                (* not below or equal, above *)
| S_ct                  (* sign *)
| NS_ct                 (* not sign *)
| P_ct                  (* parity, parity even *)
| NP_ct                 (* not parity, parity odd *)
| L_ct                  (* less than, not greater than or equal to *)
| NL_ct                 (* not less than, greater than or equal to *)
| LE_ct                 (* less than or equal to, not greater than *)
| NLE_ct                (* not less than or equal to, greater than *).

Definition string_of_condt (c: condt) : string :=
  match c with
  | O_ct => "O"
  | NO_ct => "NO"
  | B_ct => "B"
  | NB_ct => "NB"
  | E_ct => "E"
  | NE_ct => "NE"
  | BE_ct => "BE"
  | NBE_ct => "NBE"
  | S_ct => "S"
  | NS_ct => "NS"
  | P_ct => "P"
  | NP_ct => "NP"
  | L_ct => "L"
  | NL_ct => "NL"
  | LE_ct => "LE"
  | NLE_ct => "NLE"
  end.

(* -------------------------------------------------------------------- *)
Variant asm : Type :=
| LABEL of label

  (* Data transfert *)
| MOV    of         oprd & oprd    (* copy *)
| CMOVcc of condt & oprd & oprd    (* conditional copy *)

  (* Arithmetic *)
| ADD    of oprd & oprd            (* add unsigned / signed *)
| SUB    of oprd & oprd            (* sub unsigned / signed *)
| MUL    of oprd                   (* mul unsigned *)
| IMUL   of oprd & option (oprd * option word)
                                   (* mul signed with truncation *)
| DIV    of oprd                   (* div unsigned *)
| IDIV   of oprd                   (* div   signed *)

| ADC    of oprd & oprd            (* add with carry *)
| SBB    of oprd & oprd            (* sub with borrow *)

| NEG	of oprd	(* negation *)

| INC    of oprd                   (* increment *)
| DEC    of oprd                   (* decrement *)

  (* Flag *)
| SETcc  of condt & oprd           (* Set byte on condition *)
| BT of oprd & ireg              (* Bit test, sets result to CF *)

  (* Pointer arithmetic *)
| LEA    of register & oprd        (* Load Effective Address *)

  (* Comparison *)
| TEST   of oprd & oprd            (* Bit-wise logical and CMP *)
| CMP    of oprd & oprd            (* Signed sub CMP *)

  (* Jumps *)
| JMP    of label                  (* Unconditional jump *)
| Jcc    of label & condt          (* Conditional jump *)

  (* Bitwise logical instruction *)
| AND    of oprd & oprd            (* bit-wise and *)
| OR     of oprd & oprd            (* bit-wise or  *)
| XOR    of oprd & oprd            (* bit-wise xor *)
| NOT    of oprd                   (* bit-wise not *)

  (* Bit shifts *)
| SHL    of oprd & ireg            (* unsigned / left  *)
| SHR    of oprd & ireg            (* unsigned / right *)
| SAL    of oprd & ireg            (*   signed / left; synonym of SHL *)
| SAR    of oprd & ireg            (*   signed / right *)
| SHLD   of oprd & register & ireg (* unsigned (double) / left *)
.

(* -------------------------------------------------------------------- *)
Scheme Equality for register.
Scheme Equality for rflag.
Scheme Equality for scale.
Scheme Equality for condt.

Definition reg_eqMixin := comparableClass register_eq_dec.
Canonical reg_eqType := EqType register reg_eqMixin.

Definition rflag_eqMixin := comparableClass rflag_eq_dec.
Canonical rflag_eqType := EqType rflag rflag_eqMixin.

Definition scale_eqMixin := comparableClass scale_eq_dec.
Canonical scale_eqType := EqType scale scale_eqMixin.

Definition address_beq (addr1: address) addr2 :=
  match addr1, addr2 with
  | mkAddress d1 b1 s1 o1, mkAddress d2 b2 s2 o2 =>
    [&& d1 == d2, b1 == b2, s1 == s2 & o1 == o2]
  end.

Lemma address_eq_axiom : Equality.axiom address_beq.
Proof.
case=> [d1 b1 s1 o1] [d2 b2 s2 o2]; apply: (iffP idP) => /=.
+ by case/and4P; do 4! move/eqP=> ->.
by case; do 4! move=> ->; rewrite !eqxx.
Qed.

Definition address_eqMixin := Equality.Mixin address_eq_axiom.
Canonical address_eqType := EqType address address_eqMixin.

Definition oprd_beq (op1 op2 : oprd) :=
  match op1, op2 with
  | Imm_op w1, Imm_op w2 => w1 == w2
  | Glo_op g1, Glo_op g2 => g1 == g2
  | Reg_op r1, Reg_op r2 => r1 == r2
  | Adr_op a1, Adr_op a2 => a1 == a2
  | _        , _         => false
  end.

Lemma oprd_eq_axiom : Equality.axiom oprd_beq.
Proof.
case=> [w1| g1 |r1|a1] [w2| g2 |r2|a2] /=; try constructor => //;
  by apply (equivP eqP); split=> [->|[]].
Qed.

Definition oprd_eqMixin := Equality.Mixin oprd_eq_axiom.
Canonical oprd_eqType := EqType oprd oprd_eqMixin.

Definition condt_eqMixin := comparableClass condt_eq_dec.
Canonical condt_eqType := EqType condt condt_eqMixin.

(* -------------------------------------------------------------------- *)
Definition registers :=
  [:: RAX; RCX; RDX; RBX; RSP; RBP; RSI; RDI ;
      R8 ; R9 ; R10; R11; R12; R13; R14; R15 ].

Lemma registers_fin_axiom : Finite.axiom registers.
Proof. by case. Qed.

Definition reg_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK registers_fin_axiom).
Canonical reg_choiceType :=
  Eval hnf in ChoiceType register reg_choiceMixin.

Definition reg_countMixin :=
  PcanCountMixin (FinIsCount.pickleK registers_fin_axiom).
Canonical reg_countType :=
  Eval hnf in CountType register reg_countMixin.

Definition reg_finMixin :=
  FinMixin registers_fin_axiom.
Canonical reg_finType :=
  Eval hnf in FinType register reg_finMixin.

(* -------------------------------------------------------------------- *)
Definition rflags := [:: CF; PF; ZF; SF; OF; DF].

Lemma rflags_fin_axiom : Finite.axiom rflags.
Proof. by case. Qed.

Definition rflag_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK rflags_fin_axiom).
Canonical rflag_choiceType :=
  Eval hnf in ChoiceType rflag rflag_choiceMixin.

Definition rflag_countMixin :=
  PcanCountMixin (FinIsCount.pickleK rflags_fin_axiom).
Canonical rflag_countType :=
  Eval hnf in CountType rflag rflag_countMixin.

Definition rflag_finMixin :=
  FinMixin rflags_fin_axiom.
Canonical rflag_finType :=
  Eval hnf in FinType rflag rflag_finMixin.

(* -------------------------------------------------------------------- *)
Module RegMap.
  Definition map := {ffun register -> word}.

  Definition set (m : map) (x : register) (y : word) : map :=
    [ffun z => if (z == x) then y else m z].
End RegMap.

(* -------------------------------------------------------------------- *)
Module RflagMap.
  Variant rflagv := Def of bool | Undef.

  Definition map := {ffun rflag -> rflagv}.

  Definition set (m : map) (x : rflag) (y : bool) : map :=
    [ffun z => if (z == x) then Def y else m z].

  Definition oset (m : map) (x : rflag) (y : rflagv) : map :=
    [ffun z => if (z == x) then y else m z].

  Definition update (m : map) (f : rflag -> option rflagv) : map :=
    [ffun rf => odflt (m rf) (f rf)].
End RflagMap.

(* -------------------------------------------------------------------- *)
Notation regmap   := RegMap.map.
Notation rflagmap := RflagMap.map.
Notation Def      := RflagMap.Def.
Notation Undef    := RflagMap.Undef.

Definition regmap0   : regmap   := [ffun x => I64.repr 0].
Definition rflagmap0 : rflagmap := [ffun x => Undef].

(* -------------------------------------------------------------------- *)
Record x86_mem : Type :=
  X86Mem {
      xmem : mem;
      xreg : regmap;
      xrf : rflagmap;
    }.

Record x86_state := X86State {
  xm :> x86_mem;
  xc   : seq asm;
  xip  : nat;
}.

Notation x86_result := (result error x86_mem).
Notation x86_result_state := (result error x86_state).

(* -------------------------------------------------------------------- *)
Section GLOB_DEFS.

Context (gd: glob_defs).

(* -------------------------------------------------------------------- *)
Definition mem_write_reg (r: register) (w: word) (m: x86_mem) :=
  {|
    xmem := m.(xmem);
    xreg := RegMap.set m.(xreg) r w;
    xrf  := m.(xrf);
  |}.

Definition st_write_reg (r : register) (w : word) (s : x86_state) :=
  {| xm := mem_write_reg r w s;
     xc   := s.(xc);
     xip  := s.(xip); |}.

(* -------------------------------------------------------------------- *)
Definition st_get_rflag (rf : rflag) (s : x86_mem) :=
  if s.(xrf) rf is Def b then ok b else undef_error.

(* -------------------------------------------------------------------- *)
Definition mem_set_rflags (rf : rflag) (b : bool) (s : x86_mem) :=
  {|
    xmem := s.(xmem);
    xreg := s.(xreg);
    xrf  := RflagMap.set s.(xrf) rf b;
  |}.

Definition mem_unset_rflags (rf : rflag) (s : x86_mem) :=
  {|
    xmem := s.(xmem);
    xreg := s.(xreg);
    xrf  := RflagMap.oset s.(xrf) rf Undef;
  |}.

Definition st_set_rflags (rf : rflag) (b : bool) (s : x86_state) :=
  {| xm := mem_set_rflags rf b s;
     xc   := s.(xc);
     xip  := s.(xip); |}.

(* -------------------------------------------------------------------- *)
Definition mem_update_rflags f (s : x86_mem) :=
  {| xmem := s.(xmem);
     xreg := s.(xreg);
     xrf  := RflagMap.update s.(xrf) f;
     |}.

Definition st_update_rflags f (s : x86_state) :=
  {| xm := mem_update_rflags f s;
     xc   := s.(xc);
     xip  := s.(xip); |}.

(* -------------------------------------------------------------------- *)
Definition mem_write_mem (l : word) (w : word) (s : x86_mem) :=
  Let m := write_mem s.(xmem) l w in ok
  {| xmem := m;
     xreg := s.(xreg);
     xrf  := s.(xrf);
  |}.

Definition st_write_mem (l : word) (w : word) (s : x86_state) :=
  Let m := mem_write_mem l w s in ok
  {| xm := m;
     xc   := s.(xc);
     xip  := s.(xip); |}.

(* -------------------------------------------------------------------- *)
Definition st_write_ip (ip : nat) (s : x86_state) :=
  {| xm := s.(xm);
     xc   := s.(xc);
     xip  := ip; |}.

(* -------------------------------------------------------------------- *)
Coercion word_of_scale (s : scale) : word :=
  I64.repr match s with
  | Scale1 => 1
  | Scale2 => 2
  | Scale4 => 4
  | Scale8 => 8
  end.

(* -------------------------------------------------------------------- *)
Definition decode_addr (s : x86_mem) (a : address) : word := nosimpl (
  let: disp   := a.(ad_disp) in
  let: base   := odflt I64.zero (omap (s.(xreg)) a.(ad_base)) in
  let: scale  := word_of_scale a.(ad_scale) in
  let: offset := odflt I64.zero (omap (s.(xreg)) a.(ad_offset)) in

  I64.add disp (I64.add base (I64.mul scale offset))).

(* -------------------------------------------------------------------- *)
Definition write_oprd (o : oprd) (w : word) (s : x86_mem) :=
  match o with
  | Glo_op _
  | Imm_op _ => type_error
  | Reg_op r => ok (mem_write_reg r w s)
  | Adr_op a => mem_write_mem (decode_addr s a) w s
  end.

(* -------------------------------------------------------------------- *)
Definition read_oprd (o : oprd) (s : x86_mem) :=
  match o with
  | Imm_op v => ok v
  | Glo_op g => if get_global_word gd g is Some v then ok v else type_error
  | Reg_op r => ok (s.(xreg) r)
  | Adr_op a => read_mem s.(xmem) (decode_addr s a)
  end.

(* -------------------------------------------------------------------- *)
Definition read_ireg (ir : ireg) (s : x86_mem) :=
  match ir with
  | Imm_ir v => v
  | Reg_ir r => s.(xreg) r
  end.

(* -------------------------------------------------------------------- *)
Definition eval_cond (c : condt) (rm : rflagmap) :=
  let get rf :=
    if rm rf is Def b then ok b else undef_error in

  match c with
  | O_ct   => get OF
  | NO_ct  => Let b := get OF in ok (~~ b)
  | B_ct   => get CF
  | NB_ct  => Let b := get CF in ok (~~ b)
  | E_ct   => get ZF
  | NE_ct  => Let b := get ZF in ok (~~ b)
  | S_ct   => get SF
  | NS_ct  => Let b := get SF in ok (~~ b)
  | P_ct   => get PF
  | NP_ct  => Let b := get PF in ok (~~ b)

  | BE_ct =>
      Let cf := get CF in
      Let zf := get ZF in ok (cf || zf)

  | NBE_ct =>
      Let cf := get CF in
      Let zf := get ZF in ok (~~ cf && ~~ zf)

  | L_ct =>
      Let sf  := get SF in
      Let of_ := get OF in ok (sf != of_)

  | NL_ct =>
      Let sf  := get SF in
      Let of_ := get OF in ok (sf == of_)

  | LE_ct =>
      Let zf  := get ZF in
      Let sf  := get SF in
      Let of_ := get OF in ok (zf || (sf != of_))

  | NLE_ct =>
      Let zf  := get ZF in
      Let sf  := get SF in
      Let of_ := get OF in ok (~~ zf && (sf == of_))
  end.

(* -------------------------------------------------------------------- *)
Definition is_label (lbl: label) (i: asm) : bool :=
  match i with
  | LABEL lbl' => lbl == lbl'
  | _ => false
  end.

(* -------------------------------------------------------------------- *)
Definition find_label (lbl : label) (a : seq asm) :=
  let idx := seq.find (is_label lbl) a in
  if idx < size a then ok idx else type_error.

(* -------------------------------------------------------------------- *)
Definition SF_of_word (w : word) :=
  msb w.

(* -------------------------------------------------------------------- *)
Definition PF_of_word (w : word) :=
  lsb w.

(* -------------------------------------------------------------------- *)
Definition ZF_of_word (w : word) :=
  I64.eq w I64.zero.

(* -------------------------------------------------------------------- *)
Definition rflags_of_bwop (w : word) := fun rf =>
  match rf with
  | OF => Some (Def false)
  | CF => Some (Def false)
  | SF => Some (Def (SF_of_word w))
  | PF => Some (Def (PF_of_word w))
  | ZF => Some (Def (ZF_of_word w))
  | DF => None
  end.

(* -------------------------------------------------------------------- *)
Definition rflags_of_aluop (w : word) (vu vs : Z) := fun rf =>
  match rf with
  | OF => Some (Def (I64.signed   w != vs))
  | CF => Some (Def (I64.unsigned w != vu))
  | SF => Some (Def (SF_of_word w))
  | PF => Some (Def (PF_of_word w))
  | ZF => Some (Def (ZF_of_word w))
  | DF => None
  end.

(* -------------------------------------------------------------------- *)
Definition rflags_of_aluop_nocf (w : word) (vs : Z) := fun rf =>
  match rf with
  | CF => None
  | OF => Some (Def (I64.signed w != vs))
  | SF => Some (Def (SF_of_word w))
  | PF => Some (Def (PF_of_word w))
  | ZF => Some (Def (ZF_of_word w))
  | DF => None
  end.

(* --------------------------------------------------------------------- *)
Definition rflags_of_mul (ov : bool) := fun rf =>
  match rf with
  | SF | ZF | PF => Some Undef
  | OF | CF => Some (Def ov)
  | DF => None
  end.

(* --------------------------------------------------------------------- *)
Definition rflags_of_div := fun rf =>
  match rf with
  | SF | ZF | PF | OF | CF => Some Undef
  | DF => None
  end.

(* -------------------------------------------------------------------- *)
Definition rflags_of_sh i of_ r rc := fun rf =>
  match rf with
  | OF => Some (if i == I64.one then Def of_ else Undef)
  | CF => Some (Def rc)
  | SF => Some (Def (SF_of_word r))
  | PF => Some (Def (PF_of_word r))
  | ZF => Some (Def (ZF_of_word r))
  | _  => None
  end.

(* --------------------------------------------------------------------- *)
Definition all_undef := fun rf =>
  match rf with
  | SF | ZF | PF | OF | CF => Some Undef
  | DF => None
  end.


(* -------------------------------------------------------------------- *)
Implicit Types (ct : condt) (s : x86_mem) (o : oprd) (ir : ireg).
Implicit Types (lbl : label).

(* -------------------------------------------------------------------- *)
Definition eval_MOV o1 o2 s : x86_result :=
  Let v := read_oprd o2 s in
  write_oprd o1 v s.

(* -------------------------------------------------------------------- *)
Definition eval_CMOVcc ct o1 o2 s : x86_result :=
  Let b := eval_cond ct s.(xrf) in
  if b then eval_MOV o1 o2 s else ok s.

(* -------------------------------------------------------------------- *)
Definition eval_ADD o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  let v  := I64.add v1 v2 in
  let vu := (I64.unsigned v1 + I64.unsigned v2)%Z in
  let vs := (I64.signed   v1 + I64.signed   v2)%Z in
  let s  := mem_update_rflags (rflags_of_aluop v vu vs) s in
  write_oprd o1 v s.

(* -------------------------------------------------------------------- *)
Definition eval_SUB o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  let v  := I64.sub v1 v2 in
  let vu := (I64.unsigned v1 - I64.unsigned v2)%Z in
  let vs := (I64.signed   v1 - I64.signed   v2)%Z in
  let s  := mem_update_rflags (rflags_of_aluop v vu vs) s in
  write_oprd o1 v s.

(* -------------------------------------------------------------------- *)
Definition eval_MUL o s : x86_result :=
  let v1 := s.(xreg) RAX in
  Let v2 := read_oprd o s in
  let lo := I64.mul v1 v2 in
  let hi := I64.mulhu v1 v2 in
  let ov := dwordu hi lo in
  let ov := (ov >? I64.max_unsigned)%Z in
  let s  := mem_update_rflags (rflags_of_mul ov) s in
  let s  := mem_write_reg RDX hi s in
  let s  := mem_write_reg RAX lo s in
  ok s.

(* -------------------------------------------------------------------- *)
Definition eval_IMUL o1 (o2 : option (oprd * option word)) s : x86_result  :=
  match o2 with
  | None =>
      let v1 := s.(xreg) RAX in
      Let v2 := read_oprd o1 s in
      let lo := I64.mul v1 v2 in
      let hi := I64.mulhs v1 v2 in
      let ov := dwords hi lo in
      let ov := (ov <? I64.min_signed)%Z || (ov >? I64.max_unsigned)%Z in
      let s  := mem_update_rflags (rflags_of_mul ov) s in
      let s  := mem_write_reg RDX hi s in
      let s  := mem_write_reg RAX lo s in
      ok s

  | Some (o2, None) =>
      Let v1 := read_oprd o1 s in
      Let v2 := read_oprd o2 s in
      let lo := I64.mul v1 v2 in
      let hi := I64.mulhs v1 v2 in
      let ov := dwords hi lo in
      let ov := (ov <? I64.min_signed)%Z || (ov >? I64.max_unsigned)%Z in
      let s  := mem_update_rflags (rflags_of_mul ov) s in
      write_oprd o1 lo s

   | Some (o2, Some v2) =>
      Let v1 := read_oprd o2 s in
      let lo := I64.mul v1 v2 in
      let hi := I64.mulhs v1 v2 in
      let ov := dwords hi lo in
      let ov := (ov <? I64.min_signed)%Z || (ov >? I64.max_unsigned)%Z in
      let s  := mem_update_rflags (rflags_of_mul ov) s in
      write_oprd o1 lo s
  end.

(* -------------------------------------------------------------------- *)
Definition eval_DIV o s : x86_result :=
  let hi := s.(xreg) RDX in
  let lo := s.(xreg) RAX in
  let dd := dwordu hi lo in
  Let dv := read_oprd o s in
  let dv := I64.unsigned dv in
  let q  := (dd  /  dv)%Z in
  let r  := (dd mod dv)%Z in
  let ov := (q >? I64.max_unsigned)%Z in

  if (dv == 0)%Z || ov then type_error else

  let s := mem_write_reg RAX (I64.repr q) s in
  let s := mem_write_reg RDX (I64.repr r) s in

  ok (mem_update_rflags rflags_of_div s).

(* -------------------------------------------------------------------- *)
Definition eval_IDIV o s : x86_result :=
  let hi := s.(xreg) RDX in
  let lo := s.(xreg) RAX in
  let dd := dwords hi lo in
  Let dv := read_oprd o s in
  let dv := I64.signed dv in
  let q  := (Z.quot dd dv)%Z in
  let r  := (Z.rem  dd dv)%Z in
  let ov := (q <? I64.min_signed)%Z || (q >? I64.max_signed)%Z in

  if (dv == 0)%Z || ov then type_error else

  let s := mem_write_reg RAX (I64.repr q) s in
  let s := mem_write_reg RDX (I64.repr r) s in

  ok (mem_update_rflags rflags_of_div s).

(* -------------------------------------------------------------------- *)
Definition eval_ADC o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  Let c  := st_get_rflag CF s in
  let c  := if c then I64.one else I64.zero in
  let v  := add_carry v1 v2 c in
  let vu := (I64.unsigned v1 + I64.unsigned v2 + (c : Z))%Z in
  let vs := (I64.signed   v1 + I64.signed   v2 + (c : Z))%Z in
  let s  := mem_update_rflags (rflags_of_aluop v vu vs) s in
  write_oprd o1 v s.

(* -------------------------------------------------------------------- *)
Definition eval_SBB o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  Let c  := st_get_rflag CF s in
  let c  := if c then I64.one else I64.zero in
  let v  := sub_borrow v1 v2 c in
  let vu := (I64.unsigned v1 - (I64.unsigned v2 + (c : Z)))%Z in
  let vs := (I64.signed   v1 - (I64.signed   v2 + (c : Z)))%Z in
  let s  := mem_update_rflags (rflags_of_aluop v vu vs) s in
  write_oprd o1 v s.

(* -------------------------------------------------------------------- *)
Definition eval_NEG o s : x86_result :=
  Let w  := read_oprd o s in
  let v  := I64.neg w in
  let vs := (- I64.signed w)%Z in
  let s  :=
      mem_update_rflags (
          fun rf =>
          match rf with
          | CF => Some (Def (negb (I64.eq w I64.zero)))
          | _ => rflags_of_aluop_nocf v vs rf
          end) s
  in write_oprd o v s.

(* -------------------------------------------------------------------- *)
Definition eval_INC o s : x86_result :=
  Let w  := read_oprd o s in
  let v  := I64.add w I64.one in
  let vs := (I64.signed w + 1)%Z in
  let s  := mem_update_rflags (rflags_of_aluop_nocf v vs) s in
  write_oprd o v s.

(* -------------------------------------------------------------------- *)
Definition eval_DEC o s : x86_result :=
  Let w  := read_oprd o s in
  let v  := I64.sub w I64.one in
  let vs := (I64.signed w - 1)%Z in
  let s  := mem_update_rflags (rflags_of_aluop_nocf v vs) s in
  write_oprd o v s.

(* -------------------------------------------------------------------- *)
Definition eval_SETcc ct o s : x86_result :=
  Let b := eval_cond ct s.(xrf) in
  write_oprd o (if b then I64.one else I64.zero) s.

(* -------------------------------------------------------------------- *)
Definition eval_BT o ir s : x86_result :=
  Let v1 := read_oprd o s in
  let v2 := read_ireg ir s in
  let b  := I64.and v1 (I64.shl I64.one v2) != I64.zero in
  ok (mem_set_rflags CF b s).

(* -------------------------------------------------------------------- *)
Definition eval_LEA r o2 s : x86_result :=
  Let addr :=
    match o2 with
    | Imm_op w => ok w
    | Adr_op a => ok (decode_addr s a)
    | _        => type_error
    end in
  ok (mem_write_reg r addr s).

(* -------------------------------------------------------------------- *)
Definition eval_TEST o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  let v  := I64.and v1 v2 in
  ok (mem_update_rflags (rflags_of_bwop v) s).

(* -------------------------------------------------------------------- *)
Definition eval_CMP o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  let v  := I64.sub v1 v2 in
  let vu := (I64.unsigned v1 - I64.unsigned v2)%Z in
  let vs := (I64.signed   v1 - I64.signed   v2)%Z in
  ok (mem_update_rflags (rflags_of_aluop v vu vs) s).

(* -------------------------------------------------------------------- *)
Definition eval_AND o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  let v  := I64.and v1 v2 in
  let s  := mem_update_rflags (rflags_of_bwop v) s in
  write_oprd o1 v s.

(* -------------------------------------------------------------------- *)
Definition eval_OR o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  let v  := I64.or v1 v2 in
  let s  := mem_update_rflags (rflags_of_bwop v) s in
  write_oprd o1 v s.

(* -------------------------------------------------------------------- *)
Definition eval_XOR o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  let v  := I64.xor v1 v2 in
  let s  := mem_update_rflags (rflags_of_bwop v) s in
  write_oprd o1 v s.

(* -------------------------------------------------------------------- *)
Definition eval_NOT o s : x86_result :=
  Let v := read_oprd o s in write_oprd o (I64.not v) s.

(* -------------------------------------------------------------------- *)
Definition eval_SHL o ir s : x86_result :=
  Let v := read_oprd o s in
  let i := I64.and (read_ireg ir s) x86_shift_mask in

  if i == I64.zero then ok (mem_update_rflags all_undef s) else
    let rc := msb (I64.shl v (I64.sub i I64.one)) in
    let r  := I64.shl v i in
    let s  := mem_update_rflags (rflags_of_sh i (msb r (+) rc) r rc) s in
    write_oprd o r s.

(* -------------------------------------------------------------------- *)
Definition eval_SHLD o1 r2 ir s : x86_result :=
  Let v1 := read_oprd o1 s in
  let v2 := s.(xreg) r2 in
  let i := I64.and (read_ireg ir s) x86_shift_mask in

  if i == I64.zero then ok (mem_update_rflags all_undef s) else
    let rc := msb (I64.shl v1 (I64.sub i I64.one)) in
    let r1 := I64.shl v1 i in
    let r2 := I64.shr v2 (I64.sub (I64.repr I64.zwordsize) i) in
    let r  := I64.or r1 r2 in
    let s  := mem_update_rflags (rflags_of_sh i (msb r (+) rc) r rc) s in
    write_oprd o1 r s.

(* -------------------------------------------------------------------- *)
Definition eval_SHR o ir s : x86_result :=
  Let v := read_oprd o s in
  let i := I64.and (read_ireg ir s) x86_shift_mask in

  if i == I64.zero then ok (mem_update_rflags all_undef s) else
    let rc := lsb (I64.shru v (I64.sub i I64.one)) in
    let r  := I64.shru v i in
    let s  := mem_update_rflags (rflags_of_sh i (msb r) r rc) s in
    write_oprd o r s.

(* -------------------------------------------------------------------- *)
Definition eval_SAL o ir s : x86_result :=
  eval_SHL o ir s.

(* -------------------------------------------------------------------- *)
Definition eval_SAR o ir s : x86_result :=
  Let v := read_oprd o s in
  let i := I64.and (read_ireg ir s) x86_shift_mask in

  if i == I64.zero then ok (mem_update_rflags all_undef s) else
    let rc := lsb (I64.shr v (I64.sub i I64.one)) in
    let r  := I64.shr v i in
    let s  := mem_update_rflags (rflags_of_sh i false r rc) s
    in write_oprd o r s.

(* -------------------------------------------------------------------- *)
Definition eval_JMP lbl (s: x86_state) : x86_result_state :=
  Let ip := find_label lbl s.(xc) in ok (st_write_ip ip.+1 s).

(* -------------------------------------------------------------------- *)
Definition eval_Jcc lbl ct (s: x86_state) : x86_result_state :=
  Let b := eval_cond ct s.(xrf) in
  if b then eval_JMP lbl s else ok (st_write_ip (xip s).+1 s).

(* -------------------------------------------------------------------- *)
Definition eval_instr_mem (i : asm) s : x86_result :=
  match i with
  | JMP    _
  | Jcc    _ _
  | LABEL  _        => ok s
  | MOV    o1 o2    => eval_MOV o1 o2 s
  | CMOVcc ct o1 o2 => eval_CMOVcc ct o1 o2 s
  | ADD    o1 o2    => eval_ADD o1 o2 s
  | SUB    o1 o2    => eval_SUB o1 o2 s
  | MUL    o        => eval_MUL o s
  | IMUL   o1 o2i   => eval_IMUL o1 o2i s
  | DIV    o        => eval_DIV o s
  | IDIV   o        => eval_IDIV o s
  | ADC    o1 o2    => eval_ADC o1 o2 s
  | SBB    o1 o2    => eval_SBB o1 o2 s
  | NEG    o        => eval_NEG o s
  | INC    o        => eval_INC o s
  | DEC    o        => eval_DEC o s
  | SETcc  ct o     => eval_SETcc ct o s
  | BT o ir => eval_BT o ir s
  | LEA    o1 o2    => eval_LEA o1 o2 s
  | TEST   o1 o2    => eval_TEST o1 o2 s
  | CMP    o1 o2    => eval_CMP o1 o2 s
  | AND    o1 o2    => eval_AND o1 o2 s
  | OR     o1 o2    => eval_OR o1 o2 s
  | XOR    o1 o2    => eval_XOR o1 o2 s
  | NOT    o        => eval_NOT o s
  | SHL    o ir     => eval_SHL o ir s
  | SHR    o ir     => eval_SHR o ir s
  | SAL    o ir     => eval_SAL o ir s
  | SAR    o ir     => eval_SAR o ir s
  | SHLD   o1 o2 ir => eval_SHLD o1 o2 ir s
  end.

Definition eval_instr (i : asm) (s: x86_state) : x86_result_state :=
  match i with
  | LABEL  _        => ok (st_write_ip (xip s).+1 s)
  | JMP    lbl      => eval_JMP lbl s
  | Jcc    lbl ct   => eval_Jcc lbl ct s
  | _ =>
    Let m := eval_instr_mem i s in
    ok {|
        xm := m;
        xc := s.(xc);
        xip := s.(xip).+1
      |}
  end.

(* -------------------------------------------------------------------- *)
Definition fetch_and_eval (s: x86_state) :=
  if oseq.onth s.(xc) s.(xip) is Some i then
    eval_instr i s
  else type_error.

Definition x86sem1 (s1 s2: x86_state) : Prop :=
  fetch_and_eval s1 = ok s2.

Definition x86sem : relation x86_state := clos_refl_trans x86_state x86sem1.

End GLOB_DEFS.

(* -------------------------------------------------------------------- *)
Record xfundef := XFundef {
 xfd_stk_size : Z;
 xfd_nstk : register;
 xfd_arg  : seq register;
 xfd_body : seq asm;
 xfd_res  : seq register;
}.

Definition xprog : Type :=
  seq (funname * xfundef).

Definition mem_write_regs m rs vs :=
    foldl (λ m rv, let '(r,v) := rv in mem_write_reg r v m) m (zip rs vs).

Lemma mem_write_regs_cons m r rs v vs :
  mem_write_regs m (r :: rs) (v :: vs) =
  mem_write_regs (mem_write_reg r v m) rs vs.
Proof. by []. Qed.

(* FIXME: initial register map *)
Variant x86sem_fd (P: xprog) (gd: glob_defs) m1 fn va m2 vr : Prop :=
| X86Sem_fd fd p m2'
    `(get_fundef P fn = Some fd)
    `(alloc_stack m1 fd.(xfd_stk_size) = ok p)
    (c := fd.(xfd_body))
    (m1' := mem_write_reg fd.(xfd_nstk) p.1 {| xmem := p.2 ; xreg := regmap0 ; xrf := rflagmap0 |})
    `(size va = size fd.(xfd_arg))
    (m1'' := mem_write_regs m1' fd.(xfd_arg) va)
    `(x86sem gd {| xm := m1'' ; xc := c ; xip := 0 |} {| xm := m2'; xc := c; xip := size c |})
    `(vr = map (λ r, m2'.(xreg) r) fd.(xfd_res))
    `(m2 = free_stack m2'.(xmem) p.1 fd.(xfd_stk_size))
    : x86sem_fd P gd m1 fn va m2 vr.

Definition x86sem_trans gd s2 s1 s3 :
  x86sem gd s1 s2 -> x86sem gd s2 s3 -> x86sem gd s1 s3 :=
  rt_trans _ _ s1 s2 s3.
