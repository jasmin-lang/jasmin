From mathcomp Require Import all_ssreflect all_algebra.
Require Import low_memory x86_sem x86_decl compiler_util lowering.
Import Utf8 String.
Import all_ssreflect.
Import xseq expr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition string_of_register r :=
  match r with
  | RAX => "RAX"
  | RCX => "RCX"
  | RDX => "RDX"
  | RBX => "RBX"
  | RSP => "RSP"
  | RBP => "RBP"
  | RSI => "RSI"
  | RDI => "RDI"
  | R8  => "R8"
  | R9  => "R9"
  | R10 => "R10"
  | R11 => "R11"
  | R12 => "R12"
  | R13 => "R13"
  | R14 => "R14"
  | R15 => "R15"
  end%string.

Definition string_of_xmm_register r : string :=
  match r with
  | XMM0 => "XMM0"
  | XMM1 => "XMM1"
  | XMM2 => "XMM2"
  | XMM3 => "XMM3"
  | XMM4 => "XMM4"
  | XMM5 => "XMM5"
  | XMM6 => "XMM6"
  | XMM7 => "XMM7"
  | XMM8 => "XMM8"
  | XMM9 => "XMM9"
  | XMM10 => "XMM10"
  | XMM11 => "XMM11"
  | XMM12 => "XMM12"
  | XMM13 => "XMM13"
  | XMM14 => "XMM14"
  | XMM15 => "XMM15"
  end.

Definition string_of_rflag (rf : rflag) : string :=
  match rf with
 | CF => "CF"
 | PF => "PF"
 | ZF => "ZF"
 | SF => "SF"
 | OF => "OF"
 | DF => "DF"
 end%string.

Definition regs_strings :=
  Eval compute in [seq (string_of_register x, x) | x <- registers].

Lemma regs_stringsE : regs_strings =
  [seq (string_of_register x, x) | x <- registers].
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Definition xmm_regs_strings :=
  Eval compute in [seq (string_of_xmm_register x, x) | x <- xmm_registers].

Lemma xmm_regs_stringsE : xmm_regs_strings =
  [seq (string_of_xmm_register x, x) | x <- xmm_registers].
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Definition rflags_strings :=
  Eval compute in [seq (string_of_rflag x, x) | x <- rflags].

Lemma rflags_stringsE : rflags_strings =
  [seq (string_of_rflag x, x) | x <- rflags].
Proof. by []. Qed.

(* -------------------------------------------------------------------- *)
Definition reg_of_string (s : string) :=
  assoc regs_strings s.

(* -------------------------------------------------------------------- *)
Definition xmm_reg_of_string (s : string) :=
  assoc xmm_regs_strings s.

(* -------------------------------------------------------------------- *)
Definition rflag_of_string (s : string) :=
  assoc rflags_strings s.

(* -------------------------------------------------------------------- *)
Lemma rflag_of_stringK : pcancel string_of_rflag rflag_of_string.
Proof. by case. Qed.

Lemma reg_of_stringK : pcancel string_of_register reg_of_string.
Proof. by case. Qed.

Lemma xmm_reg_of_stringK : pcancel string_of_xmm_register xmm_reg_of_string.
Proof. by case. Qed.

Lemma inj_string_of_rflag : injective string_of_rflag.
Proof. by apply: (pcan_inj rflag_of_stringK). Qed.

Lemma inj_string_of_register : injective string_of_register.
Proof. by apply: (pcan_inj reg_of_stringK). Qed.

Lemma inj_string_of_xmm_register : injective string_of_xmm_register.
Proof. by apply: (pcan_inj xmm_reg_of_stringK). Qed.

(* -------------------------------------------------------------------- *)
Lemma inj_reg_of_string s1 s2 r :
     reg_of_string s1 = Some r
  -> reg_of_string s2 = Some r
  -> s1 = s2.
Proof. by rewrite /reg_of_string !regs_stringsE; apply: inj_assoc. Qed.

(* -------------------------------------------------------------------- *)
Lemma xmm_reg_of_stringI s r :
  xmm_reg_of_string s = Some r →
  string_of_xmm_register r = s.
Proof.
  have := xmm_reg_of_stringK r.
  move => /assoc_inj. apply. done.
Qed.

(* -------------------------------------------------------------------- *)
Lemma inj_xmm_reg_of_string s1 s2 r :
     xmm_reg_of_string s1 = Some r
  -> xmm_reg_of_string s2 = Some r
  -> s1 = s2.
Proof. by rewrite /xmm_reg_of_string !xmm_regs_stringsE; apply: inj_assoc. Qed.

(* -------------------------------------------------------------------- *)
Lemma inj_rflag_of_string s1 s2 rf :
     rflag_of_string s1 = Some rf
  -> rflag_of_string s2 = Some rf
  -> s1 = s2.
Proof. by rewrite /rflag_of_string !rflags_stringsE; apply: inj_assoc. Qed.

(* -------------------------------------------------------------------- *)

Definition var_of_register r :=
  {| vtype := sword64 ; vname := string_of_register r |}.

Definition var_of_xmm_register r :=
  {| vtype := sword256 ; vname := string_of_xmm_register r |}.

Definition var_of_flag f :=
  {| vtype := sbool; vname := string_of_rflag f |}.

Lemma var_of_register_inj x y :
  var_of_register x = var_of_register y →
  x = y.
Proof. by move=> [];apply inj_string_of_register. Qed.

Lemma var_of_flag_inj x y :
  var_of_flag x = var_of_flag y →
  x = y.
Proof. by move=> [];apply inj_string_of_rflag. Qed.

Lemma var_of_register_var_of_flag r f :
  ¬ var_of_register r = var_of_flag f.
Proof. by case: r;case: f. Qed.

Definition register_of_var (v:var) : option register :=
  if v.(vtype) == sword64 then reg_of_string v.(vname)
  else None.

Lemma var_of_register_of_var v r :
  register_of_var v = Some r →
  var_of_register r = v.
Proof.
  rewrite /register_of_var /var_of_register;case:ifP => //.
  case: v => [vt vn] /= /eqP -> H;apply f_equal.
  by apply: inj_reg_of_string H; apply reg_of_stringK.
Qed.

Lemma register_of_var_of_register r :
  register_of_var (var_of_register r) = Some r.
Proof. exact: reg_of_stringK. Qed.

Definition flag_of_var (v: var) : option rflag :=
  if v.(vtype) == sbool then rflag_of_string v.(vname)
  else None.

Lemma var_of_flag_of_var v f :
  flag_of_var v = Some f →
  var_of_flag f = v.
Proof.
  rewrite /flag_of_var /var_of_flag;case:ifP => //.
  case: v => [vt vn] /= /eqP -> H; apply f_equal.
  by apply: inj_rflag_of_string H; apply rflag_of_stringK.
Qed.

Lemma flag_of_var_of_flag r :
  flag_of_var (var_of_flag r) = Some r.
Proof.
  rewrite /flag_of_var /var_of_flag /=.
  by apply rflag_of_stringK.
Qed.

Definition xmm_register_of_var (v:var) : option xmm_register :=
  if v.(vtype) == sword256 then xmm_reg_of_string v.(vname)
  else None.

Lemma xmm_register_of_varI v r :
  xmm_register_of_var v = Some r →
  var_of_xmm_register r = v.
Proof.
  by rewrite /xmm_register_of_var /var_of_xmm_register; case: eqP => // <- /xmm_reg_of_stringI ->; case: v.
Qed.

Lemma xmm_register_of_var_of_xmm_register xr :
  xmm_register_of_var (var_of_xmm_register xr) = Some xr.
Proof. exact: xmm_reg_of_stringK. Qed.

(* -------------------------------------------------------------------- *)
Variant compiled_variable :=
| LRegister of register
| LXRegister of xmm_register
| LRFlag of rflag
.

Scheme Equality for compiled_variable.

Definition compiled_variable_eqMixin := comparableMixin compiled_variable_eq_dec.

Canonical compiled_variable_eqType := EqType compiled_variable compiled_variable_eqMixin.

Definition compile_var (v: var) : option compiled_variable :=
  match register_of_var v with
  | Some r => Some (LRegister r)
  | None =>
  match xmm_register_of_var v with
  | Some r => Some (LXRegister r)
  | None =>
  match flag_of_var v with
  | Some f => Some (LRFlag f)
  | None => None
  end end end.

Lemma xmm_register_of_var_compile_var x r :
  xmm_register_of_var x = Some r →
  compile_var x = Some (LXRegister r).
Proof.
  move => h; rewrite /compile_var h.
  case: (register_of_var x) (@var_of_register_of_var x) => //.
  move => r' /(_ _ erefl) ?; subst x.
  have {h} := xmm_register_of_varI h.
  by destruct r, r'.
Qed.

Lemma compile_varI x cv :
  compile_var x = Some cv →
  match cv with
  | LRegister r => var_of_register r = x
  | LXRegister r => var_of_xmm_register r = x
  | LRFlag f => var_of_flag f = x
  end.
Proof.
  rewrite /compile_var.
  case: (register_of_var x) (@var_of_register_of_var x).
  + by move => r /(_ _ erefl) <- {x} [<-]{cv}.
  move => _.
  case: (xmm_register_of_var x) (@xmm_register_of_varI x).
  + by move => r /(_ _ erefl) <- {x} [<-]{cv}.
  move => _.
  case: (flag_of_var x) (@var_of_flag_of_var x) => //.
  by move => r /(_ _ erefl) <- {x} [<-]{cv}.
Qed.

(* -------------------------------------------------------------------- *)
(* Compilation of pexprs *)
(* -------------------------------------------------------------------- *)
Definition invalid_rflag (s: string) : asm_error :=
  AsmErr_string ("Invalid rflag name: " ++ s) None.

Definition invalid_register (s: string) : asm_error :=
  AsmErr_string ("Invalid register name: " ++ s) None.

Global Opaque invalid_rflag invalid_register.

(* -------------------------------------------------------------------- *)
Definition rflag_of_var ii (v: var) :=
  match v with
  | Var sbool s =>
     match (rflag_of_string s) with
     | Some r => ciok r
     | None => cierror ii (Cerr_assembler (invalid_rflag s))
     end
  | _ => cierror ii (Cerr_assembler (AsmErr_string "Invalid rflag type" None))
  end.

(* -------------------------------------------------------------------- *)
Definition assemble_cond ii (e: pexpr) : ciexec condt :=
  match e with
  | Pvar v =>
    Let r := rflag_of_var ii v.(gv) in
    match r with
    | OF => ok O_ct
    | CF => ok B_ct
    | ZF => ok E_ct
    | SF => ok S_ct
    | PF => ok P_ct
    | DF => cierror ii (Cerr_assembler (AsmErr_string "Cannot branch on DF" None))
    end

  | Papp1 Onot (Pvar v) =>
    Let r := rflag_of_var ii v.(gv) in
    match r with
    | OF => ok NO_ct
    | CF => ok NB_ct
    | ZF => ok NE_ct
    | SF => ok NS_ct
    | PF => ok NP_ct
    | DF => cierror ii (Cerr_assembler (AsmErr_string "Cannot branch on ~~ DF" None))
    end

  | Papp2 Oor (Pvar vcf) (Pvar vzf) =>
    Let rcf := rflag_of_var ii vcf.(gv) in
    Let rzf := rflag_of_var ii vzf.(gv) in
    if ((rcf == CF) && (rzf == ZF)) then
      ok BE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (BE)" None))

  | Papp2 Oand (Papp1 Onot (Pvar vcf)) (Papp1 Onot (Pvar vzf)) =>
    Let rcf := rflag_of_var ii vcf.(gv) in
    Let rzf := rflag_of_var ii vzf.(gv) in
    if ((rcf == CF) && (rzf == ZF)) then
      ok NBE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (NBE)" None))

  | Pif _ (Pvar vsf) (Papp1 Onot (Pvar vof1)) (Pvar vof2) =>
    Let rsf := rflag_of_var ii vsf.(gv) in
    Let rof1 := rflag_of_var ii vof1.(gv) in
    Let rof2 := rflag_of_var ii vof2.(gv) in
    if ((rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok L_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (L)" None))

  | Pif _ (Pvar vsf) (Pvar vof1) (Papp1 Onot (Pvar vof2)) =>
    Let rsf := rflag_of_var ii vsf.(gv) in
    Let rof1 := rflag_of_var ii vof1.(gv) in
    Let rof2 := rflag_of_var ii vof2.(gv) in
    if ((rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok NL_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (NL)" None))

  | Papp2 Oor (Pvar vzf)
          (Pif _ (Pvar vsf) (Papp1 Onot (Pvar vof1)) (Pvar vof2)) =>
    Let rzf := rflag_of_var ii vzf.(gv) in
    Let rsf := rflag_of_var ii vsf.(gv) in
    Let rof1 := rflag_of_var ii vof1.(gv) in
    Let rof2 := rflag_of_var ii vof2.(gv) in
    if ((rzf == ZF) && (rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok LE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (LE)" None))

  | Papp2 Oand
             (Papp1 Onot (Pvar vzf))
             (Pif _ (Pvar vsf) (Pvar vof1) (Papp1 Onot (Pvar vof2))) =>
    Let rzf := rflag_of_var ii vzf.(gv) in
    Let rsf := rflag_of_var ii vsf.(gv) in
    Let rof1 := rflag_of_var ii vof1.(gv) in
    Let rof2 := rflag_of_var ii vof2.(gv) in
    if ((rzf == ZF) && (rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok NLE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (NLE)" None))

  | _ => cierror ii (Cerr_assembler (AsmErr_cond e))
  end.

(* -------------------------------------------------------------------- *)

Definition reg_of_var ii (v: var) :=
  match v with
  | Var (sword U64) s =>
     match (reg_of_string s) with
     | Some r => ciok r
     | None => cierror ii (Cerr_assembler (invalid_register s))
     end
  | _ => cierror ii (Cerr_assembler (AsmErr_string "Invalid register type" None))
  end.

Definition reg_of_vars ii (vs: seq var_i) :=
  mapM (reg_of_var ii \o v_var) vs.

Lemma reg_of_var_register_of_var ii x r :
  reg_of_var ii x = ok r →
  register_of_var x = Some r.
Proof.
 by rewrite /register_of_var; case: x => -[] //= [] // x; case: reg_of_string => // r' [->].
Qed.

(* -------------------------------------------------------------------- *)
Definition scale_of_z' ii (z:pointer) :=
  match wunsigned z with
  | 1 => ok Scale1
  | 2 => ok Scale2
  | 4 => ok Scale4
  | 8 => ok Scale8
  | _ => cierror ii (Cerr_assembler (AsmErr_string "invalid scale" None))
  end%Z.

Definition reg_of_ovar ii (x:option var_i) := 
  match x with 
  | Some x => 
    Let r := reg_of_var ii x in
    ok (Some r)
  | None =>
    ok None
  end.

Definition assemble_lea ii lea := 
  Let base := reg_of_ovar ii lea.(lea_base) in
  Let offset := reg_of_ovar ii lea.(lea_offset) in
  Let scale := scale_of_z' ii lea.(lea_scale) in
  ok (Areg {|
      ad_disp := lea.(lea_disp);
      ad_base := base;
      ad_scale := scale;
      ad_offset := offset 
    |}).

Definition addr_of_pexpr (rip:var) ii sz (e: pexpr) := 
  match lowering.mk_lea sz e with
  | Some lea => 
     match lea.(lea_base) with
     | Some r =>
        if r.(v_var) == rip then
          Let _ := assert (lea.(lea_offset) == None) 
            (ii, Cerr_assembler (AsmErr_string "Invalid global address" (Some e))) in
           ok (Arip lea.(lea_disp))
        else assemble_lea ii lea
      | None => 
        assemble_lea ii lea
      end 
  | None => cierror ii (Cerr_assembler (AsmErr_string "lea: not able to assemble address" (Some e)))
  end.

Definition addr_of_xpexpr rip ii sz v e :=
  addr_of_pexpr rip ii sz (Papp2 (Oadd (Op_w sz)) (Plvar v) e).

Definition xreg_of_var ii (x: var) : ciexec asm_arg :=
  if xmm_register_of_var x is Some r then ok (XMM r)
  else if register_of_var x is Some r then ok (Reg r)
  else cierror ii (Cerr_assembler (AsmErr_string "Not a (x)register" None)).

Definition assemble_word rip ii (sz:wsize) max_imm (e:pexpr) :=
  match e with
  | Papp1 (Oword_of_int sz') (Pconst z) =>
    match max_imm with
    | None =>  cierror ii (Cerr_assembler (AsmErr_string "Invalid pexpr for oprd, constant not allowed" (Some e)))
    | Some sz1 =>
      let w := wrepr sz1 z in
      let w1 := sign_extend sz w in
      let w2 := zero_extend sz (wrepr sz' z) in
      Let _ := assert (w1 == w2)
                (ii, Cerr_assembler (AsmErr_string "Invalid pexpr for oprd: out of bound constant" (Some e))) in
      ciok (Imm w)
    end
  | Pvar x =>
    Let _ := assert (is_lvar x)
              (ii, Cerr_assembler (AsmErr_string "Global variables remain" (Some e))) in
    let x := x.(gv) in
    xreg_of_var ii x
  | Pload sz' v e =>
    if (sz == sz') then
      Let w := addr_of_xpexpr rip ii Uptr v e in
      ok (Adr w)
    else
      cierror ii (Cerr_assembler (AsmErr_string "Invalid pexpr for word: invalid Load size" (Some e)))
  | _ => cierror ii (Cerr_assembler (AsmErr_string "Invalid pexpr for word" (Some e)))
  end.

Definition arg_of_pexpr rip ii (ty:stype) max_imm (e:pexpr) :=
  match ty with
  | sbool => Let c := assemble_cond ii e in ok (Condt c)
  | sword sz => assemble_word rip ii sz max_imm e
  | sint  => cierror ii (Cerr_assembler (AsmErr_string "sint ???" (Some e)))
  | sarr _ => cierror ii (Cerr_assembler (AsmErr_string "sarr ???" (Some e)))
  end.
