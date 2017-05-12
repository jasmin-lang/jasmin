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

(* * Syntax and semantics of the x86_64 target language *)

(* ** Imports and settings *)

From mathcomp Require Import all_ssreflect.
Require Import expr linear compiler_util low_memory x86_sem.

Import Ascii.
Import Relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Definition string_of_register (r: register) : string :=
  match r with
  | RAX => "RAX"
  | RCX => "RCX"
  | RDX => "RDX"
  | RBX => "RBX"
  | RSP => "RSP"
  | RBP => "RBP"
  | RSI => "RSI"
  | RDI => "RDI"
  | R8 => "R8"
  | R9 => "R9"
  | R10 => "R10"
  | R11 => "R11"
  | R12 => "R12"
  | R13 => "R13"
  | R14 => "R14"
  | R15 => "R15"
  end%string.

Definition reg_of_string (s: string) : option register :=
  match s with
  | String c0 tl =>
    if ascii_dec c0 "R" then
    match tl with
    | String c1 tl =>
      match tl with
      | EmptyString =>
        if ascii_dec c1 "8" then Some R8 else
        if ascii_dec c1 "9" then Some R9 else
        None
      | String c2 tl =>
        match tl with
        | EmptyString =>
          if ascii_dec c2 "X" then if ascii_dec c1 "A" then Some RAX else
          if ascii_dec c1 "B" then Some RBX else
          if ascii_dec c1 "C" then Some RCX else
          if ascii_dec c1 "D" then Some RDX else
          None else
          if ascii_dec c2 "P" then if ascii_dec c1 "S" then Some RSP else
          if ascii_dec c1 "B" then Some RBP else
          None else
          if ascii_dec c2 "I" then if ascii_dec c1 "S" then Some RSI else
          if ascii_dec c1 "D" then Some RDI else
          None else
          if ascii_dec c1 "1" then
            if ascii_dec c2 "0" then Some R10 else
            if ascii_dec c2 "1" then Some R11 else
            if ascii_dec c2 "2" then Some R12 else
            if ascii_dec c2 "3" then Some R13 else
            if ascii_dec c2 "4" then Some R14 else
            if ascii_dec c2 "5" then Some R15 else
            None else
          None
        | String _ _ => None
        end
      end
    | EmptyString => None
    end
    else None
  | EmptyString => None
  end.

Definition rflag_of_string (s: string) : option rflag :=
  match s with
  | String c0 (String c1 EmptyString) =>
    if ascii_dec c1 "F" then
      if ascii_dec c0 "C" then Some CF else
      if ascii_dec c0 "P" then Some PF else
      if ascii_dec c0 "Z" then Some ZF else
      if ascii_dec c0 "S" then Some SF else
      if ascii_dec c0 "O" then Some OF else
      if ascii_dec c0 "D" then Some DF else
      None
    else None
  | _ => None
  end.

Record xfundef := XFundef {
 xfd_stk_size : Z;
 xfd_nstk : register;
 xfd_arg  : seq register;
 xfd_body : seq asm;
 xfd_res  : seq register;
}.

Definition xprog := seq (funname * xfundef).

(* ** Conversion to assembly *
 * -------------------------------------------------------------------- *)

Definition rflag_of_var ii (v: var_i) :=
  match v with
  | VarI (Var sbool s) _ =>
     match (rflag_of_string s) with
     | Some r => ciok r
     | None => cierror ii (Cerr_assembler ("Invalid rflag name: " ++ s))
     end
  | _ => cierror ii (Cerr_assembler "Invalid rflag type")
  end.

Definition reg_of_var ii (v: var_i) :=
  match v with
  | VarI (Var sword s) _ =>
     match (reg_of_string s) with
     | Some r => ciok r
     | None => cierror ii (Cerr_assembler ("Invalid register name: " ++ s))
     end
  | _ => cierror ii (Cerr_assembler "Invalid register type")
  end.

Definition reg_of_vars ii (vs: seq var_i) :=
  mapM (reg_of_var ii) vs.

Definition word_of_int ii (z: Z) :=
  if (I64.signed (I64.repr z) == z) then
    ciok (I64.repr z)
  else
    cierror ii (Cerr_assembler "Integer constant out of bounds").

Definition word_of_pexpr ii e :=
  match e with
  | Pcast (Pconst z) => word_of_int ii z
  | _ => cierror ii (Cerr_assembler "Invalid integer constant")
  end.

Definition oprd_of_lval ii (l: lval) :=
  match l with
  | Lnone _ _ => cierror ii (Cerr_assembler "Lnone not implemented")
  | Lvar v =>
     Let s := reg_of_var ii v in
     ciok (Reg_op s)
  | Lmem v e =>
     Let s := reg_of_var ii v in
     Let w := word_of_pexpr ii e in
     ciok (Adr_op (mkAddress w (Some s) Scale1 None))
  | Laset v e => cierror ii (Cerr_assembler "Laset not handled in assembler")
  end.

Definition oprd_of_pexpr ii (e: pexpr) :=
  match e with
  | Pcast (Pconst z) =>
     Let w := word_of_int ii z in
     ciok (Imm_op w)
  | Pvar v =>
     Let s := reg_of_var ii v in
     ciok (Reg_op s)
  | Pload v e =>
     Let s := reg_of_var ii v in
     Let w := word_of_pexpr ii e in
     ciok (Adr_op (mkAddress w (Some s) Scale1 None))
  | _ => cierror ii (Cerr_assembler "Invalid pexpr for oprd")
  end.

Definition ireg_of_pexpr ii (e: pexpr) :=
  match e with
  | Pcast (Pconst z) =>
     Let w := word_of_int ii z in
     ciok (Imm_ir w)
  | Pvar v =>
     Let s := reg_of_var ii v in
     ciok (Reg_ir s)
  | _ => cierror ii (Cerr_assembler "Invalid pexpr for ireg")
  end.

Definition assemble_cond ii (e: pexpr) : ciexec condt :=
  match e with
  | Pvar v =>
    Let r := rflag_of_var ii v in
    match r with
    | OF => ok O_ct
    | CF => ok B_ct
    | ZF => ok E_ct
    | SF => ok S_ct
    | PF => ok P_ct
    | DF => cierror ii (Cerr_assembler "Cannot branch on DF")
    end
  | Papp1 Onot (Pvar v) =>
    Let r := rflag_of_var ii v in
    match r with
    | OF => ok NO_ct
    | CF => ok NB_ct
    | ZF => ok NE_ct
    | SF => ok NS_ct
    | PF => ok NP_ct
    | DF => cierror ii (Cerr_assembler "Cannot branch on ~~ DF")
    end
  | Papp2 Oor (Pvar vcf) (Pvar vzf) =>
    Let rcf := rflag_of_var ii vcf in
    Let rzf := rflag_of_var ii vzf in
    if ((rcf == CF) && (rzf == ZF)) then
      ok BE_ct
    else cierror ii (Cerr_assembler "Invalid condition")
  | Papp2 Oand (Papp1 Onot (Pvar vcf)) (Papp1 Onot (Pvar vzf)) =>
    Let rcf := rflag_of_var ii vcf in
    Let rzf := rflag_of_var ii vzf in
    if ((rcf == CF) && (rzf == ZF)) then
      ok NBE_ct
    else cierror ii (Cerr_assembler "Invalid condition")
  | Pif (Pvar vsf) (Papp1 Onot (Pvar vof1)) (Pvar vof2) =>
    Let rsf := rflag_of_var ii vsf in
    Let rof1 := rflag_of_var ii vof1 in
    Let rof2 := rflag_of_var ii vof2 in
    if ((rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok L_ct
    else cierror ii (Cerr_assembler "Invalid condition")
  | Pif (Pvar vsf) (Pvar vof1) (Papp1 Onot (Pvar vof2)) =>
    Let rsf := rflag_of_var ii vsf in
    Let rof1 := rflag_of_var ii vof1 in
    Let rof2 := rflag_of_var ii vof2 in
    if ((rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok NL_ct
    else cierror ii (Cerr_assembler "Invalid condition")
  | Papp2 Oor (Pvar vzf)
          (Pif (Pvar vsf) (Papp1 Onot (Pvar vof1)) (Pvar vof2)) =>
    Let rzf := rflag_of_var ii vzf in
    Let rsf := rflag_of_var ii vsf in
    Let rof1 := rflag_of_var ii vof1 in
    Let rof2 := rflag_of_var ii vof2 in
    if ((rzf == ZF) && (rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok LE_ct
    else cierror ii (Cerr_assembler "Invalid condition")
  | Papp2 Oand
             (Papp1 Onot (Pvar vzf))
             (Pif (Pvar vsf) (Pvar vof1) (Papp1 Onot (Pvar vof2))) =>
    Let rzf := rflag_of_var ii vzf in
    Let rsf := rflag_of_var ii vsf in
    Let rof1 := rflag_of_var ii vof1 in
    Let rof2 := rflag_of_var ii vof2 in
    if ((rzf == ZF) && (rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok NLE_ct
    else cierror ii (Cerr_assembler "Invalid condition")
  | _ => cierror ii (Cerr_assembler "Invalid condition")
  end.

Definition assemble_fopn ii (l: lvals) (o: sopn) (e: pexprs) : ciexec asm :=
  match e with
  | [:: e1; e2] =>
    Let o1 := oprd_of_pexpr ii e1 in
    Let o2 := oprd_of_pexpr ii e2 in
    match o with
    | Ox86_CMP =>
      match l with
      | [::] => ciok (CMP o1 o2)
      | _ => cierror ii (Cerr_assembler "Too many lvals in Ox86_CMP")
      end
    | _ =>
      match l with
      | [:: l] =>
        Let ol := oprd_of_lval ii l in
        if (o1 == ol) then
          ciok (match o with
          | Ox86_ADD => ADD
          | Ox86_ADC => ADC
          | Ox86_SUB => SUB
          | Ox86_SBB => SBB
          (* TODO: | Ox86_MUL => MUL *)
          | Ox86_AND => AND
          | Ox86_OR  => OR
          | Ox86_XOR | _ => XOR
          end o1 o2)
        else
          cierror ii (Cerr_assembler "Last lval & first rval of arithmetic ops should be the same")
      | _ => cierror ii (Cerr_assembler "Wrong number of lvals in arithmetic operator")
      end
    end
  | _ => cierror ii (Cerr_assembler "Wrong number of pexprs in fopn")
  end.

Definition assemble_shift ii (l: lvals) (o: sopn) (e: pexprs) : ciexec asm :=
  match e with
  | [:: Pvar vof; Pvar vcf; Pvar vsf; Pvar vpf; Pvar vzf; e1; e2] =>
    Let rof := rflag_of_var ii vof in
    Let rcf := rflag_of_var ii vcf in
    Let rsf := rflag_of_var ii vsf in
    Let rpf := rflag_of_var ii vpf in
    Let rzf := rflag_of_var ii vzf in
    Let o1 := oprd_of_pexpr ii e1 in
    Let o2 := ireg_of_pexpr ii e2 in
    if ((rof == OF) && (rcf == CF) && (rsf == SF) && (rpf == PF) && (rzf == ZF)) then
      match l with
      | [:: l] =>
        Let ol := oprd_of_lval ii l in
        if (o1 == ol) then
          ciok (match o with
          | Ox86_SHR => SHR
          | Ox86_SHL => SHL
          | Ox86_SAR | _ => SAR
          end o1 o2)
        else
          cierror ii (Cerr_assembler "lval & rval of shift should be the same")
      | _ => cierror ii (Cerr_assembler "Wrong number of lvals in shift operator")
      end
    else
      cierror ii (Cerr_assembler "Wrong rflags in lval of shift operator")
  | _ => cierror ii (Cerr_assembler "Wrong number of pexprs in shift operator")
  end.

Definition assemble_opn ii (l: lvals) (o: sopn) (e: pexprs) : ciexec asm :=
  match o with
  | Ox86_CMP | Ox86_ADD | Ox86_ADC | Ox86_SUB | Ox86_SBB (*| Ox86_MUL TODO *)
  | Ox86_AND | Ox86_OR  | Ox86_XOR | Ox86_SHR | Ox86_SHL | Ox86_SAR =>
    match l with
    | (Lvar vof) :: (Lvar vcf) :: (Lvar vsf) :: (Lvar vpf) :: (Lvar vzf) :: l =>
      Let rof := rflag_of_var ii vof in
      Let rcf := rflag_of_var ii vcf in
      Let rsf := rflag_of_var ii vsf in
      Let rpf := rflag_of_var ii vpf in
      Let rzf := rflag_of_var ii vzf in
      if ((rof == OF) && (rcf == CF) && (rsf == SF) && (rpf == PF) && (rzf == ZF)) then
        match o with
        | Ox86_CMP | Ox86_ADD | Ox86_ADC | Ox86_SUB | Ox86_SBB
        | Ox86_MUL | Ox86_AND | Ox86_OR  | Ox86_XOR => assemble_fopn ii l o e
        | Ox86_SHR | Ox86_SHL | Ox86_SAR | _ => assemble_shift ii l o e
        end
      else cierror ii (Cerr_assembler "Invalid registers in lvals")
    | _ => cierror ii (Cerr_assembler "Invalid number of lvals")
    end
  | Ox86_DEC | Ox86_INC =>
    match l with
    | [:: Lvar vof; Lvar vsf; Lvar vpf; Lvar vzf; l] =>
      Let ol := oprd_of_lval ii l in
      match e with
      | [:: e] =>
        Let or := oprd_of_pexpr ii e in
        if (or == ol) then
          ciok (match o with
          | Ox86_DEC => DEC
          | Ox86_INC | _ => INC
          end or)
        else
          cierror ii (Cerr_assembler "lval & rval of Ox86_DEC/INC should be the same")
      | _ => cierror ii (Cerr_assembler "Invalid number of pexpr in Ox86_DEC/INC")
      end
    | _ => cierror ii (Cerr_assembler "Invalid number of lval in Ox86_DEC/INC")
    end
  | _ => cierror ii (Cerr_assembler "Unhandled sopn")
  end.

Definition assemble_i (li: linstr) : ciexec asm :=
  let (ii, i) := li in
  match i with
  | Lassgn l _ e =>
     (* TODO: this is useless since lowering doesn't leave Lassgn; might remove at some point *)
     Let dst := oprd_of_lval ii l in
     Let src := oprd_of_pexpr ii e in
     ciok (MOV dst src)
  | Lopn l o p => assemble_opn ii l o p
  | Llabel l => ciok (LABEL l)
  | Lgoto l => ciok (JMP l)
  | Lcond e l =>
     Let cond := assemble_cond ii e in
     ciok (Jcc l cond)
  end.

Definition assemble_c (lc: lcmd) : ciexec (seq asm) :=
  mapM assemble_i lc.

Definition assemble_fd (fd: lfundef) :=
  Let fd' := assemble_c (lfd_body fd) in
  match (reg_of_string (lfd_nstk fd)) with
  | Some sp =>
    Let arg := reg_of_vars xH (lfd_arg fd) in
    Let res := reg_of_vars xH (lfd_res fd) in
    ciok (XFundef (lfd_stk_size fd) sp arg fd' res)
  | None => cierror xH (Cerr_assembler "Invalid stack pointer")
  end.

Definition assemble_prog (p: lprog) : cfexec xprog :=
  map_cfprog assemble_fd p.

