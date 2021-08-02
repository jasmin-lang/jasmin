From mathcomp Require Import all_ssreflect all_algebra.
Require Import low_memory psem x86_sem compiler_util lowering.
Import Utf8.
Import oseq x86_variables.
Import GRing.
Require Import ssrring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition pexpr_of_lval ii (lv:lval) : ciexec pexpr :=
  match lv with
  | Lvar x    => ok (Plvar x)
  | Lmem s x e  => ok (Pload s x e)
  | Lnone _ _
  | Laset _ _ _ _ 
  | Lasub _ _ _ _ _ => cierror ii (Cerr_assembler (AsmErr_string "pexpr_of_lval" None))
  end.

Definition nmap (T:Type) := nat -> option T.
Definition nget (T:Type) (m:nmap T) (n:nat) := m n.
Definition nset (T:Type) (m:nmap T) (n:nat) (t:T) :=
  fun x => if x == n then Some t else nget m x.
Definition nempty (T:Type) := fun n:nat => @None T.

Definition var_of_implicit i :=
  match i with
  | IArflag f => var_of_flag f
  | IAreg r   => var_of_register r
  end.

Definition compile_arg rip ii max_imm (ade: (arg_desc * stype) * pexpr) (m: nmap asm_arg) : ciexec (nmap asm_arg) :=
  let ad := ade.1 in
  let e := ade.2 in
  match ad.1 with
  | ADImplicit i =>
    Let _ :=
      assert (eq_expr (Plvar (VarI (var_of_implicit i) xH)) e)
             (ii, Cerr_assembler (AsmErr_string "compile_arg : bad implicit" (Some e))) in
    ok m
  | ADExplicit k n o =>
    Let a := arg_of_pexpr k rip ii ad.2 max_imm e in
    Let _ :=
      assert (check_oreg o a)
             (ii, Cerr_assembler (AsmErr_string "compile_arg : bad forced register" (Some e))) in
    match nget m n with
    | None => ok (nset m n a)
    | Some a' =>
      if a == a' then ok m
      else cierror ii (Cerr_assembler (AsmErr_string "compile_arg : not compatible asm_arg" (Some e)))
    end
  end.

Definition compile_args rip ii max_imm adts (es:pexprs) (m: nmap asm_arg) :=
  foldM (compile_arg rip ii max_imm) m (zip adts es).

Definition compat_imm ty a' a := 
  (a == a') || match ty, a, a' with
             | sword sz, Imm sz1 w1, Imm sz2 w2 => sign_extend sz w1 == sign_extend sz w2
             | _, _, _ => false
             end.
                
Definition check_sopn_arg rip ii max_imm (loargs : seq asm_arg) (x : pexpr) (adt : arg_desc * stype) :=
  match adt.1 with
  | ADImplicit i => eq_expr x (Plvar (VarI (var_of_implicit i) xH))
  | ADExplicit k n o =>
    match onth loargs n with
    | Some a =>
      if arg_of_pexpr k rip ii adt.2 max_imm x is Ok a' then compat_imm adt.2 a a' && check_oreg o a
      else false
    | None => false
    end
  end.

Definition check_sopn_dest rip ii max_imm (loargs : seq asm_arg) (x : pexpr) (adt : arg_desc * stype) :=
  match adt.1 with
  | ADImplicit i => eq_expr x (Plvar (VarI (var_of_implicit i) xH))
  | ADExplicit _ n o =>
    match onth loargs n with
    | Some a =>
      if arg_of_pexpr AK_mem rip ii adt.2 max_imm x is Ok a' then (a == a') && check_oreg o a
      else false
    | None => false
    end
  end.

Definition error_imm :=
 Cerr_assembler (AsmErr_string "Invalid asm: cannot truncate the immediate to a 32 bits immediate, move it to a register first" None).

Definition assemble_x86_opn_aux rip ii op (outx : lvals) (inx : pexprs) :=
  let id := instr_desc op in
  let max_imm := id.(id_max_imm) in
  Let m := compile_args rip ii max_imm (zip id.(id_in) id.(id_tin)) inx (nempty _) in
  Let eoutx := mapM (pexpr_of_lval ii) outx in
  Let m := compile_args rip ii max_imm (zip id.(id_out) id.(id_tout)) eoutx m in
  match oseq.omap (nget m) (iota 0 id.(id_nargs)) with
  | None => cierror ii (Cerr_assembler (AsmErr_string "compile_arg : assert false nget" None))
  | Some asm_args =>
      (* This should allows to fix the problem with "MOV addr (IMM U64 w)" *)
      Let asm_args := 
        match op.2, asm_args with
        | MOV U64, [:: Adr a; Imm U64 w] =>
          match truncate_word U32 w with
          | Ok w' => 
            Let _ := assert (sign_extend U64 w' == w) (ii, error_imm) in
            ok [::Adr a; Imm w']
          | _ => cierror ii error_imm 
          end
        | _, _ => ok asm_args 
        end in
      ok asm_args
  end.

Definition check_sopn_args rip ii max_imm (loargs : seq asm_arg) (xs : seq pexpr) (adt : seq (arg_desc * stype)) :=
  all2 (check_sopn_arg rip ii max_imm loargs) xs adt.

Definition check_sopn_dests rip ii max_imm (loargs : seq asm_arg) (outx : seq lval) (adt : seq (arg_desc * stype)) :=
  match mapM (pexpr_of_lval ii) outx with
  | Ok eoutx => all2 (check_sopn_dest rip ii max_imm loargs) eoutx adt
  | _  => false
  end.

Definition assemble_x86_opn rip ii op (outx : lvals) (inx : pexprs) := 
  let id := instr_desc op in
  let max_imm := id.(id_max_imm) in
  Let asm_args := assemble_x86_opn_aux rip ii op outx inx in
  let s := id.(id_str_jas) tt in
  Let _ := assert (id_check id asm_args)
       (ii, Cerr_assembler (AsmErr_string ("assemble_x86_opn : invalid instruction (check) " ++ s) None)) in
  Let _ := assert (check_sopn_args rip ii max_imm asm_args inx (zip id.(id_in) id.(id_tin)) &&
                     check_sopn_dests rip ii max_imm asm_args outx (zip id.(id_out) id.(id_tout)))
       (ii, Cerr_assembler (AsmErr_string "assemble_x86_opn: cannot check, please repport" None)) in
  ok (op.2, asm_args).

Definition assemble_sopn rip ii op (outx : lvals) (inx : pexprs) :=
  match op with
  | Onop
  | Omulu     _ 
  | Oaddcarry _ 
  | Osubcarry _ =>
    cierror ii (Cerr_assembler (AsmErr_string "assemble_sopn : invalid op" None))
  (* Low level x86 operations *)
  | Oset0 sz => 
    let op := if (sz <= U64)%CMP then (XOR sz) else (VPXOR sz) in
    Let x := 
      match rev outx with 
      | Lvar x :: _ =>  ok x
      | _ => 
        cierror ii 
          (Cerr_assembler (AsmErr_string "assemble_sopn set0: destination is not a register" None))
      end in
    assemble_x86_opn rip ii (None, op) outx [::Plvar x; Plvar x]
  | Ox86MOVZX32 =>
    Let x := 
      match outx with 
      | [::Lvar x] =>  ok x
      | _ => 
        cierror ii 
          (Cerr_assembler (AsmErr_string "assemble_sopn Ox86MOVZX32: destination is not a register" None))
      end in
    assemble_x86_opn rip ii (None, MOV U32) outx inx

  | Oconcat128 =>
    Let inx := 
        match inx with
        | [:: h; Pvar _ as l] => ok [:: l; h; @wconst U8 1%R]
        |  _ => 
          cierror ii 
            (Cerr_assembler (AsmErr_string "assemble_sopn Oconcat: assert false" None))
        end in
    assemble_x86_opn rip ii (None, VINSERTI128) outx inx
    
  | Ox86' op =>
    assemble_x86_opn rip ii op outx inx 
  end.

Lemma id_semi_sopn_sem op :
  let id := instr_desc op in
  id_semi id = sopn_sem (Ox86' op).
Proof. by []. Qed.

Lemma word_of_scale1 : word_of_scale Scale1 = 1%R.
Proof. by rewrite /word_of_scale /= /wrepr; apply/eqP. Qed.

