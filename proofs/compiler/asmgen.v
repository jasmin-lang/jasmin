From mathcomp Require Import all_ssreflect all_algebra.
Require Import low_memory psem x86_sem compiler_util lowering x86_variables.
Import Utf8.
Import oseq.
Import GRing.
Require Import ssrring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition pexpr_of_lval ii (lv:lval) : cexec pexpr :=
  match lv with
  | Lvar x          => ok (Plvar x)
  | Lmem s x e      => ok (Pload s x e)
  | Lnone _ _       => Error (E.internal_error ii "_ lval remains")
  | Laset _ _ _ _   => Error (E.internal_error ii "Laset lval remains")
  | Lasub _ _ _ _ _ => Error (E.internal_error ii "Lasub lval remains")
  end.

Definition nmap (T:Type) := nat -> option T.
Definition nget (T:Type) (m:nmap T) (n:nat) := m n.
Definition nset (T:Type) (m:nmap T) (n:nat) (t:T) :=
  fun x => if x == n then Some t else nget m x.
Definition nempty (T:Type) := fun n:nat => @None T.

Definition var_of_implicit (i:implicit_arg) :=
  match i with
  | IArflag f => var_of_flag f
  | IAreg r   => var_of_register r
  end.

Definition compile_arg rip ii max_imm (ade: (arg_desc * stype) * pexpr) (m: nmap asm_arg) : cexec (nmap asm_arg) :=
  let ad := ade.1 in
  let e := ade.2 in
  match ad.1 with
  | ADImplicit i =>
    Let _ :=
      assert (eq_expr (Plvar (VarI (var_of_implicit i) xH)) e)
             (E.internal_error ii "(compile_arg) bad implicit register") in
    ok m
  | ADExplicit k n o =>
    Let a := arg_of_pexpr k rip ii ad.2 max_imm e in
    Let _ :=
      assert (check_oreg o a)
             (E.internal_error ii "(compile_arg) bad forced register") in
    match nget m n with
    | None => ok (nset m n a)
    | Some a' =>
      if a == a' then ok m
      else Error (E.internal_error ii "(compile_arg) not compatible asm_arg")
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

Definition error_imm ii :=
 E.error ii (pp_s "Invalid asm: cannot truncate the immediate to a 32 bits immediate, move it to a register first").

Definition assemble_x86_opn_aux rip ii op (outx : lvals) (inx : pexprs) :=
  let id := instr_desc op in
  let max_imm := id.(id_max_imm) in
  Let m := compile_args rip ii max_imm (zip id.(id_in) id.(id_tin)) inx (nempty _) in
  Let eoutx := mapM (pexpr_of_lval ii) outx in
  Let m := compile_args rip ii max_imm (zip id.(id_out) id.(id_tout)) eoutx m in
  match oseq.omap (nget m) (iota 0 id.(id_nargs)) with
  | None => Error (E.internal_error ii "compile_arg : assert false nget")
  | Some asm_args =>
      (* This should allows to fix the problem with "MOV addr (IMM U64 w)" *)
      Let asm_args := 
        match op.2, asm_args with
        | MOV U64, [:: Addr a; Imm U64 w] =>
          match truncate_word U32 w with
          | Ok w' => 
            Let _ := assert (sign_extend U64 w' == w) (error_imm ii) in
            ok [::Addr a; Imm w']
          | _ => Error (error_imm ii)
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
  Let _ := assert (check_i_args_kinds id.(id_args_kinds) asm_args)
                  (E.error ii (pp_box [:: pp_s "invalid instruction, check do not pass :"; pp_s s])) in
  Let _ := assert (check_sopn_args rip ii max_imm asm_args inx (zip id.(id_in) id.(id_tin)) &&
                     check_sopn_dests rip ii max_imm asm_args outx (zip id.(id_out) id.(id_tout)))
                  (E.internal_error ii "assemble_x86_opn: cannot check") in
  ok (op.2, asm_args).

Definition assemble_sopn rip ii op (outx : lvals) (inx : pexprs) :=
  match op with
  | Onop
  | Omulu     _ 
  | Oaddcarry _ 
  | Osubcarry _ =>
    Error (E.internal_error ii "assemble_sopn : invalid op")
  (* Low level x86 operations *)
  | Oset0 sz => 
    let op := if (sz <= U64)%CMP then (XOR sz) else (VPXOR sz) in
    Let x := 
      match rev outx with 
      | Lvar x :: _ =>  ok x
      | _ => Error (E.internal_error ii "set0 : destination is not a register")
      end in
    assemble_x86_opn rip ii (None, op) outx [::Plvar x; Plvar x]
  | Ox86MOVZX32 =>
    Let x := 
      match outx with 
      | [::Lvar x] =>  ok x
      | _ => Error (E.internal_error ii "Ox86MOVZX32: destination is not a register")
      end in
    assemble_x86_opn rip ii (None, MOV U32) outx inx

  | Oconcat128 =>
    Let inx := 
        match inx with
        | [:: h; Pvar _ as l] => ok [:: l; h; @wconst U8 1%R]
        |  _ => Error (E.internal_error ii "Oconcat: assert false")
        end in
    assemble_x86_opn rip ii (None, VINSERTI128) outx inx
    
  | Ox86' op =>
    assemble_x86_opn rip ii op outx inx 
  end.

Lemma id_semi_sopn_sem op :
  let id := instr_desc op in
  id_semi id = sopn_sem (Ox86' op).
Proof. by []. Qed.
