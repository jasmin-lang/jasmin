Require Import x86_sem linear_sem.
Import Utf8 Relation_Operators.
Import all_ssreflect all_algebra.
Require Import compiler_util expr psem x86_sem linear x86_variables asmgen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Definition assemble_i rip (i: linstr) : ciexec asm :=
  let '{| li_ii := ii ; li_i := ir |} := i in
  match ir with
  | Lopn ds op es => 
    Let oa := assemble_sopn rip ii op ds es in
    ok (AsmOp oa.1 oa.2)

  | Lalign  => ciok ALIGN

  | Llabel lbl =>  ciok (LABEL lbl)

  | Lgoto lbl => ciok (JMP lbl)

  | Ligoto e =>
    Let arg := assemble_word AK_mem rip ii Uptr None e in
    ciok (JMPI arg)
  | LstoreLabel x lbl =>
    let fail (msg: string) := cierror ii (Cerr_assembler (AsmErr_string ("store-label: " ++ msg) None)) in
    Let dst := match x with
    | Lvar x => if register_of_var x is Some r then ok (Reg r) else fail "bad var"
    | Lmem _ _ _ => fail "set mem"
    | Laset _ _ _ _ => fail "set array"
    | Lasub _ _ _ _ _ => fail "sub array"
    | Lnone _ _ => fail "none"
    end%string in
    ciok (STORELABEL dst lbl)

  | Lcond e l =>
      Let cond := assemble_cond ii e in
      ciok (Jcc l cond)
  end.

(* -------------------------------------------------------------------- *)
(*TODO: use in whatever characterization using an lprog there is.*)
Definition assemble_c rip (lc: lcmd) : ciexec (seq asm) :=
  mapM (assemble_i rip) lc.

(* -------------------------------------------------------------------- *)
Definition x86_gen_error (sp: register) : instr_error :=
  (xH, Cerr_assembler (AsmErr_string
    ("Stack pointer (" ++ string_of_register sp ++ ") is also an argument")
    None)).

(* -------------------------------------------------------------------- *)

Definition assemble_fd sp rip (fd: lfundef) :=
  Let fd' := assemble_c rip (lfd_body fd) in
  Let _ := assert
             (~~ (var_of_register sp \in map v_var fd.(lfd_arg)))
             (x86_gen_error sp) in
  ciok (XFundef (lfd_align fd) sp fd' (lfd_export fd)).

(* -------------------------------------------------------------------- *)

Definition mk_rip name := {| vtype := sword Uptr; vname := name |}.

Definition assemble_prog (p: lprog) : cfexec xprog :=
  let rip := mk_rip p.(lp_rip) in
  Let _ := assert (register_of_var rip == None)
                    (Ferr_msg (Cerr_assembler ( AsmErr_string "Invalid RIP: please report" None))) in
  Let _ := assert (reg_of_string p.(lp_rsp) == Some RSP)
                    (Ferr_msg (Cerr_assembler ( AsmErr_string "Invalid RSP: please report" None))) in
  Let fds := map_cfprog (assemble_fd RSP rip) p.(lp_funcs) in
  ok {| xp_globs := p.(lp_globs); xp_funcs := fds |}
  .

Definition get_arg_value (st: x86_mem) (a: asm_arg) : value :=
  match a with
  | Reg r => Vword (xreg st r)
  | XMM r => Vword (xxreg st r)
  | Condt _ | Imm _ _ | Adr _ => Vundef sword64 (refl_equal _)
  end.

Definition get_arg_values st rs : values :=
  map (get_arg_value st) rs.

