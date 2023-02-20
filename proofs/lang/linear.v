(* * Syntax of the linear language *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import expr label sopn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ASM_OP.

Context `{asmop:asmOp}.

(* --------------------------------------------------------------------------- *)
(* Syntax                                                                      *)

Variant linstr_r :=
  | Lopn   : lvals -> sopn -> pexprs -> linstr_r
  | Lsyscall : syscall_t -> linstr_r
  | Lcall    : remote_label -> linstr_r
  | Lret     : linstr_r
  | Lalign : linstr_r
  | Llabel : label_kind -> label -> linstr_r
  | Lgoto  : remote_label -> linstr_r
  | Ligoto : pexpr -> linstr_r (* Absolute indirect jump *)
  | LstoreLabel : var -> label -> linstr_r
  | Lcond  : pexpr -> label -> linstr_r
.

Record linstr : Type := MkLI { li_ii : instr_info; li_i : linstr_r }.

Definition lcmd := seq linstr.

Definition is_label (lbl: label) (i: linstr) : bool :=
  match i.(li_i) with
  | Llabel _ lbl' => lbl == lbl'
  | _ => false
  end.

(* -------------------------------------------------------------------- *)
Definition find_label (lbl : label) (c : seq linstr) :=
  let idx := seq.find (is_label lbl) c in
  if idx < size c then ok idx else type_error.

Record lfundef := LFundef {
 lfd_info : fun_info;
 lfd_align : wsize;
 lfd_tyin : seq stype;
 lfd_arg  : seq var_i;
 lfd_body : lcmd;
 lfd_tyout : seq stype;
 lfd_res  : seq var_i;  (* /!\ did we really want to have "seq var_i" here *)
 lfd_export: bool;
 lfd_callee_saved: seq var; (* A list of variables that must be initialized before calling this function *)
 (* This is [lfd_total_stack] without padding, rounded to the next alignment
    multiple if the function is export and we need to clean the stack. *)
  lfd_used_stack : Z;
 lfd_frame_size : Z; (* we need that piece of info for clear stack *)
}.

Definition signature_of_lfundef (lfd: lfundef) : function_signature :=
  (lfd_tyin lfd, lfd_tyout lfd).

Record lprog :=
  {
    lp_rip : Ident.ident;
    lp_rsp : Ident.ident;
    lp_globs : seq u8;
    lp_funcs : seq (funname * lfundef);
  }.


End ASM_OP.
