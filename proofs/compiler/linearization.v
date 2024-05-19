(** Transformation into the linear language *)

(* ** Imports and settings *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
Require Import ZArith.
Require Import Utf8.
Import Relations.

Require Import expr fexpr compiler_util label constant_prop.
Require Export linear linear_util.
Import word_ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Module E.

Definition pass_name := "linearization"%string.

Definition my_error (msg:pp_error) :=
  {| pel_msg      := msg
   ; pel_fn       := None
   ; pel_fi       := None
   ; pel_ii       := None
   ; pel_vi       := None
   ; pel_pass     := Some pass_name
   ; pel_internal := false
  |}.

(* FIXME: are there internal errors? *)
Definition gen_error (internal: bool) (ii: option instr_info) (msg: pp_error) :=
  {| pel_msg      := msg
   ; pel_fn       := None
   ; pel_fi       := None
   ; pel_ii       := ii
   ; pel_vi       := None
   ; pel_pass     := Some pass_name
   ; pel_internal := internal
  |}.

Definition ii_error (ii: instr_info) (msg: string) :=
  gen_error false (Some ii) (pp_s msg).

Definition error (msg: string) :=
  gen_error false None (pp_s msg).

Definition internal_error (msg: string) :=
  gen_error true None (pp_s msg).

Definition assign_remains (ii : instr_info) (lv: lval) (e: pexpr) :=
  gen_error false (Some ii)
    (pp_nobox [:: pp_s "The following assignment remains:"; PPEbreak;
      pp_lv lv; pp_s " = "; pp_e e; PPEbreak;
      pp_s "Is there an instruction in the target architecture that can implement it?"; PPEbreak;
      pp_s "More information may be found online: https://github.com/jasmin-lang/jasmin/wiki/FAQ"
  ]).

End E.


(* --------------------------------------------------------------------------- *)

Record linearization_params {asm_op : Type} {asmop : asmOp asm_op} :=
  {
    (* Scratch registers used to set up stack. *)
    lip_tmp  : Ident.ident;
    lip_tmp2 : Ident.ident;

    (* Variables that can't be used to save the stack pointer.
       If lip_set_up_sp_register use its auxiliary argument, it should contain lip_tmp
    *)
    lip_not_saved_stack : seq Ident.ident;

    (* Return the arguments for a linear instruction that allocates a stack
       frame.
       The linear instruction derived from [lip_allocate_stack_frame rspi sz]
       decreases the stack pointer [sz] bytes.
       In symbols, it corresponds to:
               R[rsp] := R[rsp] - sz
     *)
    lip_allocate_stack_frame :
      var_i    (* Variable with stack pointer register. *)
      -> option var_i (* An auxiliary variable *)
      -> Z     (* Amount of space to allocate. *)
      -> seq fopn_args;

    (* Return the arguments for a linear instruction that frees a stack frame.
       The linear instruction derived from [lip_free_stack_frame rspi sz]
       increases the stack pointer [sz] bytes.
       In symbols, it corresponds to:
               R[rsp] := R[rsp] + sz
     *)
    lip_free_stack_frame :
      var_i    (* Variable with stack pointer register. *)
      -> option var_i (* An auxiliary variable *)
      -> Z     (* Amount of space to free. *)
      -> seq fopn_args;

    (* Return the arguments for a linear command that saves the value of the
       stack pointer to a register, allocates a stack frame and aligns the stack
       pointer.
       The linear command derived from [lip_set_up_sp_register rspi sz ws r]
       corresponds to:
               r := R[rsp]
               R[rsp] := (R[rsp] - sz) & - wsize_size ws
    *)
    lip_set_up_sp_register :
      var_i    (* Variable with stack pointer register. *)
      -> Z     (* Size of the stack frame to allocate. *)
      -> wsize (* Alignment. *)
      -> var_i (* Variable to save stack pointer to. *)
      -> var_i (* An auxiliary variable *)
      -> seq fopn_args;

    (* Return the arguments for a linear instruction that corresponds to
       an assignment.
       In symbols, the linear instruction derived from [lip_lmove d s]
       corresponds to:
               d := (Uptr)s
     *)
    lip_lmove :
      var_i       (* Destination variable. *)
      -> var_i    (* Source variable. *)
      -> fopn_args;

    (* Check it the give size can be write/read to/from memory,
       i.e if an operation exists for that size. *)
    lip_check_ws : wsize -> bool;

    (* Return the arguments for a linear instruction that corresponds to
       an assignment.
       In symbols, the linear instruction derived from [lip_lstore b ofs xs]
       corresponds to:
               [b + ofs] := (Uptr) s
     *)
    lip_lstore :
      var_i        (* Base register. *)
      -> Z         (* Offset. *)
      -> var_i     (* Source register. *)
      -> fopn_args;

    (* Push variables to the stack at the given offset *)
    lip_lstores :
      var_i              (* The current stack pointer *)
      -> seq (var * Z)   (* The list of variables to save at a given offset *)
      -> seq fopn_args;

    (* Load variables from the stack at the given offset *)
    lip_lloads:
      var_i           (* The current stack pointer *)
      -> seq (var * Z)   (* The list of variables to restore from a given offset *)
      -> Z            (* The offset for the stack pointer to restore*)
      -> seq fopn_args;
  }.

(* Note on function calls:

   + For X86:

     - Return address passed by register in ra:
          LstoreLabel ra lret
          Lgoto lcall
          Llabel lret
       Internally (to the callee), ra need to be free.
       The return is implemented by
          Ligoto ra
       /!\ For protection against Spectre we should avoid this calling convention

     - Return address passed by stack (on top of the stack):
          Lcall None lcall;
          Llabel lret;
       The return is implemented by
          Lret  (i.e ret in X86)
        The stack frame is incremented by the caller and by the call instruction (to push ra).


   + For ARM v7:

     - Return address passed by register in ra
         Lcall (Some ra) lcall    (i.e BL lcall with the constraint that ra should be LR(r14))
         Llabel lret
       Internally (to the callee), ra need to be free.
       The return is implemented by
          Ligoto ra   (i.e BX ra)
       The stack frame is incremented by the caller.


     - Return address passed by stack (on top of the stack):
       Lcall (Some ra) lcall (i.e BL lcall with the constraint that ra should be LR(r14))
       Llabel lret
       ra need to be free when Lcall is executed (extra_free_registers = Some ra).
       The first instruction of the function call need to push ra.
          store sp ra
       So ra need to be known at call cite and at the entry of the function.
       The stack frame is incremented by the caller.

       The return is implemented by
       Lret  (i.e POP PC in arm v7)

*)

(* The following functions are defined here, so that they can be shared between the architectures. The proofs are shared too (see linearization_proof.v). An architecture can define its own functions when there is something more efficient to do, and rely on one of these implementations in the default case. *)
Section DEFAULT.
Context {asm_op : Type} {pd : PointerData} {asmop : asmOp asm_op}.
Context (lip_tmp2 : Ident.ident).
Context (lip_lstore  : var_i -> Z -> var_i -> fopn_args)
        (lip_lload   : var_i -> var_i -> Z -> fopn_args)
        (lip_add_imm : var_i -> var_i -> Z -> seq fopn_args)
        (lip_imm_small : Z -> bool).

Definition lstores_dfl (rsp: var_i) (to_save : seq (var * Z)) :=
  map (fun '(x,ofs) => lip_lstore rsp ofs (VarI x dummy_var_info)) to_save.

Definition lstores_imm_dfl (rsp : var_i) (to_save : seq (var * Z)) :=
  if all (fun '(_,ofs) => lip_imm_small ofs) to_save then
    lstores_dfl rsp to_save
  else
    let ofs0 := snd (head (v_var rsp, 0%Z) to_save) in
    let tmp2 := VarI {| vtype := sword Uptr; vname := lip_tmp2 |} dummy_var_info in
    let to_save := map (fun '(x, ofs) => (x, ofs - ofs0)%Z) to_save in
    lip_add_imm tmp2 rsp ofs0 ++ lstores_dfl tmp2 to_save.

Definition lloads_aux (rsp:var_i) (to_restore : seq (var * Z)) :=
  map (fun '(x, ofs) => lip_lload (VarI x dummy_var_info) rsp ofs) to_restore.

Definition lloads_dfl (rsp:var_i) (to_restore : seq (var * Z)) (spofs:Z) :=
  lloads_aux rsp (to_restore ++ [:: (v_var rsp, spofs)]).

Definition lloads_imm_dfl (rsp:var_i) (to_restore : seq (var * Z)) (spofs:Z) :=
  let to_restore := to_restore ++ [:: (v_var rsp, spofs)] in
  if all (fun '(_,ofs) => lip_imm_small ofs) to_restore then
    lloads_aux rsp to_restore
  else
    let ofs0 := snd (head (v_var rsp, 0%Z) to_restore) in
    let tmp2 := VarI {| vtype := sword Uptr; vname := lip_tmp2 |} dummy_var_info in
    let to_restore := map (fun '(x, ofs) => (x, ofs - ofs0)%Z) to_restore in
    lip_add_imm tmp2 rsp ofs0 ++ lloads_aux tmp2 to_restore.

End DEFAULT.

Section WITH_PARAMS.

Context
  {asm_op : Type}
  {pd : PointerData}
  {asmop : asmOp asm_op}
  (liparams : linearization_params).

(* Return a linear instruction that corresponds to copying a register.
   The linear instruction [lmove ii rd rs] corresponds to
           R[rd] := (Uptr)R[rs]
 *)
Definition lmove
  (rd : var_i)      (* Destination register. *)
  (rs : var_i)       (* Source register. *)
  : linstr :=
  li_of_fopn_args dummy_instr_info (lip_lmove liparams rd rs).

(* Return a linear instruction that corresponds to loading from memory.
   The linear instruction [lload ii rd ws r0 ofs] corresponds to
           R[rd] := (ws)M[R[r0] + ofs]
 *)

(* Return a linear instruction that corresponds to storing to memory.
   The linear instruction [lstore ii rd ofs ws rs] corresponds to
           M[R[rd] + ofs] := (ws)R[rs]
 *)
Definition lstore
  (rd : var_i)      (* Base register. *)
  (ofs : Z)         (* Offset. *)
  (rs : var_i)      (* Source register. *)
  : linstr :=
  li_of_fopn_args dummy_instr_info (lip_lstore liparams rd ofs rs).

Definition set_up_sp_register
  (vrspi : var_i) (sf_sz : Z) (al : wsize) (r : var_i) (tmp : var_i) : lcmd :=
  map (li_of_fopn_args dummy_instr_info) (lip_set_up_sp_register liparams vrspi sf_sz al r tmp).

(* -------------------------------------------------------------------------- *)
Section CHECK_SOME.
  Context (E: Type) (error: string → E) (A B: Type) (conv: A → option B).

  Definition check_Some msg (a: A) : result E unit :=
    assert (isSome (conv a)) (error msg).

End CHECK_SOME.

(* -------------------------------------------------------------------------- *)
Section EXPR.
  Context (ii: instr_info).

  Definition to_fexpr (e: pexpr) : fexpr :=
    if fexpr_of_pexpr e is Some r then r else Fconst 0.

  Let error msg := E.gen_error true (Some ii) (pp_s msg).

  Definition check_fexpr := check_Some error fexpr_of_pexpr "check_fexpr".

  Definition check_rexpr := check_Some error rexpr_of_pexpr "check_rexpr".

  Definition check_lexpr := check_Some error lexpr_of_lval "check_lexpr".

End EXPR.

Definition ovar_of_ra (ra : return_address_location) : option var :=
  match ra with
  | RAreg ra _ => Some ra
  | RAstack ra _ _ => ra
  | RAnone => None
  end.

Definition ovari_of_ra (ra : return_address_location) : option var_i :=
  omap mk_var_i (ovar_of_ra ra).

Definition tmp_of_ra (ra : return_address_location) : option var :=
  match ra with
  | RAreg _ o => o
  | RAstack _ _ o => o
  | RAnone => None
  end.

Definition tmpi_of_ra (ra : return_address_location) : option var_i :=
  omap mk_var_i (tmp_of_ra ra).

Section PROG.

Context
  (p : sprog).
(*  (extra_free_registers : instr_info -> option var) *)

Notation rsp := {| vtype := sword Uptr; vname := sp_rsp (p_extra p); |}.
Notation rspi := (mk_var_i rsp).

Notation var_tmp  := {| vtype := sword Uptr; vname := lip_tmp  liparams; |}.
Notation var_tmp2 := {| vtype := sword Uptr; vname := lip_tmp2 liparams; |}.

(** Total size of a stack frame: local variables, extra and padding. *)
Definition stack_frame_allocation_size (e: stk_fun_extra) : Z :=
  round_ws e.(sf_align) (sf_stk_sz e + sf_stk_extra_sz e).

Definition frame_size (e: stk_fun_extra) : Z :=
  if is_RAnone e.(sf_return_address) then
    (sf_stk_sz e + sf_stk_extra_sz e)%Z
  else
    stack_frame_allocation_size e.

(* Return a linear command that pushes variables to the stack.
 * The linear command `lp_push_to_save ii to_save` pushes each
 * variable x to the stack with an offset o for each (x, o) in to_save.
 * The variables in to_save are all words.
 * In symbols, it corresponds to:
 *         M[R[rsp] + o] := x
 * for each (x, o) in to_save.
 *)
Definition push_to_save
  (to_save: seq (var * Z)) (* Variables to save and offsets in the stack. *)
  (sp : var * Z)           (* Variable to save containing the initial value of sp *)
  : lcmd :=
  map (li_of_fopn_args dummy_instr_info)
      (lip_lstores liparams rspi (to_save ++ [::sp])).

(* Return a linear command that loads variables from the stack.
 * The linear command `lp_pop_to_save ii to_save` loads each
 * variable x from the stack with an offset o for each (x, o) in to_save.
 * The variables in to_save are all words.
 * In symbols, it corresponds to:
 *         x := M[R[rsp] + o]
 * for each (x, o) in to_save.
 *)
Definition pop_to_save
  (to_save: seq (var * Z)) (* Variables to load and offsets in the stack. *)
  (sp : Z)                 (* Offset for restoring the stack pointer *)
  : lcmd :=
  map (li_of_fopn_args dummy_instr_info)
      (lip_lloads liparams rspi to_save sp).

  Section CHECK_c.

    Context (check_i: instr -> cexec unit).

    Fixpoint check_c (c:cmd) : cexec unit :=
      match c with
      | [::] => ok tt
      | i::c => check_c c >> check_i i
      end.

  End CHECK_c.

  Section CHECK_i.

  Context (this: funname) (e_caller : stk_fun_extra).

  Fixpoint check_i (i:instr) : cexec unit :=
    let (ii,ir) := i in
    match ir with
    | Cassgn lv _ _ e => Error (E.assign_remains ii lv e)
    | Copn xs tag o es =>
      allM (check_rexpr ii) es >> allM (check_lexpr ii) xs
    | Csyscall xs o es =>
      ok tt
    | Cif b c1 c2 =>
      check_fexpr ii b >> check_c check_i c1 >> check_c check_i c2
    | Cfor _ _ _ =>
      Error (E.ii_error ii "for found in linear")
    | Cwhile _ c e c' =>
      match is_bool e with
      | Some false => check_c check_i c
      | Some true => check_c check_i c >> check_c check_i c'
      | None => check_fexpr ii e >> check_c check_i c >> check_c check_i c'
      end
    | Ccall xs fn es =>
      Let _ := assert (fn != this) (E.ii_error ii "call to self") in
      if get_fundef (p_funcs p) fn is Some fd then
        let e := f_extra fd in
        Let _ := assert (~~ is_RAnone (sf_return_address e))
          (E.ii_error ii "internal call to an export function") in
        Let _ := assert (sf_align e <= sf_align e_caller)%CMP
          (E.ii_error ii "caller need alignment greater than callee") in
        Let _ := assert (sf_stk_max e + frame_size e_caller <=? sf_stk_max e_caller)%Z
          (E.ii_error ii "max size problem") in
        ok tt
      else Error (E.ii_error ii "call to unknown function")
    end.

  End CHECK_i.

  Let check_stack_ofs e ofs ws : bool :=
    [&&
     (sf_stk_sz e <=? ofs )%Z,
     (ofs + wsize_size ws <=? sf_stk_sz e + sf_stk_extra_sz e)%Z,
     (ws ≤ sf_align e)%CMP (* Stack frame is aligned for storing words of size ws *) &
     is_align (wrepr Uptr ofs) ws (* Stack slot is aligned *)
    ].

  Let check_stack_ofs_internal_call e ofs ws : bool :=
    [&&
     ofs == 0%Z,
     wsize_size ws == sf_stk_ioff e &
     (ws ≤ sf_align e)%CMP (* Stack frame is aligned for storing words of size ws *)
    ].

  Definition check_to_save_slot (p : var * Z) : cexec (Z * wsize) :=
    let '(x, ofs) := p in
    if is_word_type (vtype x) is Some ws
    then ok (ofs, ws)
    else
      Error (E.error "to-save: not a word").

  Definition all_disjoint_aligned_between (lo hi: Z) (al: wsize) (m: seq (var * Z)) : cexec unit :=
    Let last := foldM (λ a base,
                       Let: (ofs, ws) := check_to_save_slot a in
                       Let _ := assert (base <=? ofs)%Z (E.my_error (pp_hov [::pp_s "to-save: overlap"; pp_e (Pconst base); pp_e (Pconst ofs)])) in
                       Let _ := assert (ws ≤ al)%CMP (E.error "to-save: bad frame alignement") in
                       Let _ := assert (is_align (wrepr Uptr ofs) ws) (E.error "to-save: bad slot alignement") in
                       Let _ := assert (lip_check_ws liparams ws) (E.error "to-save: bad wsize") in
                       ok (ofs + wsize_size ws)%Z
                      ) lo m in
    assert (last <=? hi)%Z (E.error "to-save: overflow in the stack frame").

  Definition check_to_save (e: stk_fun_extra) : cexec unit :=
    if is_RAnone (sf_return_address e)
    then
      (* FIXME: this assert seems redundant with the check in check_fd *)
      let stk_size := (sf_stk_sz e + sf_stk_extra_sz e)%Z in
      Let _ := assert (if sf_save_stack e is SavedStackStk ofs then (ofs + wsize_size Uptr <=? stk_size)%Z else true)
                      (E.error "stack size to small") in

      all_disjoint_aligned_between
        (sf_stk_sz e)
        (if sf_save_stack e is SavedStackStk ofs then ofs else (sf_stk_sz e + sf_stk_extra_sz e))
        e.(sf_align) (sf_to_save e)
    else ok tt.

(* --------------------------------------------------------------------------- *)
(* Translation                                                                 *)

Notation "c1 ';;' c2" :=  (let: (lbl,lc) := c2 in c1 lbl lc)
   (at level 26, right associativity).

Notation "c1 '>;' c2" :=  (let: (lbl,lc) := c2 in (lbl, c1::lc))
   (at level 26, right associativity).

Section LINEAR_C.

  Variable linear_i : instr -> label -> lcmd -> label * lcmd.

  Fixpoint linear_c (c:cmd) (lbl:label) (lc:lcmd) :=
    match c with
    | [::] => (lbl, lc)
    | i::c =>
      linear_i i ;; linear_c c lbl lc
    end.

End LINEAR_C.

Definition add_align ii a (lc:lcmd) :=
  match a with
  | NoAlign => lc
  | Align   =>  MkLI ii Lalign :: lc
  end.

Definition align ii a (p:label * lcmd) : label * lcmd :=
  (p.1, add_align ii a p.2).

Section FUN.

Context
  (fn : funname).

Definition ov_type_ptr (o: option var) :=
   if o is Some r then vtype r == sword Uptr else true.

Definition check_fd (fn: funname) (fd:sfundef) :=
  let e := fd.(f_extra) in
  let stack_align := e.(sf_align) in
  Let _ := check_c (check_i fn e) fd.(f_body) in
  Let _ := check_to_save e in
  (* FIXME: strange to have both stack_frame_allocation_size and frame_size *)
  Let _ := assert [&& 0 <=? sf_stk_sz e,
                      0 <=? sf_stk_extra_sz e,
                      stack_frame_allocation_size e <? wbase Uptr
                    & frame_size e <=? sf_stk_max e]%Z
                  (E.error "bad stack size") in
  Let _ := assert match sf_return_address e with
                  | RAnone => ~~ (var_tmp2 \in map v_var fd.(f_res))
                  | RAreg ra tmp => (vtype ra == sword Uptr) && ov_type_ptr tmp
                  | RAstack ora ofs tmp =>
                      [&& ov_type_ptr tmp
                        , (if ora is Some ra then vtype ra == sword Uptr
                           else true)
                        & check_stack_ofs_internal_call e ofs Uptr]
                  end
                  (E.error "bad return-address") in
  let ok_save_stack :=
    let sf_sz := (sf_stk_sz e + sf_stk_extra_sz e)%Z in
    match sf_save_stack e with
    | SavedStackNone =>
        [&& sf_to_save e == [::]
          , sf_align e == U8
          , sf_stk_sz e == 0%Z
          & sf_stk_extra_sz e == 0%Z
        ]

    | SavedStackReg x =>
        [&& vtype x == sword Uptr
          , sf_to_save e == [::]
          & vname x != lip_tmp liparams
        ]

    | SavedStackStk ofs =>
        [&& check_stack_ofs e ofs Uptr
          , ~~ Sv.mem var_tmp  (sv_of_list fst (sf_to_save e))
          , ~~ Sv.mem var_tmp2 (sv_of_list fst (sf_to_save e))
          & ~~ Sv.mem rsp (sv_of_list fst (sf_to_save e))
          ]
    end
  in
  Let _ :=
    assert
      (~~ is_RAnone (sf_return_address e) || ok_save_stack)
      (E.error "bad save-stack")
  in
  ok tt.

Definition check_prog :=
  Let _ := map_cfprog_name check_fd (p_funcs p) in
  ok tt.

Definition allocate_stack_frame (free: bool) (ii: instr_info) (sz: Z) (tmp: option var_i)
(rastack: bool) : lcmd :=
  let sz := if rastack then (sz - wsize_size Uptr)%Z else sz in
  if sz == 0%Z
  then [::]
  else
    let args := if free
                   then (lip_free_stack_frame liparams) rspi tmp sz
                   else (lip_allocate_stack_frame liparams) rspi tmp sz in
     map (li_of_fopn_args ii) args.

Let ReturnTarget := Llabel ExternalLabel.
Let Llabel := linear.Llabel InternalLabel.

Fixpoint linear_i (i:instr) (lbl:label) (lc:lcmd) :=
  let (ii, ir) := i in
  match ir with
  | Cassgn _ _ _ _ => (lbl, lc) (* absurd case *)
  | Copn xs _ o es =>
      match oseq.omap lexpr_of_lval xs, oseq.omap rexpr_of_pexpr es with
      | Some xs, Some es => (lbl, MkLI ii (Lopn xs o es) :: lc)
      | _, _ => (lbl, lc) (* absurd case *)
      end

  | Csyscall xs o es => (lbl, MkLI ii (Lsyscall o) :: lc)

  | Cif e [::] c2 =>
    let L1 := lbl in
    let lbl := next_lbl L1 in
    MkLI ii (Lcond (to_fexpr e) L1) >; linear_c linear_i c2 lbl (MkLI ii (Llabel L1) :: lc)

  | Cif e c1 [::] =>
    let L1 := lbl in
    let lbl := next_lbl L1 in
    MkLI ii (Lcond (to_fexpr (snot e)) L1) >; linear_c linear_i c1 lbl (MkLI ii (Llabel L1) :: lc)

  | Cif e c1 c2 =>
    let L1 := lbl in
    let L2 := next_lbl L1 in
    let lbl := next_lbl L2 in
                           MkLI ii (Lcond (to_fexpr e) L1) >;
                           linear_c linear_i c2 ;;
                           MkLI ii (Lgoto (fn, L2)) >;
    MkLI ii (Llabel L1) >; linear_c linear_i c1 lbl
   (MkLI ii (Llabel L2) :: lc)

  | Cwhile a c e c' =>
    match is_bool e with
    | Some true =>
      let L1 := lbl in
      let lbl := next_lbl L1 in
      align ii a (
      MkLI ii (Llabel L1) >; linear_c linear_i c ;;
                             linear_c linear_i c' lbl
                             (MkLI ii (Lgoto (fn, L1)) :: lc))

    | Some false =>
      linear_c linear_i c lbl lc

    | None =>
      match c' with
      | [::] =>
      let L1 := lbl in
      let lbl := next_lbl L1 in
      align ii a (MkLI ii (Llabel L1) >; linear_c linear_i c lbl
                             (MkLI ii (Lcond (to_fexpr e) L1) :: lc))
      | _ =>
      let L1 := lbl in
      let L2 := next_lbl L1 in
      let lbl := next_lbl L2 in
                             MkLI ii (Lgoto (fn, L1)) >;
      align ii a (MkLI ii (Llabel L2) >; linear_c linear_i c' ;;
      MkLI ii (Llabel L1) >; linear_c linear_i c lbl
                             (MkLI ii (Lcond (to_fexpr e) L2) :: lc))
      end
    end

  | Ccall xs fn' es =>
    if get_fundef (p_funcs p) fn' is Some fd then
      let e := f_extra fd in
      let ra := sf_return_address e in
      if is_RAnone ra then (lbl, lc)
      else
        let sz := stack_frame_allocation_size e in
        let tmp := tmpi_of_ra ra in
        let before := allocate_stack_frame false ii sz tmp (is_RAstack_None ra) in
        let after := allocate_stack_frame true ii sz tmp (is_RAstack ra) in
        let lret := lbl in
        let lbl := next_lbl lbl in
        (* The test is used for the proof of linear_has_valid_labels *)
        let lcall := (fn', if fn' == fn
                           then lret    (* Absurd case. *)
                           else xH      (* Entry point. *)
                     ) in
        (* * 1. Allocate stack frame.
           * 2. Call callee
           * 3. Insert return label (callee will jump back here).
           * 4. Free stack frame.
           * 5. Continue.
           *)
        (lbl,    before
              ++ MkLI ii (Lcall (ovari_of_ra ra) lcall)
              :: MkLI ii (ReturnTarget lret)
              :: after
              ++ lc
          )
    else (lbl, lc )
  | Cfor _ _ _ => (lbl, lc)
  end.

Definition linear_body (e: stk_fun_extra) (body: cmd) : label * lcmd :=
  let: (tail, head, lbl) :=
     match sf_return_address e with
     | RAreg r _ =>
       ( [:: MkLI dummy_instr_info (Ligoto (Rexpr (Fvar (mk_var_i r)))) ]
       , [:: MkLI dummy_instr_info (Llabel 1) ]
       , 2%positive
       )
     | RAstack ra z _ =>
       ( [:: MkLI dummy_instr_info Lret ]
       , MkLI dummy_instr_info (Llabel 1) ::
         (if ra is Some ra
          then [:: lstore rspi z (mk_var_i ra) ]
          else [::])
       , 2%positive
       )
     | RAnone =>
       let sf_sz := (sf_stk_sz e + sf_stk_extra_sz e)%Z in
       match sf_save_stack e with
       | SavedStackNone =>
         ([::], [::], 1%positive)
       | SavedStackReg x =>
         (* Tail: R[rsp] := R[x]
          * Head: R[x] := R[rsp]
          *       Setup stack.
          *)
         let r := mk_var_i x in
         ( [:: lmove rspi r ]
         , set_up_sp_register rspi sf_sz (sf_align e) r (mk_var_i var_tmp)
         , 1%positive
         )
       | SavedStackStk ofs =>
         (* Tail: Load saved registers.
          *       R[rsp] := M[R[rsp] + ofs]
          * Head: R[r] := R[rsp]
          *       Setup stack.
          *       M[R[rsp] + ofs] := R[r]
          *       Push registers to save to the stack.
          *)
         let r := mk_var_i var_tmp in
         ( pop_to_save e.(sf_to_save) ofs
         , set_up_sp_register rspi sf_sz (sf_align e) r (mk_var_i var_tmp2)
             ++ push_to_save e.(sf_to_save) (var_tmp, ofs)
         , 1%positive)
       end
     end
  in
  let fd' := linear_c linear_i body lbl tail in
  (fd'.1, head ++ fd'.2).

Definition linear_fd (fd: sfundef) :=
  let e := fd.(f_extra) in
  let is_export := is_RAnone (sf_return_address e) in
  let res := if is_export then f_res fd else [::] in
  let body := linear_body e fd.(f_body) in
  (body.1,
    {| lfd_info := f_info fd
    ; lfd_align := sf_align e
    ; lfd_tyin := f_tyin fd
    ; lfd_arg := f_params fd
    ; lfd_body := body.2
    ; lfd_tyout := f_tyout fd
    ; lfd_res := res
    ; lfd_export := is_export
    ; lfd_callee_saved := if is_export then map fst e.(sf_to_save) else [::]
    ; lfd_stk_max := sf_stk_max e
    ; lfd_frame_size := frame_size e
    ; lfd_align_args := sf_align_args e
    |}).

End FUN.

Definition linear_prog : cexec lprog :=
  Let _ := check_prog in
  Let _ := assert (size p.(p_globs) == 0)
             (E.internal_error "invalid p_globs") in
  let funcs := fmap (fun nb_lbl '(f,fd) =>
    let fd := linear_fd f fd in
    ((nb_lbl + fd.1)%positive, (f, fd.2))) 1%positive p.(p_funcs)
  in
  Let _ := assert (funcs.1 <=? wbase Uptr)%Z
                  (E.internal_error "too many labels")
  in
  ok {| lp_rip   := p.(p_extra).(sp_rip);
        lp_rsp   := p.(p_extra).(sp_rsp);
        lp_globs := p.(p_extra).(sp_globs);
        lp_glob_names := p.(p_extra).(sp_glob_names);
        lp_funcs := funcs.2 |}.

End PROG.
End WITH_PARAMS.
